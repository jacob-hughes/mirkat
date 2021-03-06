// Copyright (c) 2018 King's College London created by the Software Development
// Team <http://soft-dev.org/>
//
// The Universal Permissive License (UPL), Version 1.0
//
// Subject to the condition set forth below, permission is hereby granted to any
// person obtaining a copy of this software, associated documentation and/or
// data (collectively the "Software"), free of charge and under any and all
// copyright rights in the Software, and any and all patent rights owned or
// freely licensable by each licensor hereunder covering either (i) the
// unmodified Software as contributed to or provided by such licensor, or (ii)
// the Larger Works (as defined below), to deal in both
//
// (a) the Software, and (b) any piece of software and/or hardware listed in the
// lrgrwrks.txt file if one is included with the Software (each a "Larger Work"
// to which the Software is contributed by such licensors),
//
// without restriction, including without limitation the rights to copy, create
// derivative works of, display, perform, and distribute the Software and make,
// use, sell, offer for sale, import, export, have made, and have sold the
// Software and the Larger Work(s), and to sublicense the foregoing rights on
// either these or other terms.
//
// This license is subject to the following condition: The above copyright
// notice and either this complete permission notice or at a minimum a reference
// to the UPL must be included in all copies or substantial portions of the
// Software.  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO
// EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES
// OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.

use std::mem::align_of;
use std::collections::HashMap;
use std::collections::hash_map::Entry::{Occupied, Vacant};
use std::rc::Rc;

use rustc::hir::def_id::DefId;
use rustc::mir::{Mir, Local, BasicBlock, Place, START_BLOCK};
use rustc::ty::{TyCtxt, Instance, InstanceDef};
use rustc_data_structures::indexed_vec::{Idx};

use interp::{TyVal, size_of};

/// Contains metadata that may be needed during the evaluation of a stack frame.
/// This data is the same for all Frames of the same Function, therefore it is
/// hoisted here and then referenced to in order to avoid duplication.
#[derive(Debug)]
pub struct Function<'tcx> {
    /// The unique identifier for the function definition
    pub def_id: DefId,

    /// Each MIR is a CFG of a single function in Rust
    pub mir: &'tcx Mir<'tcx>,

    /// Acts as a lookup to a vars position in the contiguous
    /// `locals` byte vector, where the index is the local id and the value is
    /// the corresponding index into the `locals` field where the value's bytes
    /// start.
    locals_offsets: Vec<usize>,
    locals_size: usize,
}

impl<'tcx> Function<'tcx> {
    pub fn new(def_id: DefId, mir: &'tcx Mir<'tcx>) -> Self {
        // Calculate local indexes
        let mut locals_offsets: Vec<usize> = Vec::with_capacity(mir.local_decls.len());
        let mut next_idx = 0;
        for decl in mir.local_decls.iter() {
            locals_offsets.push(next_idx);
            next_idx += size_of(decl.ty);
        }

        Self {
            def_id: def_id,
            mir: mir,
            locals_offsets: locals_offsets,
            locals_size: next_idx
        }
    }
}

#[derive(Debug)]
pub struct Frame<'tcx> {
    pub function: Rc<Function<'tcx>>,

    /// Address in memory where the return value should be stored.
    /// We do not name this Return Address to avoid confusion with the Return
    /// instruction, which in compiler terminology is commonly referred to as
    /// the RA.
    pub ret_val: Option<Address>,

    /// Where execution should jump to after returning from the stackframe.
    /// None if stackframe is for a diverging or main functions as these do not
    /// return to any particular address.
    pub ret_block: Option<BasicBlock>,

    /// An exact sized byte vector containing the frame local vars in their byte
    /// representation.
    locals: Vec<u8>,
}

impl<'f, 'tcx> Frame<'tcx> {
    pub fn new(function: Rc<Function<'tcx>>,
               locals: Vec<u8>,
               ret_val: Option<Address>,
               ret_block: Option<BasicBlock>)
            -> Self {
        Self {
            function: function,
            locals: locals,
            ret_val: ret_val,
            ret_block: ret_block,
        }
    }

    pub fn local_ptr(&self, local: Local) -> Ptr {
        let idx = local.index();
        let start = self.function.locals_offsets[idx];
        let end = if idx + 1 < self.function.locals_offsets.len() {
            self.function.locals_offsets[idx + 1]
        } else { // if it's the last local..
            self.function.locals_size
        };
        let size = end - start;
        Ptr::new(start, size)
    }

    fn set_bytes(&mut self, ptr: Ptr, bytes: Vec<u8>) {
        let end = ptr.addr + ptr.size;
        assert_eq!(ptr.size, bytes.len());
        self.locals.splice(ptr.addr..end, bytes.into_iter());
    }

    fn get_bytes(&self, ptr: Ptr) -> &[u8] {
        let end = ptr.addr + ptr.size;
        &self.locals[ptr.addr..end]
    }
}

/// Represents a pointer into some kind of memory.
// TODO: Extend to work with static constructs.
#[derive(Debug)]
pub enum Address {
    Heap(Ptr),
    Local(Ptr),
}

#[derive(Debug)]
pub struct Ptr {
    pub addr: usize,
    pub size: usize,
}

impl Ptr {
    pub fn new(addr: usize, size: usize) -> Self {
        Self {
            addr: addr,
            size: size,
        }
    }
}

pub struct Memory {
    // Memory is a simple vector of bytes whose size is parameterized at
    // instantiation. The memory struct only cares about preserving alignment
    // when handing out ptrs into it at runtime. Interpreting stored memory
    // properly is the responsibility of those interfacing with it.
    memory: Vec<u8>,

    // Points to the last position in memory which is actually in use.  Do not
    // use directly to get a fresh ptr into memory.  Instead use
    // `next_aligned_ptr` method for a fresh correctly aligned ptr into memory
    // for the target architecture.
    next_free: usize,

    target_alignment: usize,
}

impl Memory {
    pub fn new(size: usize) -> Memory {
        let alignment = align_of::<usize>();
        Memory {
            memory: vec![0; size],
            next_free: 0,
            target_alignment: alignment
        }
    }

    /// Returns a pointer to next free block of memory of size n. Begins at index
    /// of the heap pointer.
    //
    // TODO: There is no free list so once a block of memory is allocated it is
    // not yet possible to free it.
    pub fn next_aligned_ptr(&mut self, size: usize) -> usize {
        let r = self.next_free % self.target_alignment;
        if r > 0 {
            self.next_free += self.target_alignment - r;
        }

        if (self.next_free + size) >= self.memory.len() {
            panic!("Out of memory.")
        };
        self.next_free
    }

    fn store(&mut self, ptr: usize, value: Vec<u8>) {
        // Iterate over indexes, as we want to replace values, not shift them
        let mut ptr = ptr;
        for b in value {
            self.memory[ptr] = b;
            ptr += 1;
        }
        self.next_free = ptr
    }

    fn read(&self, ptr: usize, size: usize) -> &[u8] {
        let end = ptr + size;
        &self.memory[ptr..end]
    }
}

/// A simple stack frame based virtual machine which is used to interpret MIR
/// instructions.
pub struct Machine<'a, 'tcx: 'a> {
    stack: Vec<Frame<'tcx>>,
    funcs: HashMap<DefId, Rc<Function<'tcx>>>,
    memory: Memory,
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
}

impl<'a, 'tcx>  Machine<'a, 'tcx> {
    pub fn new(memory: Memory, tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Machine<'a, 'tcx> {
        Self {
            stack: vec![],
            funcs: HashMap::new(),
            memory: memory,
            tcx: tcx
        }
    }

    pub fn cur_frame(&self) -> &Frame<'tcx> {
        self.stack.last().unwrap()
    }

    pub fn cur_frame_mut(&mut self) -> &mut Frame<'tcx> {
        self.stack.last_mut().unwrap()
    }

    /// Retrieves a Function reference for a DefId from the Machine's storage.
    /// If it does not exist, the Function struct will be lazily instantiated
    /// and inserted for future use.
    pub fn get_or_insert_func(&mut self, def_id: DefId) -> &mut Rc<Function<'tcx>> {
        self.funcs.entry(def_id).or_insert({
            let instance = Instance::mono(self.tcx, def_id).def;
            let mir = match instance {
                InstanceDef::Item(def_id) => {
                    self.tcx.maybe_optimized_mir(def_id).unwrap()
                },
                _ => self.tcx.instance_mir(instance),
            };
            Rc::new(Function::new(def_id, mir))
        })
    }

    pub fn push_frame(&mut self,
                      def_id: DefId,
                      args: Vec<TyVal<'tcx>>,
                      ret_val: Option<Address>,
                      ret_block: Option<BasicBlock>) {
        let func = self.get_or_insert_func(def_id).clone();
        // Init locals with args and zero the rest
        let mut locals: Vec<u8> = vec![0; func.locals_size];
        let args: Vec<u8> = args.into_iter().flat_map(|x| x.to_bytes()).collect();
        locals.splice(0..args.len(), args.into_iter());

        let frame = Frame::new(func.clone(), locals, ret_val, ret_block);
        self.stack.push(frame);
    }

    pub fn pop_frame(&mut self) -> Frame {
        self.stack.pop()
            .expect("Popped from empty stack")
    }

    pub fn store(&mut self, bytes: Vec<u8>, dest: Address) {
        match dest {
            Address::Local(ptr) => {
                self.cur_frame_mut().set_bytes(ptr, bytes)
            },
            Address::Heap(ptr) =>  {
                assert_eq!(ptr.size, bytes.len());
                self.memory.store(ptr.addr, bytes)
            }
        }
    }

    pub fn read(&self, dest: Address) -> &[u8] {
        match dest {
            Address::Local(ptr) => {
                self.cur_frame().get_bytes(ptr)
            },
            Address::Heap(ptr) =>  {
                self.memory.read(ptr.addr, ptr.size)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn mem_alloc_ptr_aligns_block() {
        let mut m = Memory::new(32);
        let ptr = m.next_aligned_ptr(15);
        assert_eq!(ptr, 0);

        // Emulate behaviour of storage
        m.next_free = 15;
        let ptr = m.next_aligned_ptr(8);
        assert_eq!(ptr, 16);
    }

    #[test]
    #[should_panic]
    fn mem_alloc_panics_on_overflow() {
        let mut m = Memory::new(32);
        let ptr = m.next_aligned_ptr(100);
    }

    #[test]
    fn store_and_read() {
        let mut m = Memory::new(32);
        let ptr = m.next_aligned_ptr(15);

        let data = vec![1; 8];
        m.store(ptr, data.clone());
        assert_eq!(m.read(ptr, data.len()), data.as_slice());
    }
}
