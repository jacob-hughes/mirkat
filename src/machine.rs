// Copyright (c) 2018 King's College London
// created by the Software Development Team <http://soft-dev.org/>
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
// (a) the Software, and
// (b) any piece of software and/or hardware listed in the lrgrwrks.txt file
// if one is included with the Software (each a "Larger Work" to which the Software
// is contributed by such licensors),
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
// Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use std::collections::HashMap;
use std::mem::align_of;

use rustc::mir::{Mir, Local};

use interp::TypedVal;

#[derive(Debug)]
pub struct Frame<'tcx> {
    // Each MIR is a CFG of a single function in Rust, so it makes sense
    // for this to be in the frame.
    mir: Mir<'tcx>,

    // FIXME: Hacky... I can't find a way to actually access the private u32
    // inside the `Local` tuple struct. `Local` does  implement the Hashable
    // and PartialEQ trait however, so for  now it might just work to to use it
    // as the key
    locals: HashMap<Local, Vec<u8>>
}

impl<'tcx> Frame<'tcx> {
    fn new(mir: Mir<'tcx>) -> Frame {
        Frame {
            locals: HashMap::new(),
            mir:    mir
        }
    }

    fn set_local(&mut self, local: Local, val: Vec<u8>) {
        self.locals.insert(local, val);
    }

    fn get_local(&self, local: Local) -> &Vec<u8> {
        &self.locals[&local]
    }
}

// Represents a pointer into some kind of memory
// TODO: Extend to work with static constructs
enum Address {
    Heap(usize), // pointer to offset in memory
    Local(Local)
}


pub struct Memory {
    // Memory is a simple vector of bytes whose size is parameterized at
    // instantiation. The memory struct only cares about preserving alignment
    // when handing out ptrs into it at runtime. Interpreting stored memory
    // properly is the responsibility of those interfacing with it.
    memory: Vec<u8>,

    // Points to the last position in memory which is actually in use.
    // Do not use directly to get a fresh ptr into memory.
    // Instead use `next_aligned_ptr` method for a fresh correctly aligned ptr
    // into memory for the target architecture.
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

    // Returns a pointer to next free block of memory of size n. Begins at index
    // of the heap pointer.
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

    // TODO: It would be nice not to have to provide the size each time.
    fn read(&self, ptr: usize, size: usize) -> &[u8] {
        let end = ptr + size;
        &self.memory[ptr..end]
    }
}

/// A simple stack frame based virtual machine which is used to interpret
/// Rust's MIR.
pub struct Machine<'tcx> {
    stack: Vec<Frame<'tcx>>,
    memory: Memory,
}

impl<'tcx> Machine<'tcx> {
    pub fn new(memory: Memory) -> Machine<'tcx> {
        Machine {
            stack: vec![],
            memory: memory,
        }
    }

    pub fn cur_frame(&self) -> &Frame<'tcx> {
        self.stack.last().unwrap()
    }

    pub fn cur_frame_mut(&mut self) -> &mut Frame<'tcx> {
        self.stack.last_mut().unwrap()
    }

    fn store(&mut self, tv: TypedVal, dest: Address) {
        match dest {
            Address::Local(key) => {
                self.cur_frame_mut().set_local(key, tv.val)
            },
            Address::Heap(ptr) =>  {
                self.memory.store(ptr, tv.val)
            }
        }
    }

    fn read(&self, dest: Address, size: usize) -> &[u8] {
        match dest {
            Address::Local(key) => {
                self.cur_frame().get_local(key)
            }
            Address::Heap(ptr) => {
                self.memory.read(ptr, size)
            }
        }
    }
}
