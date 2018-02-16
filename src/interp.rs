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
// Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use std::process::exit;
use rustc::ty;
use rustc::ty::{Ty, TyCtxt};
use rustc::hir::def_id::DefId;
use rustc::mir::{
    START_BLOCK, Mir, BasicBlock, BasicBlockData, Statement, StatementKind,
    Rvalue, Place, Terminator, TerminatorKind, AggregateKind, Operand, Constant,
    Literal
};

use machine;
use machine::{Machine, Address};
use primitive::ByteCast;

const MEMORY_CAPACITY: usize = 1024; // in Bytes.

/// Stores a value represented as a vector of bytes, along with its type
/// annotation. It's important to keep track of a value's type while it is
/// being evaluated, so that we know how to interpret the bytes.
#[derive(Debug, Clone)]
pub struct TypedVal<'tcx> {
    pub ty: Ty<'tcx>,
    pub val: Vec<u8>,
}

impl<'a, 'tcx> Machine<'a, 'tcx> {
    /// Evaluates a function call, pushing a new stack frame.
    pub fn eval_fn_call(&mut self,
                        def_id: DefId,
                        ret_addr: Option<BasicBlock>) {
        self.push_frame(def_id, ret_addr);
        self.eval_basic_block(START_BLOCK)
    }

    /// The easy bit. `BasicBlock`s are a list of instructions which are guaranteed to
    /// always be executed sequentially. We just need to iterate over the statement
    /// list and execute each one in order.
    fn eval_basic_block(&mut self,
                        block: BasicBlock) {
        let basic_block_data = self.cur_frame().mir.basic_blocks().get(block).unwrap();
        for statement in &basic_block_data.statements {
            self.eval_statement(block, statement)
        }

        let term = basic_block_data.terminator();
        self.eval_terminator(term);
    }

    fn eval_statement(&mut self,
                      block: BasicBlock,
                      statement: &Statement<'tcx>) {
        match statement.kind {
            StatementKind::Assign(ref place, ref rvalue) => {
                self.eval_assign(block, place, rvalue)
            },
            StatementKind::StorageLive(local) => {
                // XXX: NotImplemented
            },
            StatementKind::StorageDead(local) => {
                // XXX: NotImplemented
            }
            _ => unimplemented!()
        }
    }

    /// The RHS of an assignment is first evaluated to a primitive. This will be
    /// either a pointer into memory or a primitive. It is then mapped to the
    /// required place in memory.
    fn eval_assign(&mut self,
                   _block: BasicBlock,
                   place: &Place<'tcx>,
                   rvalue: &Rvalue<'tcx>) {
        let dest = self.eval_place(place);
        let ref dest_ty = place.ty(self.cur_frame().mir, self.tcx).to_ty(self.tcx);
        match *rvalue {
            Rvalue::Use(ref operand) => {
                let val = self.eval_operand(operand).val;
                let tyval = TypedVal {
                    ty: dest_ty,
                    val: val
                };
                self.store(tyval, dest);
            },
            Rvalue::Aggregate(ref kind, ref ops) => {
                match **kind {
                    AggregateKind::Tuple => {
                        // XXX: Tuple layout needs some proper thought, and
                        // should be upcoming in the next PR, so we handle the
                        // empty tuple explicitly as this is the bottom type in
                        // Rust.
                        if ops.len() != 0 {
                            unimplemented!()
                        }
                    },
                    _ => unimplemented!()
                }
            },
            _ => unimplemented!()
        }
    }

    /// Each `BasicBlock` is succeeded by a `Terminator`, which encapsulates control
    /// flow. A `Terminator` determines the next `BasicBlock` that should be jumped to
    /// during execution.
    fn eval_terminator(&mut self,
                       terminator: &Terminator<'tcx>) {
        match terminator.kind {
            TerminatorKind::Goto { target } => {
                self.eval_basic_block(target)
            }
            TerminatorKind::Return =>  {
                // Move the ret_addr, otherwise we borrow twice.
                let ret_addr = self.cur_frame().ret_addr;
                match ret_addr {
                    Some(bb) => {
                        self.eval_basic_block(bb)
                    },
                    None => exit(0),
                }
            },
            _ => unimplemented!()
        }
    }

    /// A `Place` is a MIR construct which describes a pointer into some position in
    /// memory (be it local, static, or on the heap). In Mirkat, we use the
    /// information from the `Place` to create an `Address` - an enum pointing to a
    /// location inside the Machine.
    fn eval_place(&mut self, place: &Place<'tcx>) -> Address {
        match *place {
            Place::Local(local) => Address::Local(local),
            Place::Static(ref static_) => unimplemented!(),
            Place::Projection(ref proj) => unimplemented!(),
        }
    }

    /// An operand's value can always be determined without needing to temporarily
    /// save values to a stack. This is because of the recursive nature of the MIR.
    /// An operand will only ever return a primitive value or a pointer.
    fn eval_operand(&mut self,
                    operand: &Operand<'tcx>)
                    -> TypedVal<'tcx> {
        let ty = operand.ty(self.cur_frame().mir, self.tcx);
        match *operand {
            Operand::Copy(ref place) |
            Operand::Move(ref place) => {
                unimplemented!()
            }
            Operand::Constant(ref constant) => {
                let Constant {ref literal, ..} = **constant;
                let val = match *literal {
                    Literal::Value { ref value } => value.val.to_bytes(),
                    Literal::Promoted { index } => {
                        unimplemented!()
                    }
                };
                return TypedVal {
                    val,
                    ty
                }
            }
        }
    }
}

/// Builds a VM and starts interpretation from the given MIR function, this is
/// normally the main method.
pub fn entry_point<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                             def_id: DefId) {
    let m = machine::Memory::new(MEMORY_CAPACITY);
    let mut vm = Machine::new(m, tcx);
    vm.eval_fn_call(def_id, None);
}

