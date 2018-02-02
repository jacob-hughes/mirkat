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

use rustc::ty::{Ty, TyCtxt};
use rustc::mir::{
    START_BLOCK, Mir, BasicBlock, BasicBlockData, Statement, StatementKind,
    Rvalue, Place, Terminator, TerminatorKind
};

use machine;
use machine::{Machine, Address};
use primitive::eval_operand;

const MEMORY_CAPACITY: usize = 1024; // in Bytes.

/// Stores a value represented as a vector of bytes, along with its type
/// annotation. It's important to keep track of a value's type while it is
/// being evaluated, so that we know how to interpret the bytes.
#[derive(Debug, Clone)]
pub struct TypedVal<'tcx> {
    pub ty: Ty<'tcx>,
    pub val: Vec<u8>,
}

/// Builds a VM and starts interpretation from the given MIR function, this is
/// normally the main method.
pub fn entry_point<'a, 'tcx>(mir: &'tcx Mir<'tcx>,
                             tcx: TyCtxt<'a, 'tcx, 'tcx>) {
    let m = machine::Memory::new(MEMORY_CAPACITY);
    let mut vm = Machine::new(m, tcx);
    eval_mir(mir, &mut vm);
}

/// Evaluates a function call, pushing a new stack frame.
pub fn eval_mir<'a, 'tcx>(mir: &'tcx Mir<'tcx>,
                          vm: &mut Machine<'a, 'tcx>) {
    let frame = machine::Frame::new(mir);
    vm.push(frame);
    eval_basic_block(START_BLOCK, vm)
}

/// The easy bit. `BasicBlock`s are a list of instructions which are guaranteed to
/// always be executed sequentially. We just need to iterate over the statement
/// list and execute each one in order.
fn eval_basic_block(block: BasicBlock,
                    vm: &mut Machine) {
    let basic_block_data = vm.cur_frame().mir.basic_blocks().get(block).unwrap();
    for statement in &basic_block_data.statements {
        eval_statement(block, statement, vm)
    }

    let term = basic_block_data.terminator();
    eval_terminator(term, vm);
}

fn eval_statement<'a, 'tcx>(block: BasicBlock,
                  statement: &Statement<'tcx>,
                  vm: &mut Machine<'a, 'tcx>) {
    match statement.kind {
        StatementKind::Assign(ref place, ref rvalue) => {
            eval_assign(block, place, rvalue, vm)
        }
        _ => unimplemented!()
    }
}

/// The RHS of an assignment is first evaluated to a primitive. This will be
/// either a pointer into memory or a primitive. It is then mapped to the
/// required place in memory.
fn eval_assign<'a, 'tcx>(_block: BasicBlock,
                         place: &Place<'tcx>,
                         rvalue: &Rvalue<'tcx>,
                         vm: &mut Machine<'a, 'tcx>) {
    let dest = eval_place(place);
    let ref dest_ty = place.ty(vm.cur_frame().mir, vm.tcx).to_ty(vm.tcx);
    match *rvalue {
        Rvalue::Use(ref operand) => {
            let val = eval_operand(operand, vm).val;
            let tyval = TypedVal {
                ty: dest_ty,
                val: val
            };
            vm.store(tyval, dest);
        }
        _ => unimplemented!()
    }
}

/// Each `BasicBlock` is succeeded by a `Terminator`, which encapsulates control
/// flow. A `Terminator` determines the next `BasicBlock` that should be jumped to
/// during execution.
fn eval_terminator<'a,'tcx>(terminator: &Terminator<'tcx>,
                            vm: &mut Machine<'a, 'tcx>) {
    let Terminator {
        ref kind,
        ..
    } = *terminator;

    match *kind {
        TerminatorKind::Goto { target } => {
            eval_basic_block(target, vm)
        }
        _ => unimplemented!()
    }
}

/// A `Place` is a MIR construct which describes a pointer into some position in
/// memory (be it local, static, or on the heap). In Mirkat, we use the
/// information from the `Place` to create an `Address` - a struct pointing to a
/// location inside the Machine.
fn eval_place<'tcx>(place: &Place<'tcx>) -> Address {
    match *place {
        Place::Local(local) => Address::Local(local),
        Place::Static(ref static_) => unimplemented!(),
        Place::Projection(ref proj) => unimplemented!(),
    }
}

