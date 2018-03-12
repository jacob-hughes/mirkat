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

use byteorder::{ByteOrder, LittleEndian};
use std::process::exit;
use std::mem;
use rustc::ty;
use rustc::ty::{Ty, TyCtxt, TypeVariants};
use rustc::hir::def_id::DefId;
use rustc::middle::const_val::ConstVal;
use rustc::mir::{
    START_BLOCK, Mir, BasicBlock, BasicBlockData, Statement, StatementKind,
    Rvalue, Place, Terminator, TerminatorKind, AggregateKind, Operand, Constant,
    Literal, BinOp, ProjectionElem
};
use rustc_data_structures::indexed_vec::Idx;
use syntax::ast::{IntTy, UintTy};

use machine;
use machine::{Machine, Address, Ptr};

const MEMORY_CAPACITY: usize = 1024; // in Bytes.

#[derive(Debug, Clone)]
pub enum Value {
    Int(u128),
    Bool(bool),
    Ref(usize), // a Rust ptr
    Aggregate(Vec<Value>), // Tuple, struct etc..
    None,
}

impl<'tcx> Value {
    fn to_bytes(&self, ty: Ty<'tcx>) -> Vec<u8> {
        match ty.sty {
            TypeVariants::TyInt(int_ty) => {
                let val = match *self {
                    Value::Int(i) => i,
                    _ => panic!("Mismatched Types")
                };

                match int_ty {
                    IntTy::I32 => {
                        let mut buf = [0; 4];
                        LittleEndian::write_i32(&mut buf, val as i32);
                        return buf.to_vec();
                    },
                    _ => unimplemented!()
                }
            },
            TypeVariants::TyBool => {
                match *self {
                    Value::Bool(b) => {
                        vec![b as u8]
                    },
                    _ => panic!("Mismatched Types")
                }
            },
            TypeVariants::TyTuple(ref elem_tys, ..) => {
                match *self {
                    Value::Aggregate(ref elems) =>  {
                        let mut bytes: Vec<u8> = Vec::new();
                        for (elem, ty) in elems.iter().zip(elem_tys.iter()) {
                            bytes.extend(elem.to_bytes(ty))
                        }
                        return bytes;
                    },
                    _ => panic!("Mismatched Types")
                }
            }
            _ => unimplemented!()
        }
    }

    pub fn from_bytes(bytes: Vec<u8>, ty: Ty<'tcx>) -> Self {
        match ty.sty {
            TypeVariants::TyInt(int_ty) => match int_ty {
                IntTy::I32 => {
                    let v = LittleEndian::read_i32(bytes.as_slice());
                    return Value::Int(v as u128);
                },
                _ => unimplemented!()
            },
            TypeVariants::TyBool => {
                assert_eq!(bytes.len(), 1);
                let val = bytes[0] == 1;
                return Value::Bool(val)
            },
            TypeVariants::TyTuple(ref elem_types, ..) => {
                let mut start = 0;
                let mut vals: Vec<Value> = Vec::new();
                for ty in elem_types.iter() {
                    let end = start + size_of(ty);
                    let sub = bytes[start..end].to_vec();
                    vals.push(Value::from_bytes(sub, ty));
                    start = end;
                }
                return Value::Aggregate(vals);
            }
            _ => unimplemented!()
        }
    }
}

/// A Rust MIR value and its type. Used to help de/serialize values to bytes for
/// storing in memory.
#[derive(Debug, Clone)]
pub struct TyVal<'tcx> {
    ty: Ty<'tcx>,
    val: Value,
}

impl<'tcx> TyVal<'tcx> {
    pub fn new(ty: Ty<'tcx>, val: Value) -> Self {
        Self {
            ty: ty,
            val: val
        }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        self.val.to_bytes(&self.ty)
    }

    pub fn from_bytes(bytes: Vec<u8>, ty: Ty<'tcx>) -> Self {
        let val = Value::from_bytes(bytes, ty);
        TyVal::new(ty, val)
    }

}

impl<'a, 'tcx> Machine<'a, 'tcx> {
    /// Evaluates a function call, pushing a new stack frame.
    pub fn eval_fn_call(&mut self,
                        def_id: DefId,
                        args: Vec<TyVal<'tcx>>,
                        ret_val: Option<Address>,
                        ret_block: Option<BasicBlock>) {
        self.push_frame(def_id, args, ret_val, ret_block);
        self.eval_basic_block(START_BLOCK)
    }

    /// The easy bit. `BasicBlock`s are a list of instructions which are guaranteed to
    /// always be executed sequentially. We just need to iterate over the statement
    /// list and execute each one in order.
    fn eval_basic_block(&mut self,
                        block: BasicBlock) {
        let basic_block_data = self.cur_frame()
                               .mir.basic_blocks()
                               .get(block)
                               .unwrap();
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
                self.store(val.to_bytes(dest_ty), dest);
            },
            Rvalue::CheckedBinaryOp(binop, ref lhs, ref rhs) => {
                // We assume that the lhs and rhs are of the same type
                let lhs = self.eval_operand(lhs);
                let rhs = self.eval_operand(rhs);
                let (res, overflow) = self.binary_op(binop, lhs, rhs);
                let val = Value::Aggregate(vec![res, overflow]);
                self.store(val.to_bytes(dest_ty), dest);
            },
            Rvalue::Aggregate(ref kind, ref ops) => {
                match **kind {
                    AggregateKind::Tuple => {
                        if ops.len() == 0 {
                            return; // Unit type is empty tuple, and zero-sized.
                        }

                        let mut vals: Vec<Value> = Vec::new();
                        for op in ops.iter() {
                            let val = self.eval_operand(op).val;
                            vals.push(val);
                        }
                    },
                    _ => unimplemented!()
                }
            },
            _ => unimplemented!("{:?}", rvalue)
        }
    }

    fn binary_op(&self,
                 binop: BinOp,
                 lhs: TyVal<'tcx>,
                 rhs: TyVal<'tcx>)
                 -> (Value, Value) {
        match binop {
            BinOp::Add => {
                match (lhs.val, rhs.val) {
                    (Value::Int(lv), Value::Int(rv)) => {
                        assert_eq!(lhs.ty, rhs.ty);
                        let res = lv + rv;
                        let overflow = !in_bounds(res, &lhs.ty);
                        (Value::Int(res), Value::Bool(overflow))
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
                // Move the ret_block, otherwise we borrow twice.
                let ret_block = self.cur_frame().ret_block;
                self.pop_frame();
                match ret_block {
                    Some(bb) => {
                        self.eval_basic_block(bb)
                    },
                    None => exit(0),
                }
            },
            TerminatorKind::Call {
                ref func,
                ref args,
                ref destination,
                ref cleanup
            } => {
                let (ret_val, ret_block) = match *destination {
                    Some((ref place, bb)) => (Some(self.eval_place(place)), Some(bb)),
                    None => (None, None)
                };
                let func = self.eval_operand(func);
                let fn_def = match func.ty.sty {
                    ty::TyFnDef(def_id, substs) => {
                        ty::Instance::resolve(
                            self.tcx,
                            self.tcx.param_env(def_id),
                            def_id,
                            substs,
                        ).unwrap()
                    },
                    _ => unimplemented!()
                };

                let args: Vec<TyVal> = args.iter()
                    .map(|arg| self.eval_operand(arg))
                    .collect();
                self.eval_fn_call(fn_def.def_id(), args, ret_val, ret_block)
            },
            TerminatorKind::Assert {
                ref cond,
                expected,
                ref msg,
                target,
                ref cleanup
            } => {
                let cond = self.eval_operand(cond).val;
                let cond_val = match cond {
                    Value::Bool(b) => b,
                    _ => panic!("Mismatched type")
                };

                if cond_val == expected {
                    self.eval_basic_block(target);
                } else {
                    panic!("{:?}", msg);
                }
            }
            _ => unimplemented!("{:?}", terminator.kind)
        }
    }

    /// A `Place` is a MIR construct which describes a pointer into some position in
    /// memory (be it local, static, or on the heap). In Mirkat, we use the
    /// information from the `Place` to create an `Address` - an enum pointing to a
    /// location inside the Machine.
    fn eval_place(&mut self, place: &Place<'tcx>) -> Address {
        match *place {
            Place::Local(local) => {
                let ptr = self.cur_frame().local_ptr(local);
                Address::Local(ptr)
            }
            Place::Projection(ref proj) => {
                match proj.elem {
                    ProjectionElem::Field(field, _) => {
                        let base_ty = self.place_ty(&proj.base);
                        let base_addr = self.eval_place(&proj.base);
                        // I'm not sure how correct this is. This may fail if we
                        // recursively call through projections. Unfortunately,
                        // I'm not sure why this would ever be the case
                        // though... Nested field access is turned into local
                        // move's in MIR, so perhaps it's an edge case not worth
                        // worrying about.
                        assert_ne!(mem::discriminant(&proj.base), mem::discriminant(place));

                        match base_addr {
                            Address::Local(p) => {
                                let ptr = self.field_ptr(p, field.index(), base_ty);
                                return Address::Local(ptr);
                            },
                            Address::Heap(p) => {
                                let ptr = self.field_ptr(p, field.index(), base_ty);
                                return Address::Heap(ptr);
                            },
                        }
                    },
                    _ => unimplemented!("{:?}", proj.elem)
                }
            },
            Place::Static(ref static_) => unimplemented!(),
        }
    }

    /// Given a pointer to some aggregate type, this will return a new, more
    /// granular pointer to the field specified by the field index.
    pub fn field_ptr(&self, ptr: Ptr, field_idx: usize, ty: Ty<'tcx>) -> Ptr {
        let (start, size) = match ty.sty {
            TypeVariants::TyTuple(ref elem_types, ..) => {
                let mut start = 0;
                let mut size = 0;
                for (i, ty) in elem_types.iter().enumerate() {
                    if i == field_idx {
                        size = size_of(ty);
                        break;
                    }
                    start += size_of(ty);
                }
                (start, size)
            },
            _ => unimplemented!()
        };
        assert!(size <= ptr.size);
        let addr = ptr.addr + start;
        Ptr::new(addr, size)
    }

    fn get_value_from_place(&mut self,
                           place: &Place<'tcx>,
                           ty: Ty<'tcx>)
                           -> TyVal<'tcx> {
        let addr = self.eval_place(place);
        let bytes = self.read(addr).to_vec();
        TyVal::from_bytes(bytes, ty)
    }

    fn place_ty(&self, place: &Place<'tcx>) -> Ty<'tcx> {
        place.ty(self.cur_frame().mir, self.tcx).to_ty(self.tcx)
    }

    /// An operand's value can always be determined without needing to temporarily
    /// save values to a stack. This is because of the recursive nature of the MIR.
    /// An operand will only ever return a primitive value or a pointer.
    fn eval_operand(&mut self,
                    operand: &Operand<'tcx>)
                    -> TyVal<'tcx> {
        let ty = operand.ty(self.cur_frame().mir, self.tcx);
        match *operand {
            Operand::Copy(ref place) |
            Operand::Move(ref place) => {
                self.get_value_from_place(place, ty)
            }
            Operand::Constant(ref constant) => {
                let val: Value;
                match constant.literal {
                    Literal::Value { ref value } => {
                        match value.val {
                            ConstVal::Integral(int) => {
                                val = Value::Int(int.to_u128().unwrap())
                            },
                            ConstVal::Bool(b) => {
                                val = Value::Bool(b)
                            },
                            ConstVal::Function(def_if, substs) => {
                                val = Value::None
                            }
                            _ => unimplemented!("{:?}", value.val)
                        }
                    },
                    Literal::Promoted { index } => {
                        unimplemented!()
                    }
                };
                TyVal::new(ty, val)
            },
        }
    }
}

/// Returns the exact number of bytes required to store a given type. Useful for
/// calling before reading bytes from memory.
pub fn size_of<'tcx>(ty: Ty<'tcx>) -> usize {
    use::syntax::ast::IntTy;
    match ty.sty {
        TypeVariants::TyInt(int_ty) => match int_ty {
            IntTy::I8 => 1,
            IntTy::I16 => 2,
            IntTy::I32 => 4,
            IntTy::I64 => 8,
            IntTy::I128 => 16,
            _ => unimplemented!(),
        },
        TypeVariants::TyUint(uint_ty) => match uint_ty {
            UintTy::U8 => 1,
            UintTy::U16 => 2,
            UintTy::U32 => 4,
            UintTy::U64 => 8,
            UintTy::U128 => 16,
            _ => unimplemented!(),
        },
        TypeVariants::TyBool => 1,
        TypeVariants::TyTuple(tys, ..) => {
            let mut size = 0;
            for t in tys.iter() {
                size += size_of(t);
            }
            size
        },
        _ => unimplemented!("{:?}", ty.sty),
    }
}

/// Builds a VM and starts interpretation from the given MIR function, this is
/// normally the main method.
pub fn entry_point<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                             def_id: DefId) {
    let m = machine::Memory::new(MEMORY_CAPACITY);
    let mut vm = Machine::new(m, tcx);
    vm.eval_fn_call(def_id, vec![], None, None);
}

fn in_bounds<'tcx>(val: u128, ty: Ty<'tcx>) -> bool {
    match ty.sty {
        TypeVariants::TyInt(int_ty) => {
            match int_ty {
                IntTy::I32 => {
                    let val = val as i32;
                    val >= <i32>::min_value() && val <= <i32>::max_value()
                },
                _ => unimplemented!()
            }
        },
        _ => unimplemented!()
    }
}

