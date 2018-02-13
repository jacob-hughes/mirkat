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

use rustc_const_math::ConstInt;
use rustc::mir::{Operand, Constant, Literal};
use rustc::middle::const_val::ConstVal;
use rustc::ty::{Ty, TypeVariants};
use syntax::ast::{IntTy, UintTy};

use interp::TypedVal;
use machine::Machine;


pub trait ByteCast {
    type T;

    fn to_bytes(&self) -> Vec<u8>;

    fn new_from(bytes: &[u8], ty: TypeVariants) -> Self::T;
}

impl<'tcx> ByteCast for ConstVal<'tcx> {
    type T = ConstVal<'tcx>;

    fn to_bytes(&self) -> Vec<u8> {
        match *self {
            ConstVal::Integral(ref ci) => ci.to_bytes(),
            _ => unimplemented!()
        }
    }

    fn new_from(bytes: &[u8], ty: TypeVariants)-> ConstVal<'tcx> {
        unimplemented!()
    }
}

impl<'tcx> ByteCast for ConstInt {
    type T = ConstInt;

    fn to_bytes(&self) -> Vec<u8> {
        match *self {
            ConstInt::I8(n) => vec![n as u8],
            ConstInt::I16(n) => {
                let mut buf = [0; 2]; LittleEndian::write_i16(&mut buf, n);
                buf.to_vec()
            }
            ConstInt::I32(n) => {
                let mut buf = [0; 4];
                LittleEndian::write_i32(&mut buf, n);
                buf.to_vec()
            }
            ConstInt::I64(n) => {
                let mut buf = [0; 8];
                LittleEndian::write_i64(&mut buf, n);
                buf.to_vec()
            }
            ConstInt::U8(n) => vec![n],
            ConstInt::U16(n) => {
                let mut buf = [0; 2];
                LittleEndian::write_u16(&mut buf, n);
                buf.to_vec()
            }
            ConstInt::U32(n) => {
                let mut buf = [0; 4];
                LittleEndian::write_u32(&mut buf, n);
                buf.to_vec()
            }
            ConstInt::U64(n) => {
                let mut buf = [0; 8];
                LittleEndian::write_u64(&mut buf, n);
                buf.to_vec()
            }
            _ => unimplemented!()
        }
    }

    fn new_from(bytes: &[u8], ty: TypeVariants) -> ConstInt {
        match ty {
            TypeVariants::TyInt(int_ty) =>  {
                match int_ty {
                    IntTy::I8 => ConstInt::I8(bytes[0] as i8),
                    IntTy::I16 => {
                        let lit = LittleEndian::read_i16(bytes);
                        ConstInt::I16(lit)
                    }
                    IntTy::I32 => {
                        let lit = LittleEndian::read_i32(bytes);
                        ConstInt::I32(lit)
                    }
                    IntTy::I64 => {
                        let lit = LittleEndian::read_i64(bytes);
                        ConstInt::I64(lit)
                    }
                    _ => unimplemented!()
                }
            }
            TypeVariants::TyUint(uint_ty) => {
                match uint_ty {
                    UintTy::U8 => ConstInt::U8(bytes[0]),
                    UintTy::U16 => {
                        let lit = LittleEndian::read_u16(bytes);
                        ConstInt::U16(lit)
                    }
                    UintTy::U32 => {
                        let lit = LittleEndian::read_u32(bytes);
                        ConstInt::U32(lit)
                    }
                    UintTy::U64 => {
                        let lit = LittleEndian::read_u64(bytes);
                        ConstInt::U64(lit)
                    }
                    _ => unimplemented!()
                }
            }
            _ => panic!("Only an integer was expected")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn up_and_downcast_i32() {
        let origin = ConstInt::I32(50);
        let ty = TypeVariants::TyInt(IntTy::I32);
        let bytes = origin.to_bytes();

        let new = ConstInt::new_from(bytes.as_slice(), ty);
        assert_eq!(origin, new);
    }

    #[test]
    fn up_and_downcast_u32() {
        let origin = ConstInt::U32(50);
        let ty = TypeVariants::TyUint(UintTy::U32);
        let bytes = origin.to_bytes();

        let new = ConstInt::new_from(bytes.as_slice(), ty);
        assert_eq!(origin, new);
    }

    #[test]
    #[should_panic]
    fn const_int_non_int_type() {
        let origin = ConstInt::U32(50);
        let ty = TypeVariants::TyChar;
        let bytes = origin.to_bytes();
        let new = ConstInt::new_from(bytes.as_slice(), ty);
    }
}
