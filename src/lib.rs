#![feature(rustc_private, link_args)]
extern crate rustc;
extern crate rustc_data_structures;
extern crate syntax;
extern crate byteorder;

pub mod interp;
pub mod machine;
