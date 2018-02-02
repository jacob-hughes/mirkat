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

#![feature(rustc_private, link_args)]
extern crate getopts;
extern crate rustc;
extern crate rustc_driver;
extern crate syntax;
extern crate byteorder;
extern crate rustc_const_math;
extern crate mirkat;

use rustc_driver::{driver, CompilerCalls};
use rustc::ty::TyCtxt;
use rustc::session::Session;
use std::process;
use rustc::hir::def_id::DefId;
pub use rustc_const_math::ConstInt;

use mirkat::machine::{Machine, Memory};

/// This struct is required by the rustc API in order to implement traits which
/// are used to hook into the compiler and customise the build pipeline. In
/// Mirkat, we stop compilation after the MIR has been generated and then hand
/// the MIR over to the interpreter. This means that Mirkat's invocation of rustc
/// will never hit LLVM.
struct MirkatCompilerCalls { }

impl<'a> CompilerCalls<'a> for MirkatCompilerCalls {
    fn build_controller(&mut self,
                        _: &Session,
                        _: &getopts::Matches)
                        -> driver::CompileController<'a> {
        let mut control = driver::CompileController::basic();

        control.after_analysis.stop = rustc_driver::Compilation::Stop;
        control.after_analysis.callback = Box::new(move |state| {
            state.session.abort_if_errors();
            let tcx = state.tcx.unwrap();
            if let Some((entry_node_id, _)) = *state.session.entry_fn.borrow() {
                let entry_def_id = tcx.hir.local_def_id(entry_node_id);
                let _start_wrapper = tcx.lang_items().start_fn().and_then(|start_fn| {
                    if tcx.is_mir_available(start_fn) {
                        Some(start_fn)
                    } else {
                        None
                    }
                });
            }
            else {
                panic!("No main function found");
            }
        });
        control
    }
}

/// Without specifying the sysroot, the rustc library can't be used.  This code
/// was taken from Miri, it looks for a MIRKAT_SYSROOT environment variable and
/// complains if one isn't found.
/// https://github.com/solson/miri/blob/919604e1ead8294c8ca14f101be4380ea1ea370c/miri/bin/miri.rs#L228
fn find_sysroot() -> String {
    if let Ok(sysroot) = std::env::var("MIRKAT_SYSROOT") {
        return sysroot;
    }

    // Taken from https://github.com/Manishearth/rust-clippy/pull/911.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => {
            option_env!("RUST_SYSROOT")
                .expect(
                    "need to specify RUST_SYSROOT env var or use rustup or multirust",
                )
                .to_owned()
        }
    }
}


fn main() {
    let mut args: Vec<String> = std::env::args().collect();

    let sysroot_flag = String::from("--sysroot");
    if !args.contains(&sysroot_flag) {
        args.push(sysroot_flag);
        args.push(find_sysroot());
    }
    let mut compiler_calls = MirkatCompilerCalls{};
    match rustc_driver::run_compiler(&args, &mut compiler_calls, None, None) {
        (Ok(_), _) => {
            process::exit(0)
        }
        (Err(_code), _) => process::exit(1),
    }
}

