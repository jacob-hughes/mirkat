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

extern crate mirkat;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const STATUS_CODE_OK: i32 = 0;
const COMPILE_PASS_DIR: &str = "./tests/compile_pass";

/// Invokes Mirkat when given a path to a valid Rust program. Compares the
/// expected return code against that returned from Mirkat. This is surprisingly
/// effective at catching bugs in Mirkat. It's not uncommon that when things go
/// wrong, Mirkat blows up catastrophically.
fn test_prog(path: &Path, status_code: i32) -> bool {
    eprint!("test {:?} ... ", path.file_name().unwrap());
    if status_code == run_prog(path) {
        eprintln!("ok");
        true
    } else {
        eprintln!("FAILED");
        false
    }
}

fn get_sysroot() -> PathBuf {
    let sysroot = std::env::var("MIRKAT_SYSROOT").unwrap_or_else(|_| {
        let sysroot = std::process::Command::new("rustc")
            .arg("--print")
            .arg("sysroot")
            .output()
            .expect("rustc not found")
            .stdout;
        String::from_utf8(sysroot).expect("sysroot is not utf8")
    });
    PathBuf::from(sysroot.trim())
}

fn run_prog(path: &Path) -> i32 {
    let status = Command::new("target/debug/mirkat")
                    .arg(path)
                    .status()
                    .expect("mirkat bin not found");
    status.code().unwrap()
}

//  Having tests run inside a loop like this as part of a single integration
//  test isn't ideal, but I can't find a better way yet using Rust's testing
//  framework.
#[test]
fn run_pass() {
    let paths = fs::read_dir(COMPILE_PASS_DIR).unwrap();
    let mut passed = true;

    for path in paths {
        if !test_prog(&path.unwrap().path(), STATUS_CODE_OK) {
            passed = false;
        }
    }
    assert!(passed)
}
