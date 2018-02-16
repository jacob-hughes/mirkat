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
use std::process::{Stdio, Command, Output};

const STATUS_CODE_OK: i32 = 0;
const COMPILE_PASS_DIR: &str = "./tests/compile_pass";
const MIRKAT_BIN: &str = "target/debug/mirkat";

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

/// Invokes Mirkat when given a path to a valid Rust program. Compares the
/// expected return code against that returned from Mirkat. This is surprisingly
/// effective at catching bugs in Mirkat. It's not uncommon that when things go
/// wrong, Mirkat blows up catastrophically.
fn test_prog(path: &Path, expected_code: i32) -> Result<(), Vec<u8>> {
    let out = run_prog(path);

    if out.status.code().unwrap() == expected_code {
        Ok(())
    } else {
        Err(out.stderr)
    }
}

/// If a test fails, we want to display the stderr from running it. If we don't
/// handle this nicely though, it's hard to see the wood for the trees.
fn fmt_err(test_name: &str, stderr: &Vec<u8>) {
    eprintln!("=== {:?} error: ===", test_name);
    eprintln!("");
    let error = std::str::from_utf8(stderr)
        .expect("Error reading stderr from test into UTF-8 string");
    eprintln!("{}", error)
}

fn run_prog(path: &Path) -> Output {
    let child = Command::new(MIRKAT_BIN.to_string())
                .arg(path)
                .stderr(Stdio::piped())
                .spawn()
                .unwrap();
    child.wait_with_output().unwrap()
}

//  Having tests run inside a loop like this as part of a single integration
//  test isn't ideal, but I can't find a better way yet using Rust's testing
//  framework.
#[test]
fn run_pass() {
    let entries = fs::read_dir(COMPILE_PASS_DIR).unwrap();
    let mut errors: Vec<(String, Vec<u8>)> = vec![];
    for entry in entries {
        if let Ok(entry) = entry {
            let path = entry.path();
            let test_name = path.file_name()
                                .unwrap()
                                .to_str()
                                .unwrap()
                                .to_string();
            eprint!("test {:?} ... ", &test_name);
            match test_prog(&path, STATUS_CODE_OK) {
                Ok(_) => eprintln!("ok"),
                Err(stderr) => {
                    eprintln!("FAIL");
                    errors.push((test_name, stderr))
                }
            }
        }
    }

    eprintln!();
    for &(ref name, ref stderr) in errors.iter() {
        fmt_err(name, stderr)
    }
    assert_eq!(errors.len(), 0);
}
