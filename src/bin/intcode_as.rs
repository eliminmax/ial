use intcode::asm::build_ast;
use std::env::args_os;
use std::fs::read_to_string;

fn main() {
    let input = read_to_string(args_os().nth(1).expect("must provide filename")).expect("must be able to read");

    match build_ast(&input) {
        Ok(lines) => {
            for line in lines {
                println!("{line}")
            }
        }
        Err(err) => eprintln!("{err:?}")
    }
}
