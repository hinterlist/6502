mod lib;

use crate::lib::{Cpu, Mem, RESET_VEC};

fn main() {
    println!("Please private path to you program:");
    let mut file_path = String::new();
    std::io::stdin()
        .read_line(&mut file_path)
        .expect("Failed to read file path");

    let file_path = file_path.trim();

    let file_content = std::fs::read_to_string(file_path).expect("Failed to read file content");

    println!(
        "Read {bytes} from {path}",
        bytes = file_content.as_bytes().len(),
        path = file_path
    );

    let mut mem = Mem::new();
    mem.init();

    let mut pc = RESET_VEC;
    for b in file_content.as_bytes() {}
}
