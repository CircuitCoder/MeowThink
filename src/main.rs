use crate::{lexer::tokenize, parser::parse};

mod lexer;
mod parser;

fn main() -> anyhow::Result<()> {
    let input = std::fs::read_to_string("./testcases/even.mtk")?;
    let tokens = tokenize(&input);
    let mut tokens = tokens.peekable();

    let ast = match parse(&mut tokens) {
        Ok(ast) => ast,
        Err(e) => {
            println!("{:?}", e);
            return Err(anyhow::anyhow!("Parsing failed"));
        }
    };

    println!("{:#?}", ast);

    Ok(())
}
