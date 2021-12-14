use crate::{lexer::tokenize, parser::parse, eval::{eval_top, Evaluated}};

mod data;
mod lexer;
mod parser;
mod eval;

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let input = std::fs::read_to_string("./testcases/nat.mtk")?;
    let tokens = tokenize(&input);
    let mut tokens = tokens.peekable();

    let ast = match parse(&mut tokens) {
        Ok(ast) => ast,
        Err(e) => {
            log::error!("{:?}", e);
            return Err(anyhow::anyhow!("Parsing failed"))
        }
    };

    log::debug!("{:#?}", ast);

    let Evaluated(v, t, src) = eval_top(&ast).map_err(|e| {
        log::error!("{:?}", e);
        anyhow::anyhow!("Evaluation failed")
    })?;
    log::info!("{}", v);
    log::debug!("{:#?}", v);

    Ok(())
}
