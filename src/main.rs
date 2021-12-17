mod data;
mod lexer;
mod parser;
mod eval;

use std::path::PathBuf;

use structopt::StructOpt;
use simplelog::*;

use crate::{lexer::tokenize, parser::parse, eval::{eval_top, Evaluated}};

#[derive(StructOpt)]
struct Args {
    /// Log level
    #[structopt(long, default_value="info")]
    log_level: log::LevelFilter,

    /// Path to the entry file
    entry: PathBuf,
}

#[paw::main]
fn main(args: Args) -> anyhow::Result<()> {
    TermLogger::init(args.log_level, Config::default(), TerminalMode::Mixed, ColorChoice::Auto)?;
    let input = std::fs::read_to_string(args.entry)?;
    let tokens = tokenize(&input);
    let mut tokens = tokens.peekable();

    let ast = match parse(&mut tokens) {
        Ok(ast) => ast,
        Err(e) => {
            log::error!("{}", e);
            return Err(anyhow::anyhow!("Parsing failed"))
        }
    };

    log::debug!("{:#?}", ast);

    let Evaluated(v, t, src) = eval_top(&ast).map_err(|e| {
        log::error!("{}", e);
        anyhow::anyhow!("Evaluation failed")
    })?;
    log::info!("{}", v);
    log::debug!("{:#?}", v);

    Ok(())
}
