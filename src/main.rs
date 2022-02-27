#![feature(if_let_guard)]

mod data;
mod lexer;
mod parser;
mod eval;
mod exec;

use std::path::PathBuf;

use structopt::StructOpt;
use simplelog::*;

use crate::eval::Evaluated;

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
    let mut runner = exec::Runner::default();
    let Evaluated(v, t, src) = runner.run(args.entry)?;
    log::info!("{}", v);
    log::debug!("{:#?}", v);

    Ok(())
}
