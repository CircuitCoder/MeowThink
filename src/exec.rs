use std::{path::PathBuf, collections::{HashMap, HashSet}, ops::RangeBounds};

use crate::{data::Path, eval::{EvalCtx, Evaluated}};
use crate::{lexer::tokenize, parser::parse};

fn resolve<'a>(cur: &PathBuf, p: &Path<'a>) -> anyhow::Result<PathBuf> {
    let mut cur = cur.clone();
    match p {
        Path::Absolute(_) => {
            unimplemented!()
        },
        Path::Relative(ref segs) => {
            if !cur.pop() {
                return Err(anyhow::anyhow!("Unable to resolve: {}", p));
            }
            for seg in segs {
                match seg {
                    crate::data::RelPathSeg::Up => if !cur.pop() {
                        return Err(anyhow::anyhow!("Unable to resolve: {}", p));
                    }
                    crate::data::RelPathSeg::Down(d) => cur.push(*d),
                }
            }
        },
    }

    cur.set_extension("mtk");
    Ok(cur)
}

#[derive(Default)]
pub struct Runner {
    cache: HashMap<PathBuf, Evaluated>,
    inflights: HashSet<PathBuf>,
}

impl Runner {
    pub fn run(&mut self, file: PathBuf) -> anyhow::Result<Evaluated> {
        let file = file.canonicalize()?;

        if !self.inflights.insert(file.clone()) {
            return Err(anyhow::anyhow!("Curcular import at {}", file.display()));
        }

        let input = std::fs::read_to_string(&file)?;
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

        let mut ctx = EvalCtx::default();

        let ret = ctx.eval_top(&ast, &file, self).map_err(|e| {
            log::error!("{}", e);
            anyhow::anyhow!("Evaluation failed")
        })?;

        assert!(self.inflights.remove(&file));
        self.cache.insert(file, ret.clone());

        Ok(ret)
    }

    pub fn run_import<'a>(&mut self, cur: &PathBuf, p: &Path<'a>) -> anyhow::Result<Evaluated> {
        let p = resolve(cur, p)?;
        log::debug!("Import: {}", p.display());

        self.run(p)
    }
}