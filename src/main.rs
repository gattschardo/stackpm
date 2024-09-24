fn main() {
    println!("Hello, stackpm!");

    let p = ast::parse("[imp] claim prove id qed").unwrap();
    let q = Expr::Quote(p);
    println!("{q}");

    let i = ast::parse("imp").unwrap();
    types::check(&types::context(), i.last().unwrap());

    repl()
}

#[cfg(test)]
mod test;

fn repl() {
    let mut s = Vec::new();
    let ctx = types::context();
    loop {
        let raw = read().unwrap();
        let es = ast::parse(&raw).unwrap();
        for e in es {
            if e == Expr::Word("?".to_string()) {
                println!("{}", s.last().unwrap());
                continue;
            }
            if let Some(w) = types::check(&ctx, &e) {
                exec(&mut s, w);
            }
        }
    }
}

fn read() -> Option<String> {
    use std::io::Write;
    print!("> ");
    std::io::stdout().flush().ok()?;
    let mut r = String::new();
    let _ = std::io::stdin().read_line(&mut r).ok()?;
    Some(r)
}

fn exec(s: &mut Vec<Expr>, w: &str) {
    match w {
        "imp" => s.push(Expr::Word("A".to_string())),
        _ => todo!(),
    }
}

#[derive(Debug, PartialEq)]
enum Op {
    Help,
    And,
    Or,
    Imp,
}

#[derive(Debug, PartialEq)]
enum Expr {
    Op(Op),
    Var(String),
    Word(String),
    Quote(Vec<Expr>),
}

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Op::Help => write!(f, "?"),
            Op::And => write!(f, "∧"),
            Op::Or => write!(f, "∨"),
            Op::Imp => write!(f, "→"),
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Expr::Op(o) => write!(f, "{o}"),
            Expr::Var(v) => write!(f, "{v}"),
            Expr::Word(w) => write!(f, "{w}"),
            Expr::Quote(q) => {
                write!(f, "[")?;
                let mut it = q.iter().peekable();
                while let Some(e) = it.next() {
                    if it.peek().is_some() {
                        write!(f, "{e} ")?;
                    } else {
                        write!(f, "{e}")?;
                    }
                }
                write!(f, "]")
            }
        }
    }
}

mod types {
    use std::collections::HashMap;

    use crate::Expr;

    pub enum Typ {
        Var,
        //Claim,
        //Thm,
    }

    #[allow(dead_code)]
    pub struct WTyp {
        before: Vec<Typ>,
        after: Vec<Typ>,
    }

    pub fn context() -> HashMap<String, WTyp> {
        let mut h = HashMap::new();
        h.insert(
            "imp".to_string(),
            WTyp {
                before: vec![Typ::Var],
                after: vec![Typ::Var],
            },
        );
        h.insert(
            "id".to_string(),
            WTyp {
                before: vec![Typ::Var],
                after: vec![Typ::Var],
            },
        );
        h
    }

    pub fn check<'a>(ctx: &HashMap<String, WTyp>, e: &'a Expr) -> Option<&'a str> {
        match e {
            Expr::Op(_) => None,
            Expr::Var(_) => None,
            Expr::Word(w) => {
                assert!(ctx.get(w).is_some());
                Some(w)
            }
            Expr::Quote(_) => {
                println!("???");
                None
            }
        }
    }
}

mod ast {
    use pest_derive::Parser;

    use crate::{Expr, Op};

    type ParseError = Box<pest::error::Error<Rule>>;

    #[derive(Parser)]
    #[grammar = "spm.pest"]
    struct SPMParser;

    pub fn parse(i: &str) -> Result<Vec<Expr>, ParseError> {
        use pest::Parser;
        Ok(to_exprs(
            SPMParser::parse(Rule::program, i).map_err(Box::new)?,
        ))
    }

    fn to_op(o: &str) -> Op {
        match o {
            "?" => Op::Help,
            "→" | "->" => Op::Imp,
            "∧" | "&" => Op::And,
            "∨" | "|" => Op::Or,
            _ => unreachable!(),
        }
    }

    fn to_exprs(es: pest::iterators::Pairs<'_, Rule>) -> Vec<Expr> {
        let mut r = Vec::with_capacity(es.len());
        for e in es {
            if e.as_rule() == Rule::EOI {
                break;
            }
            r.push(match e.as_rule() {
                Rule::op => Expr::Op(to_op(e.as_str())),
                Rule::var => Expr::Var(e.as_str().to_string()),
                Rule::word => Expr::Word(e.as_str().to_string()),
                Rule::quote => Expr::Quote(to_exprs(e.into_inner())),
                Rule::program | Rule::expr | Rule::EOI | Rule::WHITESPACE => unreachable!(),
            });
        }
        r
    }
}
