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

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
enum Mode {
    Normal,
    Proof,
}

fn repl() {
    let mut s = Vec::new();
    let mut m = Mode::Normal;
    let ctx = types::context();
    let mut run = true;
    while run {
        let raw = read()
            .or_else(|| {
                run = false;
                Some("".to_string())
            })
            .unwrap();
        let es = ast::parse(&raw).unwrap();
        for e in es {
            match e {
                Expr::Op(Op::Help) => {
                    println!("{}", s.last().unwrap());
                    continue;
                }
                _ => {}
            }
            m = match m {
                Mode::Normal => {
                    let m = exec(&mut s, e);
                    //println!("stack len is {}", s.len());
                    m
                }
                Mode::Proof => {
                    if let Some(w) = types::check(&ctx, &e) {
                        println!("known type {w}");
                    }
                    todo!()
                }
            };
        }
    }
}

fn read() -> Option<String> {
    use std::io::Write;
    print!("> ");
    std::io::stdout().flush().ok()?;
    let mut r = String::new();
    let n = std::io::stdin().read_line(&mut r).ok()?;
    if n == 0 {
        return None;
    }
    Some(r)
}

fn pop_quote(s: &mut Vec<Expr>) -> Option<Vec<Expr>> {
    if s.is_empty() {
        eprintln!("expected quote, found empty stack");
    }
    let q = s.pop()?;
    match q {
        Expr::Quote(qq) => Some(qq.into_iter().rev().collect()),
        e => {
            eprintln!("expected quote, found {e}");
            None
        }
    }
}

#[derive(Debug, Clone)]
struct Prop {
    before: Vec<Expr>,
    after: Vec<Expr>,
}

impl std::fmt::Display for Prop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let Prop { before, after } = self;
        write!(
            f,
            "prop: {} -- {}",
            eval_prop(before.clone()).unwrap(),
            eval_prop(after.clone()).unwrap()
        )
    }
}

fn make_prop(a: Vec<Expr>, b: Vec<Expr>) -> Prop {
    let c = Prop {
        before: b,
        after: a,
    };
    //println!("{c}");
    c
}

fn exec(s: &mut Vec<Expr>, e: Expr) -> Mode {
    match e {
        Expr::Op(Op::Help) => {
            for w in s.iter().take(4) {
                print!("{w} ");
            }
            println!();
        }
        Expr::Word(w) if w == "imp" => s.push(Expr::Word("A".to_string())),
        Expr::Word(w) if w == "claim" => {
            let a = pop_quote(s).unwrap();
            let b = pop_quote(s).unwrap();
            s.push(Expr::Prop(make_prop(a, b)));
        }
        Expr::Quote(q) => {
            //println!("pushing quote {q:?}");
            s.push(Expr::Quote(q))
        }
        _ => todo!(),
    }
    Mode::Normal
}

fn render(e: Expr) -> String {
    match e {
        Expr::Var(v) => v,
        Expr::Word(w) => format!("({w})"),
        _ => unimplemented!(),
    }
}

fn eval_prop(mut p: Vec<Expr>) -> Option<String> {
    let mut s = Vec::new();
    while let Some(e) = p.pop() {
        match e {
            v @ Expr::Var(_) => s.push(v),
            Expr::Op(o) => {
                //eprintln!("at op {o}");
                let b = render(s.pop()?);
                //eprintln!("first arg: {a}");
                let a = render(s.pop()?);
                //eprintln!("snd arg: {b}");
                s.push(Expr::Word(format!("{a} {o} {b}")))
            }
            _ => todo!(),
        }
    }
    Some(format!("{}", Expr::Quote(s)))
}

#[derive(Debug, Clone, Copy)]
enum Op {
    Help,
    And,
    Or,
    Imp,
}

#[derive(Debug, Clone)]
enum Expr {
    Op(Op),
    Var(String),
    Word(String),
    Quote(Vec<Expr>),
    Prop(Prop),
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
            Expr::Prop(c) => write!(f, "{c}"),
        }
    }
}

mod types {
    use std::collections::HashMap;

    use crate::Expr;

    pub enum Typ {
        Var,
        //Prop,
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
            Expr::Quote(_) => None,
            Expr::Prop(_) => None,
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
