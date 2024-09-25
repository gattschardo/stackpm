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

#[derive(Debug, Clone)]
#[allow(dead_code)]
enum Mode {
    Normal,
    Proof(Prop, Vec<Term>, Vec<Expr>),
}

fn repl() {
    let mut s = Vec::new();
    let mut m = Mode::Normal;
    //let ctx = types::context();
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
            if is_help(&e) {
                match &m {
                    Mode::Normal => help("toplevel", &s),
                    Mode::Proof(prop, stk, _) => help(&format!("proving {prop}"), &stk),
                }
                continue;
            }
            let n0 = m.clone();
            m = match m {
                Mode::Normal => exec(&mut s, e),
                Mode::Proof(prop, stk, proof) => match prove(prop, stk, e, proof) {
                    None => n0,
                    Some((Mode::Normal, thm)) => {
                        s.push(Expr::Thm(thm.unwrap()));
                        Mode::Normal
                    }
                    Some((p, _)) => p,
                },
            };
        }
    }
}

fn is_help(e: &Expr) -> bool {
    match e {
        Expr::Op(Op::Help) => true,
        _ => false,
    }
}

fn help<T>(m: &str, s: &[T])
where
    T: std::fmt::Display,
{
    match s.last() {
        Some(v) => println!("{m}: {v}"),
        None => println!("{m}: ε"),
    }
}

fn prove(
    prop: Prop,
    mut s: Vec<Term>,
    e: Expr,
    mut proof: Vec<Expr>,
) -> Option<(Mode, Option<Theorem>)> {
    match e {
        Expr::Word(w) if w == "qed" => {
            if !unify(&s, &prop.after) {
                println!(
                    "proof not finished, expected {}, have {}",
                    display_stack(&prop.after),
                    display_stack(&s)
                );
                return None;
            }
            return Some((Mode::Normal, Some(make_theorem(prop.clone(), proof))));
        }
        Expr::Word(ref w) => match w.as_ref() {
            "swap" => {
                let a = pop(&mut s)?;
                let b = pop(&mut s)?;
                proof.push(e.clone());
                s.push(a);
                s.push(b);
            }
            "drop" => {
                let _ = pop(&mut s)?;
                proof.push(e.clone());
            }
            "and_intro" => {
                let b = pop(&mut s)?;
                let a = pop(&mut s)?;
                proof.push(e.clone());
                s.push(Term::App(Op::And, Box::new(a), Box::new(b)));
            }
            other => todo!("prove other word {other}"),
        },
        other => todo!("prove {other}"),
    }
    Some((Mode::Proof(prop, s, proof), None))
}

#[derive(Debug, Clone)]
struct Theorem {
    prop: Prop,
    proof: Vec<Expr>,
}

fn make_theorem(prop: Prop, proof: Vec<Expr>) -> Theorem {
    Theorem { prop, proof }
}

fn unify(a: &[Term], b: &[Term]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    for (ta, tb) in std::iter::zip(a, b) {
        if !uni(ta, tb) {
            return false;
        }
    }
    true
}

fn uni(a: &Term, b: &Term) -> bool {
    match (a, b) {
        (Term::Var(va), Term::Var(vb)) if va == vb => {
            // ok
        }
        (Term::App(o1, a1, b1), Term::App(o2, a2, b2))
            if o1 == o2 && uni(&*a1, &*a2) && uni(&*b1, &*b2) =>
        {
            // ok
        }
        _ => {
            return false;
        }
    }
    true
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

fn pop<T>(s: &mut Vec<T>) -> Option<T> {
    if s.is_empty() {
        eprintln!("expected value, found empty stack");
    }
    s.pop()
}

fn pop_prop(s: &mut Vec<Expr>) -> Option<Prop> {
    let p = pop(s)?;
    match p {
        Expr::Prop(pp) => Some(pp),
        e => {
            eprintln!("expected quote, found {e}");
            None
        }
    }
}

fn pop_quote(s: &mut Vec<Expr>) -> Option<Vec<Expr>> {
    let q = pop(s)?;
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
    before: Vec<Term>,
    after: Vec<Term>,
}

fn make_prop(a: Vec<Expr>, b: Vec<Expr>) -> Option<Prop> {
    Some(Prop {
        before: make_terms(b)?,
        after: make_terms(a)?,
    })
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
        Expr::Word(w) => match w.as_ref() {
            "term" => {
                let a = pop_quote(s).unwrap();
                let mut ts = make_terms(a).unwrap();
                assert_eq!(ts.len(), 1);
                s.push(Expr::Term(ts.pop().unwrap()));
            }
            "claim" => {
                let a = pop_quote(s).unwrap();
                let b = pop_quote(s).unwrap();
                s.push(Expr::Prop(make_prop(a, b).unwrap()));
            }
            "prove" => {
                let ref p @ Prop { ref before, .. } = pop_prop(s).unwrap();
                return Mode::Proof(p.clone(), before.clone(), Vec::new());
            }
            other => todo!("other word {other}"),
        },
        Expr::Quote(q) => {
            //println!("pushing quote {q:?}");
            s.push(Expr::Quote(q))
        }
        _ => todo!(),
    }
    Mode::Normal
}

fn render(e: &Term) -> String {
    match e {
        Term::Var(v) => v.clone(),
        a @ Term::App(_, _, _) => format!("({a})"),
    }
}

fn make_terms(mut p: Vec<Expr>) -> Option<Vec<Term>> {
    let mut s = Vec::new();
    while let Some(e) = p.pop() {
        match e {
            Expr::Var(v) => s.push(Term::Var(v)),
            Expr::Op(o) => {
                let b = Box::new(s.pop()?);
                let a = Box::new(s.pop()?);
                s.push(Term::App(o, a, b));
            }
            _ => todo!(),
        }
    }
    Some(s)
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Op {
    Help,
    And,
    Or,
    Imp,
}

#[derive(Debug, Clone)]
enum Term {
    Var(String),
    App(Op, Box<Term>, Box<Term>),
}

#[derive(Debug, Clone)]
enum Expr {
    Op(Op),
    Var(String),
    Word(String),
    Quote(Vec<Expr>),
    Term(Term),
    Prop(Prop),
    Thm(Theorem),
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

fn display_stack<T>(v: &[T]) -> String
where
    T: std::fmt::Display,
{
    let mut s = String::new();
    let mut it = v.iter().peekable();
    while let Some(e) = it.next() {
        if it.peek().is_some() {
            s.push_str(&format!("{e} "));
        } else {
            s.push_str(&format!("{e}"));
        }
    }
    s
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Term::App(o, a, b) => write!(f, "{} {o} {}", render(&*a), render(&*b)),
            Term::Var(v) => write!(f, "{v}"),
        }
    }
}

impl std::fmt::Display for Prop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let Prop { before, after } = self;
        write!(f, "{} -- {}", display_stack(before), display_stack(after))
    }
}

impl std::fmt::Display for Theorem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let Theorem { prop, proof } = self;
        write!(f, "theorem {prop}: {}.", display_stack(proof))
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Expr::Op(o) => write!(f, "{o}"),
            Expr::Var(v) => write!(f, "{v}"),
            Expr::Word(w) => write!(f, "{w}"),
            Expr::Term(t) => write!(f, "{}", *t),
            Expr::Quote(q) => write!(f, "[{}]", display_stack(q)),
            Expr::Prop(c) => write!(f, "prop: {c}"),
            Expr::Thm(t) => write!(f, "{t}"),
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
            Expr::Term(_) => None,
            Expr::Var(_) => None,
            Expr::Word(w) => {
                assert!(ctx.get(w).is_some());
                Some(w)
            }
            Expr::Quote(_) => None,
            Expr::Prop(_) => None,
            Expr::Thm(_) => None,
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
