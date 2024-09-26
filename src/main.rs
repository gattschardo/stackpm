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
            .expect("option not filled after or_else");
        let es = match ast::parse(&raw) {
            Ok(r) => r,
            Err(e) => {
                println!("failed to parse input: {e}");
                continue;
            }
        };
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
                Mode::Normal => match exec(&mut s, e) {
                    Some(m) => m,
                    None => {
                        println!("?");
                        n0
                    }
                },
                Mode::Proof(prop, stk, proof) => match prove(prop, stk, e, proof) {
                    None => n0,
                    Some((Mode::Normal, thm)) => {
                        match thm {
                            Some(thm) => s.push(Expr::Thm(thm)),
                            None => {} //s.push(Expr::Prop(prop)),
                        }
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
    print!("{m}: ");
    match s.len() {
        0 => println!("ε"),
        n if n <= 5 => {
            println!("{}", display_stack(s))
        }
        _ => {
            println!("... {}", display_stack(&s[s.len() - 5..]))
        }
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
        Expr::Word(w) if w == "abort" => {
            println!("aborting proof attempt");
            return Some((Mode::Normal, None));
        }
        Expr::Word(ref w) => match w.as_ref() {
            "drop" => {
                let _ = pop(&mut s)?;
                proof.push(e.clone());
            }
            "swap" => {
                let a = pop(&mut s)?;
                let b = pop(&mut s)?;
                proof.push(e.clone());
                s.push(a);
                s.push(b);
            }
            "dig2" => {
                let a = pop(&mut s)?;
                let b = pop(&mut s)?;
                let c = pop(&mut s)?;
                proof.push(e.clone());
                s.push(b);
                s.push(a);
                s.push(c);
            }
            "bury2" => {
                let a = pop(&mut s)?;
                let b = pop(&mut s)?;
                let c = pop(&mut s)?;
                proof.push(e.clone());
                s.push(a);
                s.push(c);
                s.push(b);
            }
            "and_intro" => {
                let b = pop(&mut s)?;
                let a = pop(&mut s)?;
                proof.push(e.clone());
                s.push(Term::App(Op::And, Box::new(a), Box::new(b)));
            }
            "and_elim" => {
                let (a, b) = pop_and(&mut s)?;
                proof.push(e.clone());
                s.push(a);
                s.push(b);
            }
            "imp_elim" => {
                let imp = pop_imp(&mut s)?;
                let a = pop(&mut s)?;
                let b = apply_imp(imp, a)?;
                proof.push(e.clone());
                s.push(b);
            }
            other => {
                println!("prove other word {other}");
                return None;
            }
        },
        other => {
            println!("prove {other}");
            return None;
        }
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

fn pop_and(s: &mut Vec<Term>) -> Option<(Term, Term)> {
    let o = pop(s)?;
    match o {
        Term::App(Op::And, a, b) => Some((*a, *b)),
        _ => None,
    }
}

fn pop_imp(s: &mut Vec<Term>) -> Option<Term> {
    let i = pop(s)?;
    match i {
        Term::App(Op::Imp, _, _) => Some(i),
        _ => {
            eprintln!("expected implication, found {i}");
            None
        }
    }
}

fn pop_prop(s: &mut Vec<Expr>) -> Option<Prop> {
    let p = pop(s)?;
    match p {
        Expr::Prop(pp) => Some(pp),
        e => {
            eprintln!("expected prop, found {e}");
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

fn apply_imp(imp: Term, a: Term) -> Option<Term> {
    let (arg, conc) = match imp {
        Term::App(Op::Imp, a, c) => Some((a, c)),
        _ => None,
    }?;
    if !uni(&a, &arg) {
        println!("argument does not match, expected {arg}, got {a}");
        return None;
    }
    Some(*conc)
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

fn exec(s: &mut Vec<Expr>, e: Expr) -> Option<Mode> {
    match e {
        Expr::Op(Op::Help) => unreachable!("handled above"),
        Expr::Word(w) if w == "imp" => s.push(Expr::Word("A".to_string())),
        Expr::Word(w) => match w.as_ref() {
            "term" => {
                let a = pop_quote(s)?;
                let mut ts = make_terms(a)?;
                match ts.len() {
                    1 => s.push(Expr::Term(ts.pop().expect("pop failed for vec of len() 1"))),
                    n => {
                        println!("expected single element term, found {n}");
                        return None;
                    }
                }
            }
            "claim" => {
                let a = pop_quote(s)?;
                let b = pop_quote(s)?;
                s.push(Expr::Prop(make_prop(a, b)?));
            }
            "prove" => {
                let ref p @ Prop { ref before, .. } = pop_prop(s)?;
                return Some(Mode::Proof(p.clone(), before.clone(), Vec::new()));
            }
            other => {
                println!("other word {other}");
                return None;
            }
        },
        Expr::Quote(q) => {
            //println!("pushing quote {q:?}");
            s.push(Expr::Quote(q))
        }
        _ => todo!(),
    }
    Some(Mode::Normal)
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
            other => {
                println!("cannot convert {other} to term");
                return None;
            }
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

impl Expr {
    pub fn as_prop(&self) -> Option<&Prop> {
        match self {
            Expr::Prop(p) => Some(p),
            _ => None,
        }
    }

    pub fn as_quote(&self) -> Option<&[Expr]> {
        match self {
            Expr::Quote(q) => Some(&q),
            _ => None,
        }
    }
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
