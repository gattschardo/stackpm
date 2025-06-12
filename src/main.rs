fn main() {
    println!("Hello, stackpm!");

    repl()
}

#[cfg(test)]
mod test;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Const {
    Bottom,
    Top,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum HelpMode {
    Status,
    Commands,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Op {
    Help(HelpMode),
    And,
    Or,
    Imp,
}

#[derive(Debug, Clone)]
pub enum Term {
    Const(Const),
    Var(String),
    App(Op, Box<Term>, Box<Term>),
}

#[derive(Debug, Clone)]
pub struct Prop {
    before: Vec<Term>,
    after: Vec<Term>,
}

#[derive(Debug, Clone)]
pub struct Theorem {
    prop: Prop,
    proof: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Const(Const),
    Op(Op),
    Var(String),
    Word(String),
    Quote(Vec<Expr>),
    Term(Term),
    Prop(Prop),
    Thm(Theorem),
}

#[derive(Debug, Clone)]
struct ProofCtx {
    prop: Prop,
    stk: Vec<Term>,
    proof: Vec<Expr>,
    estk: Vec<Expr>,
}

#[derive(Debug, Clone)]
enum Mode {
    Normal,
    Proof(ProofCtx),
}

fn init_proof(prop: Prop) -> ProofCtx {
    let Prop { ref before, .. } = prop;
    ProofCtx {
        prop: prop.clone(),
        stk: before.clone(),
        proof: Vec::new(),
        estk: Vec::new(),
    }
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
                    Mode::Proof(ProofCtx { prop, stk, .. }) => {
                        help(&format!("proving {prop}"), &stk)
                    }
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
                Mode::Proof(ctx) => {
                    match prove(ctx, e) {
                        None => n0,
                        Some((Mode::Normal, thm)) => {
                            match thm {
                                Some(thm) => s.push(Expr::Thm(thm)),
                                None => {} //s.push(Expr::Prop(prop)),
                            }
                            Mode::Normal
                        }
                        Some((p, _)) => p,
                    }
                }
            };
        }
    }
}

fn is_help(e: &Expr) -> bool {
    match e {
        Expr::Op(Op::Help(_)) => true,
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

fn prove(ctx: ProofCtx, e: Expr) -> Option<(Mode, Option<Theorem>)> {
    let ProofCtx {
        prop,
        mut stk,
        mut proof,
        mut estk,
    } = ctx;
    match e {
        Expr::Word(w) if w == "qed" => {
            if !unify(&stk, &prop.after) {
                println!(
                    "proof not finished, expected {}, have {}",
                    display_stack(&prop.after),
                    display_stack(&stk)
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
            "dup" => {
                let a = pop(&mut stk)?;
                stk.push(a.clone());
                stk.push(a);
                proof.push(e.clone());
            }
            "drop" => {
                let _ = pop(&mut stk)?;
                proof.push(e.clone());
            }
            "swap" => {
                let a = pop(&mut stk)?;
                let b = pop(&mut stk)?;
                proof.push(e.clone());
                stk.push(a);
                stk.push(b);
            }
            "dig2" => {
                let a = pop(&mut stk)?;
                let b = pop(&mut stk)?;
                let c = pop(&mut stk)?;
                proof.push(e.clone());
                stk.push(b);
                stk.push(a);
                stk.push(c);
            }
            "bury2" => {
                let a = pop(&mut stk)?;
                let b = pop(&mut stk)?;
                let c = pop(&mut stk)?;
                proof.push(e.clone());
                stk.push(a);
                stk.push(c);
                stk.push(b);
            }
            "and_intro" => {
                let b = pop(&mut stk)?;
                let a = pop(&mut stk)?;
                proof.push(e.clone());
                stk.push(Term::App(Op::And, Box::new(a), Box::new(b)));
            }
            "and_elim" => {
                let (a, b) = pop_and(&mut stk)?;
                proof.push(e.clone());
                stk.push(a);
                stk.push(b);
            }
            "imp_intro" => {
                let arg_q = pop_quote(&mut estk)?;
                let arg_term = make_term(arg_q.clone())?;
                let pf_q = pop_quote(&mut estk)?;
                let mut inner_stk = stk.clone();
                inner_stk.push(arg_term.clone());
                let ret_term = prove_sub(
                    "imp_intro",
                    ProofCtx {
                        prop: dummy_prop(),
                        stk: inner_stk,
                        proof: Vec::new(),
                        estk: Vec::new(),
                    },
                    &pf_q.clone().into_iter().rev().collect::<Vec<_>>(),
                )?;
                stk.push(Term::App(Op::Imp, Box::new(arg_term), Box::new(ret_term)));
                proof.push(Expr::Quote(pf_q.into_iter().rev().collect()));
                proof.push(Expr::Quote(arg_q.into_iter().rev().collect()));
                proof.push(e);
            }
            "imp_elim" => {
                let imp = pop_imp(&mut stk)?;
                let a = pop(&mut stk)?;
                let b = apply_imp(imp, a)?;
                proof.push(e.clone());
                stk.push(b);
            }
            "or1_intro" => {
                let oq = pop_quote(&mut estk)?;
                let o = make_term(oq.clone())?;
                let a = pop(&mut stk)?;
                let b = apply_or(o, a.clone(), true)?;
                proof.push(Expr::Quote(oq.into_iter().rev().collect()));
                proof.push(e);
                stk.push(Term::App(Op::Or, Box::new(a), Box::new(b)));
            }
            "or2_intro" => {
                let oq = pop_quote(&mut estk)?;
                let o = make_term(oq.clone())?;
                let b = pop(&mut stk)?;
                let a = apply_or(o, b.clone(), false)?;
                proof.push(Expr::Quote(oq.into_iter().rev().collect()));
                proof.push(e);
                stk.push(Term::App(Op::Or, Box::new(a), Box::new(b)));
            }
            "or_elim" => {
                let or = pop_or(&mut stk)?;
                let (a, b) = dest_or(or)?;
                let bq = pop_quote(&mut estk)?;
                let aq = pop_quote(&mut estk)?;
                let mut astk = stk.clone();
                astk.push(a);
                let a_ret = prove_sub(
                    "or_elim (1)",
                    ProofCtx {
                        prop: dummy_prop(),
                        stk: astk,
                        proof: Vec::new(),
                        estk: Vec::new(),
                    },
                    &aq.clone().into_iter().rev().collect::<Vec<_>>(),
                )?;
                let mut bstk = stk.clone();
                bstk.push(b);
                let b_ret = prove_sub(
                    "or_elim (2)",
                    ProofCtx {
                        prop: dummy_prop(),
                        stk: bstk,
                        proof: Vec::new(),
                        estk: Vec::new(),
                    },
                    &bq.clone().into_iter().rev().collect::<Vec<_>>(),
                )?;
                if !uni(&a_ret, &b_ret) {
                    println!("or branch conclusions do not match: {a_ret}, {b_ret}");
                    return None;
                }
                stk.push(a_ret);
                proof.push(Expr::Quote(aq.into_iter().rev().collect()));
                proof.push(Expr::Quote(bq.into_iter().rev().collect()));
                proof.push(e);
            }
            // bottom_elim: ex falso quod libet
            "efql" => {
                let _bot = pop_bottom(&mut stk)?;
                let ret_q = pop_quote(&mut estk)?;
                let ret_t = make_term(ret_q.clone())?;
                proof.push(Expr::Quote(ret_q.into_iter().rev().collect()));
                proof.push(e);
                stk.push(ret_t);
            }
            // case analysis: tertium non datur
            "cases" => {
                let a_q = pop_quote(&mut estk)?;
                let a_t = make_term(a_q.clone())?;
                proof.push(Expr::Quote(a_q.into_iter().rev().collect()));
                proof.push(e);
                stk.push(Term::App(
                    Op::Or,
                    Box::new(a_t.clone()),
                    Box::new(Term::App(
                        Op::Imp,
                        Box::new(a_t.clone()),
                        Box::new(Term::Const(Const::Bottom)),
                    )),
                ));
            }
            other => {
                println!("prove other word {other}");
                return None;
            }
        },
        expr @ Expr::Quote(_) => {
            estk.push(expr);
        }
        other => {
            println!("prove {other}");
            return None;
        }
    }
    Some((
        Mode::Proof(ProofCtx {
            prop,
            stk,
            proof,
            estk,
        }),
        None,
    ))
}

fn prove_sub(lbl: &str, mut ctx: ProofCtx, pf: &[Expr]) -> Option<Term> {
    println!("starting sub-proof with stack {}", display_stack(&ctx.stk));
    for e in pf {
        println!("running inner: {e:?}");
        let ctx1 = match prove(ctx, e.clone()) {
            None => {
                println!("failed in sub-proof {}.", display_stack(pf));
                return None;
            }
            Some((Mode::Proof(ctx1), None)) => {
                println!("after: {}", display_stack(&ctx1.stk));
                ctx1
            }
            _ => {
                unreachable!("cannot finish/abort proof inside imp_intro?");
            }
        };
        ctx = ctx1;
    }
    if ctx.stk.len() != 1 {
        println!("stack length after {lbl}: {}, expected 1", ctx.stk.len());
        return None;
    }
    Some(ctx.stk.pop().expect("pop of vec with length 1 failed?"))
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
        (Term::Const(ca), Term::Const(cb)) if ca == cb => {
            // ok
        }
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
        _ => {
            eprintln!("expected and, found {o}");
            None
        }
    }
}

fn pop_or(s: &mut Vec<Term>) -> Option<Term> {
    let o = pop(s)?;
    match o {
        Term::App(Op::Or, _, _) => Some(o),
        _ => {
            eprintln!("expected or, found {o}");
            None
        }
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

fn pop_bottom(s: &mut Vec<Term>) -> Option<Term> {
    let b = pop(s)?;
    match b {
        Term::Const(Const::Bottom) => Some(b),
        _ => {
            eprintln!("expected bottom (⊥), found {b}");
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

fn apply_or(or: Term, a: Term, left: bool) -> Option<Term> {
    let (oa, ob) = dest_or(or)?;
    if left {
        if !uni(&oa, &a) {
            println!("argument does not match, expected {oa}, got {a}");
            return None;
        }
        Some(ob)
    } else {
        if !uni(&ob, &a) {
            println!("argument does not match, expected {ob}, got {a}");
            return None;
        }
        Some(oa)
    }
}

fn dest_or(or: Term) -> Option<(Term, Term)> {
    match or {
        Term::App(Op::Or, a, b) => Some((*a, *b)),
        _ => None,
    }
}

fn make_prop(a: Vec<Expr>, b: Vec<Expr>) -> Option<Prop> {
    Some(Prop {
        before: make_terms(b)?,
        after: make_terms(a)?,
    })
}

fn dummy_prop() -> Prop {
    Prop {
        before: Vec::new(),
        after: Vec::new(),
    }
}

fn exec(s: &mut Vec<Expr>, e: Expr) -> Option<Mode> {
    match e {
        Expr::Op(Op::Help(_)) => unreachable!("handled above"),
        Expr::Word(w) if w == "imp" => s.push(Expr::Word("A".to_string())),
        Expr::Word(w) => match w.as_ref() {
            "term" => {
                let q = pop_quote(s)?;
                s.push(Expr::Term(make_term(q)?));
            }
            "claim" => {
                let a = pop_quote(s)?;
                let b = pop_quote(s)?;
                s.push(Expr::Prop(make_prop(a, b)?));
            }
            "prove" => {
                return Some(Mode::Proof(init_proof(pop_prop(s)?)));
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
        Term::Const(c) => format!("{c}"),
        Term::Var(v) => v.clone(),
        a @ Term::App(_, _, _) => format!("({a})"),
    }
}

fn make_terms(mut p: Vec<Expr>) -> Option<Vec<Term>> {
    let mut s = Vec::new();
    while let Some(e) = p.pop() {
        match e {
            Expr::Const(c) => s.push(Term::Const(c)),
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

fn make_term(p: Vec<Expr>) -> Option<Term> {
    let mut ts = make_terms(p)?;
    match ts.len() {
        1 => Some(ts.pop().expect("pop failed for vec of len() 1")),
        n => {
            println!("expected single element term, found {n}");
            None
        }
    }
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

impl std::fmt::Display for Const {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Const::Bottom => write!(f, "⊥"),
            Const::Top => write!(f, "⊤"),
        }
    }
}

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Op::Help(HelpMode::Status) => write!(f, "?"),
            Op::Help(HelpMode::Commands) => write!(f, "!"),
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
            Term::Const(c) => write!(f, "{c}"),
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
            Expr::Const(c) => write!(f, "{c}"),
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

// unfinished
#[allow(dead_code)]
mod types {
    use std::collections::HashMap;

    use crate::Expr;

    pub enum Typ {
        Var,
        //Prop,
        //Thm,
    }

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
            Expr::Const(_) => None,
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

    use crate::{Const, Expr, HelpMode, Op};

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

    fn to_const(c: &str) -> Const {
        match c {
            "⊥" => Const::Bottom,
            "⊤" => Const::Top,
            _ => unreachable!("missing const {c}"),
        }
    }

    fn to_op(o: &str) -> Op {
        match o {
            "?" => Op::Help(HelpMode::Status),
            "!" => Op::Help(HelpMode::Commands),
            "→" | "->" => Op::Imp,
            "∧" | "&" => Op::And,
            "∨" | "|" => Op::Or,
            _ => unreachable!("missing op {o}"),
        }
    }

    fn to_exprs(es: pest::iterators::Pairs<'_, Rule>) -> Vec<Expr> {
        let mut r = Vec::with_capacity(es.len());
        for e in es {
            if e.as_rule() == Rule::EOI {
                break;
            }
            r.push(match e.as_rule() {
                Rule::constant => Expr::Const(to_const(e.as_str())),
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
