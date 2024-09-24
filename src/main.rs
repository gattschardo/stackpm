fn main() {
    println!("Hello, stackpm!");

    let p = ast::parse("[imp] claim prove id qed").unwrap();
    let q = Expr::Quote(p);
    println!("{q}");
}

#[derive(Debug)]
enum Expr {
    Word(String),
    Quote(Vec<Expr>),
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
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

mod ast {
    use pest_derive::Parser;

    use crate::Expr;

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

    fn to_exprs(es: pest::iterators::Pairs<'_, Rule>) -> Vec<Expr> {
        let mut r = Vec::with_capacity(es.len());
        for e in es {
            if e.as_rule() == Rule::EOI {
                break;
            }
            r.push(match e.as_rule() {
                Rule::word => Expr::Word(e.as_str().to_string()),
                Rule::quote => Expr::Quote(to_exprs(e.into_inner())),
                Rule::program | Rule::expr | Rule::EOI | Rule::WHITESPACE => unreachable!(),
            });
        }
        r
    }
}
