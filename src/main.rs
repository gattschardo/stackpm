fn main() {
    println!("Hello, stackpm!");

    let p = ast::parse("[imp] claim");
    println!("{p:?}");
    show(&mut p.unwrap());
}

fn show(es: &mut pest::iterators::Pairs<'_, ast::Rule>) {
    for e in es {
        for x in e.into_inner() {
            println!("rule {:?}: {}", x.as_rule(), x.as_str());
        }
    }
}

mod ast {
    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "spm.pest"]
    struct SPMParser;

    pub fn parse(i: &str) -> Result<pest::iterators::Pairs<'_, Rule>, pest::error::Error<Rule>> {
        use pest::Parser;
        SPMParser::parse(Rule::program, i)
    }
}
