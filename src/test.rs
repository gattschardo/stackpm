#[test]
fn session1() {
    use crate::{ast, Expr};

    for task in [
        "[A] [A] claim",
        "[A B] [A] claim",
        "[A B] [B A] claim",
        "[A B] [A B &] claim",
        "[A A] [A A &] claim",
        "[A B &] [A] claim",
        "[A B &] [A B] claim",
        "[A B &] [A B &] claim",
        "[A B ∧] [B A &] claim",
        "[A B & C &] [A B C] claim",
        "[A B & C &] [A C &] claim",
        "[A B & C &] [A B C & &] claim",
    ] {
        let e = ast::parse(task);
        //println!("{e:?}");
        assert!(e.is_ok());
        let q = Expr::Quote(e.unwrap());
        println!("{q}");
    }
}
