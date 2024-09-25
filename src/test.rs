fn eval(i: &str) -> crate::Expr {
    use crate::{ast, exec};

    let es = ast::parse(i).unwrap();
    let mut s = Vec::new();
    for e in es {
        let _ = exec(&mut s, e);
    }
    assert_eq!(s.len(), 1);
    let t = s.pop().unwrap();
    println!("{t}");
    t
}

#[test]
fn term() {
    let t = eval("[A B & C | D ->] term");
    println!("{t}");
    assert_eq!("((A ∧ B) ∨ C) → D", format!("{t}"));
}

#[test]
fn session1() {
    for (task, prop) in [
        ("[A] [A] claim", "prop: A -- A"),
        ("[A B] [A] claim", "prop: A B -- A"),
        ("[A B] [B A] claim", "prop: A B -- B A"),
        ("[A B] [A B &] claim", "prop: A B -- A ∧ B"),
        ("[A A] [A A &] claim", "prop: A A -- A ∧ A"),
        ("[A B &] [A] claim", "prop: A ∧ B -- A"),
        ("[A B &] [A B] claim", "prop: A ∧ B -- A B"),
        ("[A B &] [A B &] claim", "prop: A ∧ B -- A ∧ B"),
        ("[A B ∧] [B A &] claim", "prop: A ∧ B -- B ∧ A"),
        ("[A B & C &] [A B C] claim", "prop: (A ∧ B) ∧ C -- A B C"),
        ("[A B & C &] [A C &] claim", "prop: (A ∧ B) ∧ C -- A ∧ C"),
        (
            "[A B & C &] [A B C & &] claim",
            "prop: (A ∧ B) ∧ C -- A ∧ (B ∧ C)",
        ),
    ] {
        let p = eval(task);
        println!("{p}");
        assert_eq!(prop, format!("{p}"));
    }
}
