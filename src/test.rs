#[test]
fn session1() {
    use crate::{ast, exec};

    for (task, prop) in [
        ("[A] [A] claim", "prop: [A] -- [A]"),
        ("[A B] [A] claim", "prop: [A B] -- [A]"),
        ("[A B] [B A] claim", "prop: [A B] -- [B A]"),
        ("[A B] [A B &] claim", "prop: [A B] -- [A ∧ B]"),
        ("[A A] [A A &] claim", "prop: [A A] -- [A ∧ A]"),
        ("[A B &] [A] claim", "prop: [A ∧ B] -- [A]"),
        ("[A B &] [A B] claim", "prop: [A ∧ B] -- [A B]"),
        ("[A B &] [A B &] claim", "prop: [A ∧ B] -- [A ∧ B]"),
        ("[A B ∧] [B A &] claim", "prop: [A ∧ B] -- [B ∧ A]"),
        (
            "[A B & C &] [A B C] claim",
            "prop: [(A ∧ B) ∧ C] -- [A B C]",
        ),
        (
            "[A B & C &] [A C &] claim",
            "prop: [(A ∧ B) ∧ C] -- [A ∧ C]",
        ),
        (
            "[A B & C &] [A B C & &] claim",
            "prop: [(A ∧ B) ∧ C] -- [A ∧ (B ∧ C)]",
        ),
    ] {
        let es = ast::parse(task);
        //println!("{e:?}");
        assert!(es.is_ok());
        let mut s = Vec::new();
        for e in es.unwrap() {
            let _ = exec(&mut s, e);
        }
        assert_eq!(s.len(), 1);
        let p = s.pop().unwrap();
        println!("{p}");
        assert_eq!(prop, format!("{p}"));
    }
}
