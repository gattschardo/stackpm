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

fn check_proof(task: &str, prop: &str, proof: &str) {
    use crate::{ast::parse, display_stack, prove, Expr, Mode, Prop};
    let p = eval(task);
    println!("{p}");
    assert_eq!(prop, format!("{p}"));
    let Prop { before, .. } = p.as_prop().unwrap();
    let mut stk = before.clone();
    let mut pf = Vec::new();
    let mut v = parse(proof)
        .unwrap()
        .pop()
        .unwrap()
        .as_quote()
        .unwrap()
        .to_vec();
    let v0 = v.clone();
    v.push(Expr::Word("qed".to_string()));
    println!("trying proof: {}", display_stack(&v));
    let mut done = false;
    for e in v {
        let (stk1, pf1) = match prove(p.as_prop().unwrap().clone(), stk, e, pf) {
            Some((Mode::Proof(_p, stk1, pf1), _)) => (stk1, pf1),
            Some((Mode::Normal, thm)) => {
                assert_eq!(display_stack(&thm.unwrap().proof), display_stack(&v0));
                done = true;
                break;
            }
            _ => {
                assert!(false);
                return;
            }
        };
        stk = stk1;
        pf = pf1;
    }
    assert!(done);
}

#[test]
fn term() {
    let t = eval("[A B & C | D ->] term");
    println!("{t}");
    assert_eq!("((A ∧ B) ∨ C) → D", format!("{t}"));
}

#[test]
fn session1_and() {
    for (task, prop, proof) in [
        ("[A] [A] claim", "prop: A -- A", "[]"),
        ("[A B] [A] claim", "prop: A B -- A", "[drop]"),
        ("[A B] [B A] claim", "prop: A B -- B A", "[swap]"),
        ("[A B] [A B &] claim", "prop: A B -- A ∧ B", "[and_intro]"),
        ("[A A] [A A &] claim", "prop: A A -- A ∧ A", "[and_intro]"),
        ("[A B &] [A] claim", "prop: A ∧ B -- A", "[and_elim drop]"),
        ("[A B &] [A B] claim", "prop: A ∧ B -- A B", "[and_elim]"),
        ("[A B &] [A B &] claim", "prop: A ∧ B -- A ∧ B", "[]"),
        (
            "[A B ∧] [B A &] claim",
            "prop: A ∧ B -- B ∧ A",
            "[and_elim swap and_intro]",
        ),
        (
            "[A B & C &] [A B C] claim",
            "prop: (A ∧ B) ∧ C -- A B C",
            "[and_elim swap and_elim dig2]",
        ),
        (
            "[A B & C &] [A C &] claim",
            "prop: (A ∧ B) ∧ C -- A ∧ C",
            "[and_elim swap and_elim drop swap and_intro]",
        ),
        (
            "[A B & C &] [A B C & &] claim",
            "prop: (A ∧ B) ∧ C -- A ∧ (B ∧ C)",
            "[and_elim swap and_elim dig2 and_intro and_intro]",
        ),
    ] {
        check_proof(task, prop, proof);
    }
}

#[test]
fn session2_impl() {
    for (task, prop, proof) in [("[A A B ->] [B] claim", "prop: A A → B -- B", "[imp_elim]")] {
        check_proof(task, prop, proof);
    }
}
