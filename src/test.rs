fn eval2(i: &str, j: &str) -> crate::Expr {
    use crate::{ast, exec};

    let es = ast::parse(i).unwrap();
    let fs = ast::parse(j).unwrap();
    let mut s = Vec::new();
    for e in es {
        let _ = exec(&mut s, e);
    }
    for f in fs {
        let _ = exec(&mut s, f);
    }
    assert_eq!(s.len(), 1);
    let t = s.pop().unwrap();
    println!("{t}");
    t
}

fn check_proof(task: &str, prop: &str, proof: &str) {
    use crate::{ast::parse, display_stack, prove, Expr, Mode, ProofCtx, Prop};
    let p = eval2(task, "claim");
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
        let (stk1, pf1) = match prove(
            ProofCtx {
                prop: p.as_prop().unwrap().clone(),
                stk,
                proof: pf,
            },
            e,
        ) {
            Some((Mode::Proof(ProofCtx { stk, proof, .. }), _)) => (stk, proof),
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
    let t = eval2("[A B & C | D ->]", "term");
    println!("{t}");
    assert_eq!("((A ∧ B) ∨ C) → D", format!("{t}"));
}

#[test]
fn session1_and() {
    for (task, prop, proof) in [
        ("[A] [A]", "prop: A -- A", "[]"),
        ("[A B] [A]", "prop: A B -- A", "[drop]"),
        ("[A B] [B A]", "prop: A B -- B A", "[swap]"),
        ("[A B] [A B &]", "prop: A B -- A ∧ B", "[and_intro]"),
        ("[A A] [A A &]", "prop: A A -- A ∧ A", "[and_intro]"),
        ("[A B &] [A]", "prop: A ∧ B -- A", "[and_elim drop]"),
        ("[A B &] [A B]", "prop: A ∧ B -- A B", "[and_elim]"),
        ("[A B &] [A B &]", "prop: A ∧ B -- A ∧ B", "[]"),
        (
            "[A B ∧] [B A &]",
            "prop: A ∧ B -- B ∧ A",
            "[and_elim swap and_intro]",
        ),
        (
            "[A B & C &] [A B C]",
            "prop: (A ∧ B) ∧ C -- A B C",
            "[and_elim swap and_elim dig2]",
        ),
        (
            "[A B & C &] [A C &]",
            "prop: (A ∧ B) ∧ C -- A ∧ C",
            "[and_elim swap and_elim drop swap and_intro]",
        ),
        (
            "[A B & C &] [A B C & &]",
            "prop: (A ∧ B) ∧ C -- A ∧ (B ∧ C)",
            "[and_elim swap and_elim dig2 and_intro and_intro]",
        ),
    ] {
        check_proof(task, prop, proof);
    }
}

#[test]
fn session2_impl() {
    for (task, prop, proof) in [
        ("[A A B ->] [B]", "prop: A A → B -- B", "[imp_elim]"),
        (
            "[A A B -> B C ->] [C]",
            "prop: A A → B B → C -- C",
            "[bury2 imp_elim swap imp_elim]",
        ),
        //(_, "prop: A A → B A → C B → D C → D -- D", _),
        //("[A B -> B C ->] [A -> C]", "prop: A → B B → C -- A → C", "[[dig2 imp_elim imp_elim] [A] imp_intro"),
    ] {
        check_proof(task, prop, proof);
    }
}
