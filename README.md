StackPM
-------

The goal is to create an interactive theorem prover supporting similar concepts
as "the incredible proof machine" (see [incredible.pm]) -- so mostly
first-order logic -- but with a stack-based (think Forth/Joy) instead of a
visual language.

The current code supports predicate logic without quantifiers. However the
proofs are already quite hard to read, so unless inspiration strikes how to
make this more usuable, I will probably not add more features for now.

An example proof can look like this:

```
[A B -> ⊥ ->] [A B ⊥ -> &] claim
(* prop: (A → B) → ⊥ -- A ∧ (B → ⊥) *)
prove
        [B] cases
        [
                [drop swap drop] [A] imp_intro
                swap drop swap imp_elim
                [A B ⊥ -> &] efql]
        [
                [A] cases
                [swap and_intro swap drop]
                [
                        [swap imp_elim [B] efql swap drop swap drop] [A] imp_intro
                        swap drop swap drop swap imp_elim
                        [A B ⊥ → ∧] efql]
                or_elim swap drop swap drop]
        or_elim swap drop
qed
```
