/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
  a → a :=
  assume ha: a
  ha

theorem K (a b : Prop) :
  a → b → b :=
  assume ha: a
  assume hb: b
  hb

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
  assume habc: a → b → c
  assume hb: b
  assume ha: a
  habc ha hb

theorem proj_fst (a : Prop) :
  a → a → a :=
  assume haa : a
  assume ha : a
  haa

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
  a → a → a :=
  assume haa: a
  assume ha : a
  ha

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
  assume habc: a → b → c
  assume ha: a
  assume ac: (a → c)
  assume b: b
  habc ha b

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
  assume hab: a → b
  assume hnb: ¬ b
  assume ha: a
  -- function to take in an a and return a false
  hnb (hab ha)


/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  -- left to right
  Iff.intro
  (assume pnq: ∀x, p x ∧ q x
    have hp: ∀ x, p x :=
      assume x: α
      have pxqx: p x ∧ q x := pnq x
      show p x from And.left pxqx
    have hq: ∀ x, q x :=
      assume x: α
      have pxqx: p x ∧ q x := pnq x
      show q x from And.right pxqx
    show (∀x, p x) ∧ (∀x, q x) from
      And.intro hp hq)

  -- right to left
  (assume xpxq: (∀x, p x) ∧ (∀x, q x)
    have hxp: ∀x, p x := And.left xpxq
    have hxq: ∀x, q x := And.right xpxq
    have hpq: ∀x, p x ∧ q x :=
      assume x: α
      have hp: p x := hxp x
      have hq: q x := hxq x
      show p x ∧ q x
        from And.intro hp hq
    show ∀x, p x ∧ q x from
      hpq)



/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  sorry


/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/

theorem binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  sorry

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  sorry


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
  False :=
  sorry

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
  False :=
  sorry

end LoVe
