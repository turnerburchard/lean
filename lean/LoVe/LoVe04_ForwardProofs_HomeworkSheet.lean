/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 4 (10 points): Forward Proofs

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- 1.1 (2 points). Prove the same theorem again, this time by providing a proof
term.

Hint: There is an easy way. -/

theorem about_Impl_term :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
    assume a: Prop
    assume b: Prop
    assume hnaob: ¬ a ∨ b
    -- why can't we assume ha within the Or.elim?
    assume ha: a
    show b from Or.elim hnaob
      -- given hna, b
      (
      assume hna: ¬ a

      False.elim (hna ha)
       -- i don't understand how proving false proves b
       -- Ex falso quodlibet
      )
      -- given b, b
      (
        assume hb: b
        hb
      )



/- 1.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
    fix a: Prop
    fix b: Prop
    fix hnaob: ¬ a ∨ b
    assume ha: a
    show b from Or.elim hnaob
      (
        sorry
      )
      (sorry)

    -- whoops same proof again



/- ## Question 2 (6 points): Connectives and Quantifiers

2.1 (3 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
  (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  sorry

/- 2.2 (3 points). We have proved or stated three of the six possible
implications between `ExcludedMiddle`, `Peirce`, and `DoubleNegation` in the
exercise of lecture 3. Prove the three missing implications using structured
proofs, exploiting the three theorems we already have. -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

theorem Peirce_of_DN :
  DoubleNegation → Peirce :=
    Peirce_of_EM (SorryTheorems.EM_of_DN hDN)

theorem EM_of_Peirce :
  Peirce → ExcludedMiddle :=
  begin
    intro hPeirce,
    apply EM_of_DN,
    apply DN_of_Peirce,
    exact hPeirce,
  end

theorem dn_of_em :
  ExcludedMiddle → DoubleNegation :=
begin
  intro hEM,
  apply DN_of_Peirce,
  apply Peirce_of_EM,
  exact hEM,
end


end BackwardProofs

end LoVe
