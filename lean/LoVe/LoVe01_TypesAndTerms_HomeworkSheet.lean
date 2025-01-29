/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 1 (10 points): Types and Terms

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (6 points): Terms

We start by declaring four new opaque types. -/

opaque α : Type
opaque β : Type
opaque γ : Type
opaque δ : Type

/- 1.1 (4 points). Complete the following definitions, by providing terms with
the expected type.

Please use reasonable names for the bound variables, e.g., `a : α`, `b : β`,
`c : γ`.

Hint: A procedure for doing so systematically is described in Section 1.4 of the
Hitchhiker's Guide. As explained there, you can use `_` as a placeholder while
constructing a term. By hovering over `_`, you will see the current logical
context. -/

def B : (α → β) → (γ → α) → γ → β :=
  fun f₁ f₂ c ↦ f₁ (f₂ c)
  -- compute f2(c) first and apply result as input to f1

def S : (α → β → γ) → (α → β) → α → γ :=
  fun f₁ f₂ a ↦ f₁ a (f₂ a)

  -- f1(a) becomes β → γ so we need a β as an input which we get from (f₂ a)

def moreNonsense : ((α → β) → γ → δ) → γ → β → δ :=
  fun f₁ c b ↦ f₁ (fun _ ↦ b) c
  -- little more confusing with placeholder
  -- create anonymous function which ignores input and returns b

def evenMoreNonsense : (α → β) → (α → γ) → α → β → γ :=
  fun _ f₂ a _ ↦ f₂ a
  -- easy!

/- 1.2 (2 points). Complete the following definition.

This one looks more difficult, but it should be fairly straightforward if you
follow the procedure described in the Hitchhiker's Guide.

Note: Peirce is pronounced like the English word "purse". -/

def weakPeirce : ((((α → β) → α) → α) → β) → β :=
  fun f₁ ↦ f₁ fun _ ↦ (fun _ ↦ (fun _ ↦ _))
  -- this one is crazy i don't understand it

/- ## Question 2 (4 points): Typing Derivation

Show the typing derivation for your definition of `B` above, using ASCII or
Unicode art. You might find the characters `–` (to draw horizontal bars) and `⊢`
useful.

Feel free to introduce abbreviations to avoid repeating large contexts `C`. -/

-- write your solution here

end LoVe
