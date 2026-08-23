/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Exact cycles of finite abelian groups

An exact sequence of finite abelian groups arranged in a cycle of even length has the property
that the product of the orders of the terms in even position equals the product of the orders of
the terms in odd position.  The reason is entirely local: at each term the order splits as the
order of the kernel times the order of the range, the kernel at one term is the range at the
previous one, and going once around the cycle each range is counted exactly once on either side.

The case needed later is a cycle of length six, the *hexagon* that the Tate cohomology of a
cyclic group attaches to a short exact sequence of modules.  It is stated here on its own because
nothing about cohomology enters: it is a statement about six finite abelian groups and six maps.

## Main results

* `InverseGalois.CFT.card_eq_card_ker_mul_card_range`: the order of a finite abelian group is the
  order of the kernel times the order of the range of any homomorphism out of it.
* `InverseGalois.CFT.card_mul_card_mul_card_eq_of_exactHexagon`: **the hexagon identity**, that in
  a cyclic exact sequence of six finite abelian groups the alternating product of the orders is
  trivial.

## Tags

exact sequence, finite abelian group, hexagon
-/

namespace InverseGalois.CFT

/-- **The order of a finite abelian group splits as kernel times range.**  The first isomorphism
theorem identifies the quotient by the kernel with the range, and the order of a group is the
order of a subgroup times its index. -/
theorem card_eq_card_ker_mul_card_range {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Finite A] (f : A →+ B) : Nat.card A = Nat.card f.ker * Nat.card f.range := by
  have hquot : Nat.card (A ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  have hindex := AddSubgroup.card_mul_index f.ker
  rw [AddSubgroup.index_eq_card, hquot] at hindex
  exact hindex.symm

/-- **The hexagon identity.**  Six finite abelian groups joined in a cycle by six homomorphisms,
exact at every term, satisfy the relation that the product of the orders in odd position equals
the product of the orders in even position.  Writing `rᵢ` for the order of the range of the `i`-th
map, the order of the `i`-th group is `rᵢ₋₁ * rᵢ`, and both sides of the claimed identity are the
product of all six `rᵢ`. -/
theorem card_mul_card_mul_card_eq_of_exactHexagon
    {A₁ A₂ A₃ A₄ A₅ A₆ : Type*} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
    [AddCommGroup A₄] [AddCommGroup A₅] [AddCommGroup A₆]
    [Finite A₁] [Finite A₂] [Finite A₃] [Finite A₄] [Finite A₅] [Finite A₆]
    (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ A₃) (f₃ : A₃ →+ A₄) (f₄ : A₄ →+ A₅) (f₅ : A₅ →+ A₆)
    (f₆ : A₆ →+ A₁)
    (h₁ : f₆.range = f₁.ker) (h₂ : f₁.range = f₂.ker) (h₃ : f₂.range = f₃.ker)
    (h₄ : f₃.range = f₄.ker) (h₅ : f₄.range = f₅.ker) (h₆ : f₅.range = f₆.ker) :
    Nat.card A₁ * Nat.card A₃ * Nat.card A₅ = Nat.card A₂ * Nat.card A₄ * Nat.card A₆ := by
  have e₁ := card_eq_card_ker_mul_card_range f₁
  have e₂ := card_eq_card_ker_mul_card_range f₂
  have e₃ := card_eq_card_ker_mul_card_range f₃
  have e₄ := card_eq_card_ker_mul_card_range f₄
  have e₅ := card_eq_card_ker_mul_card_range f₅
  have e₆ := card_eq_card_ker_mul_card_range f₆
  rw [← h₁] at e₁
  rw [← h₂] at e₂
  rw [← h₃] at e₃
  rw [← h₄] at e₄
  rw [← h₅] at e₅
  rw [← h₆] at e₆
  rw [e₁, e₂, e₃, e₄, e₅, e₆]
  ring

end InverseGalois.CFT
