/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Prescribing the values of a homomorphism to a finite group on a generating family

A free group on a finite set of letters has exactly `|H| ^ (number of letters)` homomorphisms to a
finite group `H`, one for each choice of values on the letters.  If a group is free on that many
letters and a family of its elements indexed by them generates it, the same count applies twice:
precomposition with the surjection naming that family is an injection between two sets of
homomorphisms of the same finite size, hence a bijection.  So *every* choice of values in `H` for
the members of the family is realized by a homomorphism out of the group, exactly as it would be
were the family a basis.

This is the finite-quotient form of the Hopf property of a finitely generated free group, and it is
what one needs to build a cover of a region with prescribed local monodromy: the punctures number
the rank of the fundamental group, the loops around them generate it, and the prescribed local
monodromies are arbitrary elements of a finite group.

## Main results

* `Rigidity.RET.surjective_freeGroupLift` — the homomorphism naming a generating family is onto.
* `Rigidity.RET.exists_monoidHom_apply_eq` — a homomorphism to a finite group taking prescribed
  values on a generating family indexed by the letters of a free group.
-/

namespace Rigidity.RET

variable {G : Type*} [Group G] {α : Type*} {H : Type*} [Group H]

/-- **The homomorphism from a free group naming a generating family is onto.** -/
theorem surjective_freeGroupLift {γ : α → G} (hγ : Subgroup.closure (Set.range γ) = ⊤) :
    Function.Surjective (FreeGroup.lift γ) := by
  rw [← MonoidHom.range_eq_top, MonoidHom.range_eq_map, ← FreeGroup.closure_range_of,
    MonoidHom.map_closure, ← Set.range_comp]
  simpa [Function.comp_def, FreeGroup.lift_apply_of] using hγ

/-- Homomorphisms out of a free group on finitely many letters into a finite group are finite in
number: each is named by its values on the letters. -/
theorem finite_freeGroup_monoidHom [Finite α] [Finite H] : Finite (FreeGroup α →* H) :=
  Finite.of_equiv _ (FreeGroup.lift (β := H))

/-- **A homomorphism to a finite group can be prescribed arbitrarily on a generating family
indexed by the letters of a free group.**  Precomposition with the surjection naming the family is
an injection of the homomorphisms out of the group into the homomorphisms out of the free group;
those two sets have the same finite number of elements, so it is onto. -/
theorem exists_monoidHom_apply_eq [Finite α] [Finite H] (ψ : G ≃* FreeGroup α) {γ : α → G}
    (hγ : Subgroup.closure (Set.range γ) = ⊤) (h : α → H) :
    ∃ φ : G →* H, ∀ i, φ (γ i) = h i := by
  classical
  haveI : Finite (FreeGroup α →* H) := finite_freeGroup_monoidHom
  -- Homomorphisms out of the group are named by homomorphisms out of the free group.
  let e : (G →* H) ≃ (FreeGroup α →* H) :=
    { toFun := fun φ => φ.comp ψ.symm.toMonoidHom
      invFun := fun φ => φ.comp ψ.toMonoidHom
      left_inv := fun φ => by ext x; simp
      right_inv := fun φ => by ext x; simp }
  haveI : Finite (G →* H) := Finite.of_equiv _ e.symm
  -- Precomposition with the surjection naming the family is injective, hence onto.
  have hσ : Function.Surjective (FreeGroup.lift γ) := surjective_freeGroupLift hγ
  have hP : Function.Injective fun φ : G →* H => φ.comp (FreeGroup.lift γ) := by
    intro φ₁ φ₂ hEq
    ext x
    obtain ⟨y, rfl⟩ := hσ x
    exact congrArg (fun f : FreeGroup α →* H => f y) hEq
  obtain ⟨φ, hφ⟩ := (Finite.injective_iff_surjective_of_equiv e).mp hP (FreeGroup.lift h)
  refine ⟨φ, fun i => ?_⟩
  have := congrArg (fun f : FreeGroup α →* H => f (FreeGroup.of i)) hφ
  simpa [FreeGroup.lift_apply_of] using this

end Rigidity.RET
