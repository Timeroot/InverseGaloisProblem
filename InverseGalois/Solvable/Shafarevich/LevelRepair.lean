/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LevelRamification
import InverseGalois.Solvable.Shafarevich.LevelTwist
import InverseGalois.Solvable.Shafarevich.RamifiedTransport

/-!
# The repair of the restriction costs nothing beyond a lift which carries it

What the ladder asks of the arithmetic at every rung past the first is that a lift which already has
every clause of a solution except the prescribed restriction be replaced by one which has that too.
Of the four clauses of a solution, three survive any replacement over the same map to the level
below: such a replacement is again over the base realization, because the projection of the
extension is compatible with the projection to the operator group, and being onto is free past the
first layer, the layer lying in the Frattini subgroup of the normal factor.  So the whole of the
repair is the production of *some* lift, over the same solution below and still trivial along the
family, which carries the restriction; whether it is onto is not something the arithmetic has to
check.

That is the shape the arithmetic works in.  Two lifts of the same solution differ by a one cocycle
with values in the layer, and the restriction the new lift is to carry is a condition on its
behaviour at the primes where it ramifies over the base realization — of which there are finitely
many up to conjugacy.  So the repair is a prescription of the local components of a global class of
the first cohomology, which is what the duality theorems of class field theory speak about.

## Main definitions

* `InverseGalois.Shafarevich.HasLiftRepair` — **the repair of the restriction, asked only for a
  lift and not for a solution.**

## Main results

* `InverseGalois.Shafarevich.hasSolutionRepair_of_hasLiftRepair` — **a repair which produces a lift
  produces a solution**, past the first layer.

## Tags

Shafarevich's theorem, embedding problem, ramification, one cocycle, Frattini subgroup
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

/-! ### The repair, asked for a lift -/

/-- **The repair of the restriction, asked only for a lift and not for a solution.**

The data is the same as for the repair the ladder consumes: a solution at one rung carrying the
restriction, and a lift of it across the next layer which is onto, smooth, over that solution and
trivial on the part of each member of the finite family the base realization already kills.  What is
asked back is less: another lift over the same solution, again smooth and again trivial along the
family, which carries the restriction — and nothing about it being onto, that being free past the
first layer.

The repair may spend a shrinking of its own: it announces the number of letters it wants the given
lift read at, and answers with a surjection onto the number asked for and a lift over the pushed
down solution.  That is the same bargain the count against the second cohomology strikes, and it
costs nothing, solutions being available at every number of letters. -/
def HasLiftRepair (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type)
    [Group S] [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (φ : Gal(Ω/k) →* U) {t : ℕ} (D : Fin t → Subgroup Gal(Ω/k)) : Prop :=
  ∃ N : ℕ,
    ∀ (Φ : Gal(Ω/k) →* GenericQuot ℓ U N S j) (f : Gal(Ω/k) →* GenericQuot ℓ U N S (j + 1)),
      IsSmoothHom Φ → (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) →
      IsSplitTotallyRamifiedHom ℓ φ Φ → Function.Surjective f → IsSmoothHom f →
      (∀ x, (layerExtension ℓ (genericAut U N S) j).rightHom (f x) = Φ x) →
      (∀ ν : Fin t, ∀ x ∈ D ν, φ x = 1 → f x = 1) →
      ∃ (α : Generic U N S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
        ∃ Ψ : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1), IsSmoothHom Ψ ∧
          (∀ x, (layerExtension ℓ (genericAut U n S) j).rightHom (Ψ x)
            = layerSemidirectMap ℓ hα j (Φ x)) ∧
          (∀ ν : Fin t, ∀ x ∈ D ν, φ x = 1 → Ψ x = 1) ∧ IsSplitTotallyRamifiedHom ℓ φ Ψ

/-! ### The repair the ladder consumes -/

/-- **A repair which produces a lift produces a solution**, past the first layer.

A lift over the solution below is over the base realization, the projection of the extension leaving
the operator coordinate alone; and it is onto, because the solution below is onto — the given lift
being onto, the projection of the extension being onto and the shrinking the repair spends being
onto — and a lift over a surjection generates the group one layer up together with the layer, which
past the first layer lies in the Frattini subgroup of the normal factor. -/
theorem hasSolutionRepair_of_hasLiftRepair (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U]
    (n : ℕ) (S : Type) [Group S] [Finite S] (hS : IsPGroup ℓ S) {j : ℕ} (hj : 1 ≤ j)
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {φ : Gal(Ω/k) →* U} {t : ℕ}
    {D : Fin t → Subgroup Gal(Ω/k)} (h : HasLiftRepair ℓ U n S j φ D) :
    HasSolutionRepair ℓ U n S j φ D (IsSplitTotallyRamified ℓ U S φ) := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun Φ f hΦsm hΦright hΦP hfsurj hfsm hfright hfD => ?_⟩
  obtain ⟨α, hα, hαsurj, Ψ, hΨsm, hΨright, hΨD, hΨP⟩ :=
    h Φ f hΦsm hΦright hΦP hfsurj hfsm hfright hfD
  refine ⟨Ψ, ?_, hΨsm, ?_, ?_, hΨP⟩
  · refine surjective_of_rightHom_comp_surjective ℓ (isPGroup_generic U n S hS)
      (genericAut U n S) hj Ψ fun y => ?_
    obtain ⟨w, hw⟩ := layerSemidirectMap_surjective ℓ hα j hαsurj y
    obtain ⟨v, hv⟩ := (layerExtension ℓ (genericAut U N S) j).rightHom_surjective w
    obtain ⟨z, hz⟩ := hfsurj v
    exact ⟨z, by rw [MonoidHom.comp_apply, hΨright z, ← hfright z, hz, hv, hw]⟩
  · intro x
    have hr : SemidirectProduct.rightHom (Ψ x) = SemidirectProduct.rightHom (Φ x) :=
      congrArg SemidirectProduct.rightHom (hΨright x)
    rw [hr, hΦright x]
  · rintro A ⟨ν, rfl⟩ x hx hx1
    exact hΨD ν x hx hx1

end InverseGalois.Shafarevich
