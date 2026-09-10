/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LevelRepair
import InverseGalois.Solvable.Shafarevich.LocalLift

/-!
# The repair, with the roots of unity taken out of it

What the arithmetic owes the ladder is a lift carrying the restriction on ramification.  All but one
clause of that restriction is a statement about the values the lift takes on the decomposition and
inertia subgroups of a prime: that the base realization kill the decomposition subgroup, that the
lift take no value there it does not already take on inertia, and that its local image be cyclic.
The remaining clause is about the field — the local field is asked to carry the roots of unity of
the prime times the order of the local image — and it is the awkward one, because that order grows
as the ladder is climbed and so the demand it makes on the base field is not fixed in advance.

It is, however, bounded.  Every value of a solution at a prime where the base realization splits
completely lies over the identity of the base group, hence comes from the generic operator group,
which is killed by the exponent of the test group — a bound depending on neither the level nor the
number of letters.  So the roots of unity clause is discharged once and for all by asking the base
realization to fix the roots of unity of the prime times that exponent, and the repair the
arithmetic is asked for is a statement about values alone.

## Main definitions

* `InverseGalois.Shafarevich.HasCyclicRepair` — **the repair, with the roots of unity taken out of
  it**.

## Main results

* `InverseGalois.Shafarevich.hasLiftRepair_of_hasCyclicRepair` — **the repair about values alone is
  the repair**, for a base realization fixing the roots of unity of the prime times the exponent of
  the test group.

## Tags

Shafarevich's theorem, embedding problem, ramification, cyclic extension, decomposition group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S]
  [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (φ : Gal(Ω/k) →* U) {t : ℕ}
  (D : Fin t → Subgroup Gal(Ω/k))

/-! ### The repair about values alone -/

/-- **The repair, with the roots of unity taken out of it.**

The data is that of `InverseGalois.Shafarevich.HasLiftRepair`: a solution at one rung carrying the
restriction, and a lift of it across the next layer which is smooth, over that solution and trivial
on the part of each member of the finite family the base realization already kills.  What is asked
back is another such lift whose ramification over the base realization is cyclic and totally
ramified at every prime where it occurs, with nothing asked about the roots of unity in the local
field. -/
def HasCyclicRepair : Prop :=
  ∀ (Φ : Gal(Ω/k) →* GenericQuot ℓ U n S j) (f : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1)),
    IsSmoothHom Φ → (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) →
    IsSplitTotallyRamifiedHom ℓ φ Φ → IsSmoothHom f →
    (∀ x, (layerExtension ℓ (genericAut U n S) j).rightHom (f x) = Φ x) →
    (∀ ν : Fin t, ∀ x ∈ D ν, φ x = 1 → f x = 1) →
    ∃ Ψ : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1), IsSmoothHom Ψ ∧
      (∀ x, (layerExtension ℓ (genericAut U n S) j).rightHom (Ψ x) = Φ x) ∧
      (∀ ν : Fin t, ∀ x ∈ D ν, φ x = 1 → Ψ x = 1) ∧ IsCyclicRamifiedHom φ Ψ

/-! ### The repair about values alone is the repair -/

variable {ℓ U n S j φ D}

/-- **The repair about values alone is the repair**, for a base realization fixing the roots of
unity of the prime times the exponent of the test group.

A lift across one layer over a solution which is over the base realization is itself over the base
realization, so at a prime where the base realization splits completely its values lie over the
identity of the base group and are killed by that exponent.  The roots of unity clause of the
restriction asks for the roots of unity of the prime times the order of one of those values, and
those are among the ones the base realization is asked to fix. -/
theorem hasLiftRepair_of_hasCyclicRepair
    (hmu : ∀ ζ : Ωˣ, ζ ^ (ℓ * Monoid.exponent S) = 1 → ∀ σ ∈ φ.ker, σ • ζ = ζ)
    (h : HasCyclicRepair ℓ U n S j φ D) : HasLiftRepair ℓ U n S j φ D := by
  intro Φ f hΦsm hΦright hΦP _ hfsm hfright hfD
  obtain ⟨Ψ, hΨsm, hΨright, hΨD, hcyc⟩ := h Φ f hΦsm hΦright hΦP hfsm hfright hfD
  have hright : ∀ x, SemidirectProduct.rightHom (Ψ x) = φ x := by
    intro x
    have hr := congrArg SemidirectProduct.rightHom (hΨright x)
    rw [hΦright x] at hr
    exact hr
  refine ⟨Ψ, hΨsm, hΨright, hΨD,
    isSplitTotallyRamifiedHom_of_isCyclicRamifiedHom (fun x hx => ?_) hmu hcyc⟩
  exact pow_exponent_eq_one_of_rightHom_eq_one ℓ U n S (j + 1) (by rw [hright x, hx])

end InverseGalois.Shafarevich
