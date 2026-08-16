/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.BaseField

/-!
# One function is enough

Everything the Galois correspondence for a covering asks of the analysis is a single function: one
holomorphic function of moderate growth taking distinct values at the points of one fibre.  Such a
function separates every nontrivial deck transformation from the identity at that fibre, which is
the faithfulness the correspondence runs on, and the conclusion is then a Galois extension of the
rational functions of the base coordinate with the deck group as Galois group.

That is the whole analytic input, stated once and used once.  It is also, by the criteria of
`RET/Analytic/`, a primitive element: every function of moderate growth on the covering is a
rational expression in the base coordinate and in it.

## Main definitions

* `Rigidity.RET.HasSeparatingFunction` — the covering carries a function of moderate growth
  separating the points of a fibre.

## Main results

* `Rigidity.RET.separating_of_hasSeparatingFunction` — such a function moves every nontrivial deck
  transformation.
* `Rigidity.RET.exists_isGalois_ratFunc_of_hasSeparatingFunction` — a connected covering with such
  a function has a function field which is a Galois extension of the rational functions of the base
  coordinate, of degree the order of the deck group and with the deck group as Galois group.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

section Separating

universe u

variable {Y : Type u} [TopologicalSpace Y] {f : Y → ℂ} {S : Finset ℂ}

/-- **The covering carries a separating function**: a holomorphic function of moderate growth
taking distinct values at the points of some fibre. -/
def HasSeparatingFunction (hf : IsLocalHomeomorph f) (S : Finset ℂ) (H : Type*) [Group H]
    [MulAction H Y] : Prop :=
  ∃ F ∈ coverRing hf S, ∃ y₀ : Y, ∀ a b : H, F (a • y₀) = F (b • y₀) → a = b

variable {H : Type*} [Group H] [MulAction H Y]

/-- **A separating function moves every nontrivial deck transformation.** -/
theorem separating_of_hasSeparatingFunction {hf : IsLocalHomeomorph f}
    (hsep : HasSeparatingFunction hf S H) (a : H) (ha : a ≠ 1) :
    ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y := by
  obtain ⟨F, hF, y₀, hinj⟩ := hsep
  exact ⟨F, hF, y₀, fun h => ha (hinj a 1 (by simpa using h))⟩

end Separating

section Field

universe u

variable {Y : Type u} [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y] {f : Y → ℂ}
variable {S : Finset ℂ}
variable {H : Type*} [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]

attribute [local instance] FractionRing.liftAlgebra ratFuncAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
/-- **A connected covering with a separating function has a function field which is a Galois
extension of the rational functions of the base coordinate, with the deck group as Galois group
and degree the order of that group.**

This is the Galois correspondence for a covering in the form the Riemann existence theorem wants:
a topological covering of a punctured plane, together with one holomorphic function of moderate
growth separating the points of a fibre, produces a finite Galois extension of `ℂ(T)` realizing
the deck group. -/
theorem exists_isGalois_ratFunc_of_hasSeparatingFunction (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hsep : HasSeparatingFunction hf S H) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra (RatFunc ℂ) L),
      IsGalois (RatFunc ℂ) L ∧ Nonempty (H ≃* (L ≃ₐ[RatFunc ℂ] L)) ∧
        Module.finrank (RatFunc ℂ) L = Nat.card H := by
  have hsep' : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y :=
    fun a ha => separating_of_hasSeparatingFunction hsep a ha
  letI := coverRatFuncAlgebra hf hrange
  exact ⟨FractionRing ↥(coverRing hf S), inferInstance, inferInstance,
    isGalois_ratFunc_coverRing hf hrange htrans hsep',
    ⟨mulEquivAlgEquiv_ratFunc_coverRing hf hrange htrans hsep'⟩,
    finrank_ratFunc_coverRing hf hrange htrans hsep'⟩

end Field

end Rigidity.RET

end
