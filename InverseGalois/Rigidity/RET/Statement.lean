/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The honest Riemann Existence Theorem: its recognizable conclusion

This file names the **textbook conclusion** of the rigidity method — the object the honest
Riemann Existence Theorem actually produces — so that the axiom cut can be phrased against a
statement one would recognize from Völklein, *Groups as Galois Groups* (Thm 2.13) or Serre,
*Topics in Galois Theory* (§8): *a finite group with a rigid, rational, generating,
product-one tuple occurs as the Galois group of a **regular** extension of `ℚ(T)`.*

The now-retired axiom `riemann_existence_ax` was **over-specified**: it handed over the entire
`of_regular_family` polynomial bundle — a monic `ℚ[T][X]` family, an absolutely irreducible
resolvent, cofinite separability, and the *per-specialization* landing/root certificates.  A
textbook RET produces none of that arithmetic model; it produces a **field extension**.  It has
been replaced by the covers-form theorem `riemann_existence_cover` (`RET.Existence`), whose output
is exactly such a field extension.  This file defines that field extension as
`IsRegularInverseGalois`, the honest target: the two Mathlib-blocked steps

* `RigidityCertificate G → IsRegularInverseGalois G` (RET + branch-cycle descent), and
* `IsRegularInverseGalois G → IsInverseGalois G` (specialization / Hilbert irreducibility),

can then each be stated recognizably, instead of being smuggled together into one bundle.

## Main definitions

* `IsRegularInverseGalois G` — there is a regular Galois extension `L / ℚ(T)` with
  `Gal(L / ℚ(T)) ≃* G`, "regular" meaning `ℚ` is relatively algebraically closed in `L` (the
  field of constants of `L` is exactly `ℚ`, i.e. `algebraicClosure ℚ L = ⊥`).

## Main results

* `IsRegularInverseGalois.of_mulEquiv` — invariance under group isomorphism.
-/

open Polynomial

/-- A group `G` is a **regular inverse Galois group** (over `ℚ(T)`) if there is a finite Galois
extension `L / ℚ(T)` with `Gal(L / ℚ(T)) ≃* G` that is **regular**: `ℚ` is relatively
algebraically closed in `L`, i.e. the relative algebraic closure `algebraicClosure ℚ L` is the
bottom intermediate field `⊥ = ℚ` (`L` gains no new constants over `ℚ`).

This is the recognizable conclusion of the rigidity method (Völklein, *Groups as Galois Groups*,
Thm 2.13).  Regularity is exactly what makes the extension specialize: it descends to a genuine
`ℚ`-Galois extension with the same group at infinitely many values of `T` (Hilbert
irreducibility), giving `IsInverseGalois G`. -/
def IsRegularInverseGalois (G : Type*) [Group G] : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℚ) L) (_ : FiniteDimensional (RatFunc ℚ) L)
    (_ : IsGalois (RatFunc ℚ) L) (_ : Algebra ℚ L) (_ : IsScalarTower ℚ (RatFunc ℚ) L),
    algebraicClosure ℚ L = ⊥ ∧ Nonempty ((L ≃ₐ[RatFunc ℚ] L) ≃* G)

namespace IsRegularInverseGalois

variable {G H : Type*} [Group G] [Group H]

/-- Invariance under group isomorphism: a regular Galois realization of `G` is also one of any
group isomorphic to `G`. -/
theorem of_mulEquiv (hG : IsRegularInverseGalois G) (e : G ≃* H) :
    IsRegularInverseGalois H := by
  obtain ⟨L, hF, hA, hFD, hGal, hAQ, hST, hreg, ⟨φ⟩⟩ := hG
  exact ⟨L, hF, hA, hFD, hGal, hAQ, hST, hreg, ⟨φ.trans e⟩⟩

end IsRegularInverseGalois
