/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.MultiKummer
import InverseGalois.Rigidity.RET.Genus.OrdUltra

/-!
# The order of a Kummer radicand pulled back along a function

A multi-point Kummer radicand is a product `∏ᵢ (X - tᵢ)^{eᵢ}` of linear polynomials.  Substituting
for `X` an element `u` of a function field turns it into `∏ᵢ (u - tᵢ)^{eᵢ}`, whose order at a place
is the corresponding combination `∑ᵢ eᵢ · ord (u - tᵢ)` of the orders of the individual factors.

Two special cases carry the whole weight of an independence argument.  At a place where `u` avoids
every `tᵢ` — that is, where each `u - tᵢ` is a unit — the substituted radicand is a unit too.  At a
place where `u - tᵢ₀` has a simple zero and every other `u - tᵢ` is a unit, the substituted radicand
has order exactly `eᵢ₀`.  A place of the second kind is what certifies that one layer of a family of
Kummer extensions is independent of the others.

## Main results

* `Rigidity.RET.eval₂_multiA` — substituting into a multi-point radicand.
* `Rigidity.RET.ord_eval₂_multiA` — its order as a combination of the orders of the factors.
* `Rigidity.RET.ord_eval₂_multiA_eq_zero` — a place at which the substituted radicand is a unit.
* `Rigidity.RET.ord_eval₂_multiA_eq` — a place at which it has order exactly one exponent.
-/

open Polynomial IsDedekindDomain

noncomputable section

namespace Rigidity.RET

open GeomAKLB

variable {K : Type*} [Field K] (φ : k →+* K) {r : ℕ} (t : Fin r → k) (e : Fin r → ℕ) (u : K)

/-- **Substituting an element of an extension into a multi-point Kummer radicand.** -/
theorem eval₂_multiA : eval₂ φ u (multiA t e) = ∏ i, (u - φ (t i)) ^ e i := by
  simp [multiA, eval₂_finset_prod, eval₂_pow]

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]

/-- **The order of a substituted radicand is the combination of the orders of its factors.** -/
theorem ord_eval₂_multiA (v : HeightOneSpectrum R) (hu : ∀ i, u - φ (t i) ≠ 0) :
    ord K v (eval₂ φ u (multiA t e)) = ∑ i, e i * ord K v (u - φ (t i)) := by
  rw [eval₂_multiA, ord_prod (v := v) Finset.univ (fun i => (u - φ (t i)) ^ e i)
    fun i _ => pow_ne_zero _ (hu i)]
  exact Finset.sum_congr rfl fun i _ => ord_pow v (hu i) (e i)

/-- **A substituted radicand is a unit at a place where the substituted element avoids every
point.** -/
theorem ord_eval₂_multiA_eq_zero (v : HeightOneSpectrum R) (hu : ∀ i, u - φ (t i) ≠ 0)
    (h : ∀ i, ord K v (u - φ (t i)) = 0) :
    ord K v (eval₂ φ u (multiA t e)) = 0 := by
  rw [ord_eval₂_multiA φ t e u v hu]
  simp [h]

/-- **A substituted radicand has order exactly one exponent at a place where the substituted element
meets exactly one point, simply.** -/
theorem ord_eval₂_multiA_eq (v : HeightOneSpectrum R) (hu : ∀ i, u - φ (t i) ≠ 0) {i₀ : Fin r}
    (h₀ : ord K v (u - φ (t i₀)) = 1) (h : ∀ i, i ≠ i₀ → ord K v (u - φ (t i)) = 0) :
    ord K v (eval₂ φ u (multiA t e)) = e i₀ := by
  rw [ord_eval₂_multiA φ t e u v hu, Finset.sum_eq_single i₀]
  · rw [h₀, mul_one]
  · intro i _ hi
    rw [h i hi, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i₀) hi

end Rigidity.RET
