/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.CompletionGalois
import InverseGalois.CFT.Units.OrbitPlaces
import InverseGalois.CFT.Global.HasseNorm

/-!
# A rational number which is everywhere locally a sum of two squares

A rational number is a sum of two squares as soon as it is one in every field of `p`-adic numbers.
The archimedean place is not needed: a sum of two squares in the completion at a single finite place
is already positive, so the Hasse norm theorem for the extension obtained by adjoining a square root
of minus one has nothing left to check at infinity.

The local hypothesis arrives here in the shape produced by the local theory, namely as a statement
about the completion of the rational numbers at the prime lying under a prime of a number field.
Every prime of the rational numbers is the prime under some prime of the number field, and the
completion at the prime corresponding to a rational prime is the field of `p`-adic numbers, so the
two shapes agree.

## Main results

* `InverseGalois.CFT.exists_sq_add_sq_of_adicCompletion`: a rational number which is a sum of two
  squares in the completion at a prime corresponding to a rational prime is a sum of two squares in
  the field of `p`-adic numbers.
* `InverseGalois.CFT.exists_sq_add_sq_of_forall_adicCompletion`: **a rational number which is a sum
  of two squares in the completion at the prime below every prime of a number field is a sum of two
  squares.**

## Tags

sum of two squares, Hasse norm theorem, p-adic number, completion, number field
-/

open IsDedekindDomain NumberField

namespace InverseGalois.CFT

/-! ### Transport to the field of `p`-adic numbers -/

/-- A rational number which is a sum of two squares in the completion at a prime corresponding to a
rational prime is a sum of two squares in the field of `p`-adic numbers. -/
theorem exists_sq_add_sq_of_adicCompletion (p : Nat.Primes) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : v = (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p) {c : ℚ}
    (h : ∃ x y : v.adicCompletion ℚ, x ^ 2 + y ^ 2 = algebraMap ℚ (v.adicCompletion ℚ) c) :
    ∃ u t : ℚ_[(p : ℕ)], (c : ℚ_[(p : ℕ)]) = u ^ 2 + t ^ 2 := by
  subst hv
  obtain ⟨x, y, hxy⟩ := h
  set e := Padic.adicCompletionEquiv (R := 𝓞 ℚ) p with he
  refine ⟨e.symm x, e.symm y, e.injective ?_⟩
  simp only [map_add, map_pow, ContinuousAlgEquiv.coe_toAlgEquiv,
    ContinuousAlgEquiv.apply_symm_apply]
  rw [hxy, ← eq_ratCast (algebraMap ℚ ℚ_[(p : ℕ)]) c]
  exact e.toAlgEquiv.commutes c

/-! ### The global statement -/

variable {K : Type} [Field K] [NumberField K]

/-- **A rational number which is a sum of two squares in the completion at the prime below every
prime of a number field is a sum of two squares.**  Adjoining a square root of minus one to the
rational numbers gives a quadratic extension whose norm form is the sum of two squares, and the
Hasse norm theorem for that extension needs no condition at the real place. -/
theorem exists_sq_add_sq_of_forall_adicCompletion {c : ℚ} (hc : c ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 K),
      ∃ x y : (primeUnder (𝓞 ℚ) w).adicCompletion ℚ,
        algebraMap ((primeUnder (𝓞 ℚ) w).adicCompletion ℚ) (w.adicCompletion K) (x ^ 2 + y ^ 2)
          = toAdicCompletion w (algebraMap ℚ K c)) :
    ∃ u t : ℚ, c = u ^ 2 + t ^ 2 := by
  have hloc : ∀ p : Nat.Primes, ∃ u t : ℚ_[(p : ℕ)],
      (c : ℚ_[(p : ℕ)]) = u ^ 2 - ((-1 : ℚ) : ℚ_[(p : ℕ)]) * t ^ 2 := by
    intro p
    obtain ⟨w, hw⟩ :=
      exists_primeUnder_eq (𝓞 ℚ) (𝓞 K) ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
    obtain ⟨x, y, hxy⟩ := h w
    have hstep : x ^ 2 + y ^ 2
        = algebraMap ℚ ((primeUnder (𝓞 ℚ) w).adicCompletion ℚ) c := by
      refine (algebraMap ((primeUnder (𝓞 ℚ) w).adicCompletion ℚ)
        (w.adicCompletion K)).injective ?_
      rw [hxy, ← IsScalarTower.algebraMap_apply ℚ ((primeUnder (𝓞 ℚ) w).adicCompletion ℚ)
        (w.adicCompletion K) c, IsScalarTower.algebraMap_apply ℚ K (w.adicCompletion K) c]
      rfl
    obtain ⟨u, t, hut⟩ :=
      exists_sq_add_sq_of_adicCompletion p (primeUnder (𝓞 ℚ) w) hw ⟨x, y, hstep⟩
    exact ⟨u, t, by rw [hut]; push_cast; ring⟩
  obtain ⟨u, t, hut⟩ := exists_sub_sq_of_forall_local hc (by norm_num : (-1 : ℚ) ≠ 0) hloc
  exact ⟨u, t, by rw [hut]; ring⟩

end InverseGalois.CFT
