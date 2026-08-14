/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.OrdBound

/-!
# The value of a function at a prime

Over an algebraically closed field of constants a point of a cover has no room for a residue field
larger than the constants: every function of the cover agrees, at a given prime, with a constant.
That is a statement about the functions of the domain, and it extends at once to all functions
merely regular at the prime, since such a function is a fraction whose denominator is invertible
there: invert the denominator modulo the prime, correct the numerator, and the difference between
the function and the resulting constant vanishes at the prime.

## Main results

* `Rigidity.RET.exists_const_ordAtLeast_one_sub` — a function regular at a prime agrees there, to
  first order, with a constant.
-/

open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section


namespace Rigidity.RET

section Residue

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {v : HeightOneSpectrum R}
variable {k : Type*} [Field k] [Algebra k R] [Algebra k K] [IsScalarTower k R K]

/-- **A function of the domain invertible at a prime has an inverse modulo that prime.** -/
theorem exists_mul_sub_one_mem {s : R} (hs : s ∉ v.asIdeal) : ∃ w : R, w * s - 1 ∈ v.asIdeal := by
  haveI hmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  obtain ⟨w, i, hi, hwi⟩ := hmax.exists_inv hs
  refine ⟨w, ?_⟩
  have heq : w * s - 1 = -i := by linear_combination hwi
  rw [heq]
  exact neg_mem hi

/-- **A function regular at a prime agrees there, to first order, with a constant.** -/
theorem exists_const_ordAtLeast_one_sub
    (hk : ∀ b : R, ∃ c : k, b - algebraMap k R c ∈ v.asIdeal)
    {z : K} (hz : OrdAtLeast K v 0 z) :
    ∃ c : k, OrdAtLeast K v 1 (z - algebraMap k K c) := by
  obtain ⟨a, s, hsv, hsz⟩ := exists_den_notMem_of_ord_nonneg K v (ordAtLeast_zero_iff.1 hz)
  obtain ⟨w, hw⟩ := exists_mul_sub_one_mem hsv
  obtain ⟨c, hc⟩ := hk (w * a)
  refine ⟨c, ?_⟩
  -- the numerator of `z - c` vanishes at the prime
  have hmem : a - algebraMap k R c * s ∈ v.asIdeal := by
    have heq : a - algebraMap k R c * s
        = s * (w * a - algebraMap k R c) - a * (w * s - 1) := by ring
    rw [heq]
    exact sub_mem (Ideal.mul_mem_left _ _ hc) (Ideal.mul_mem_left _ _ hw)
  have hs0 : s ≠ 0 := by rintro rfl; exact hsv (Submodule.zero_mem _)
  have hsK : algebraMap R K s ≠ 0 := fun h => hs0 (IsFractionRing.to_map_eq_zero_iff.mp h)
  -- the numerator, as a function, is the denominator times the difference
  have hnum : algebraMap R K (a - algebraMap k R c * s)
      = algebraMap R K s * (z - algebraMap k K c) := by
    rw [map_sub, map_mul, ← hsz, ← IsScalarTower.algebraMap_apply k R K]
    ring
  have hinv : OrdAtLeast K v 0 (algebraMap R K s)⁻¹ := by
    refine ordAtLeast_of_ord_le ?_
    have h1 : 0 ≤ ord K v (algebraMap R K s) := ord_nonneg v s
    have h2 : ¬ 0 < ord K v (algebraMap R K s) := fun h =>
      hsv ((mem_iff_ord_pos (K := K) v hs0).2 h)
    rw [ord_inv]
    omega
  have hnumbound : OrdAtLeast K v 1 (algebraMap R K (a - algebraMap k R c * s)) := by
    rcases eq_or_ne (a - algebraMap k R c * s) 0 with h0 | h0
    · rw [h0, map_zero]
      exact ordAtLeast_zero_fun 1
    · exact ordAtLeast_of_ord_le ((mem_iff_ord_pos (K := K) v h0).1 hmem)
  have hzc : z - algebraMap k K c
      = algebraMap R K (a - algebraMap k R c * s) * (algebraMap R K s)⁻¹ := by
    rw [hnum]
    field_simp
  rw [hzc]
  simpa using hnumbound.mul hinv

end Residue

end Rigidity.RET
