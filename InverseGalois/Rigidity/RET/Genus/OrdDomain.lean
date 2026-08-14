/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.OrdSmul
import InverseGalois.Rigidity.RET.Genus.OrdUltra

/-!
# The order of an element of the ring itself

Computations inside a cover happen in its integral model, not in its function field: the roots of an
equation, their differences, and the products that relate them are all elements of a Dedekind
domain.  Reading the order of such an element through the fraction field each time is noise, so this
file names it and restates the calculus — additivity on products, the ultrametric rules for sums,
invariance under automorphisms fixing the place, vanishing on units — directly for elements of the
domain.

Two facts are specific to the domain and have no counterpart in the fraction field: the order is
never negative, and it is positive exactly at the elements of the prime.  Together they turn "this
element is a unit modulo the prime" into "its order is zero", which is what pins down the terms of
an equation that do not contribute to a ramification count.

## Main results

* `Rigidity.RET.intOrd_mul`, `Rigidity.RET.intOrd_pow`, `Rigidity.RET.intOrd_prod` — additivity.
* `Rigidity.RET.intOrd_eq_zero_of_notMem` — an element outside the prime has order zero.
* `Rigidity.RET.intOrd_sub_of_lt` — a strictly shallower term fixes the order of a difference.
* `Rigidity.RET.intOrd_smul_eq` — invariance under an automorphism fixing the prime.
-/

open IsDedekindDomain Pointwise

noncomputable section

namespace Rigidity.RET

variable {B : Type*} [CommRing B] [IsDedekindDomain B]
variable (K : Type*) [Field K] [Algebra B K] [IsFractionRing B K]
variable {v : HeightOneSpectrum B}

/-- **The order of an element of a Dedekind domain at a height-one prime**: the multiplicity of the
prime in the factorization of the ideal it generates. -/
abbrev intOrd (v : HeightOneSpectrum B) (y : B) : ℤ := ord K v (algebraMap B K y)

variable {K}

omit [IsDedekindDomain B] in
theorem algebraMap_ne_zero_of_ne_zero {y : B} (hy : y ≠ 0) : algebraMap B K y ≠ 0 :=
  fun h => hy (IsFractionRing.injective B K (h.trans (map_zero (algebraMap B K)).symm))

/-- The order of an element of the domain is never negative. -/
theorem intOrd_nonneg (y : B) : 0 ≤ intOrd K v y := ord_nonneg v y

@[simp] theorem intOrd_zero : intOrd K v (0 : B) = 0 := by
  unfold intOrd; simp

@[simp] theorem intOrd_one : intOrd K v (1 : B) = 0 := by
  unfold intOrd; simp

/-- **The order is additive on products.** -/
theorem intOrd_mul {y z : B} (hy : y ≠ 0) (hz : z ≠ 0) :
    intOrd K v (y * z) = intOrd K v y + intOrd K v z := by
  unfold intOrd
  rw [map_mul,
    ord_mul v (algebraMap_ne_zero_of_ne_zero hy) (algebraMap_ne_zero_of_ne_zero hz)]

/-- **The order is multiplied by the exponent on powers.** -/
theorem intOrd_pow {y : B} (hy : y ≠ 0) (j : ℕ) : intOrd K v (y ^ j) = j * intOrd K v y := by
  unfold intOrd
  rw [map_pow, ord_pow v (algebraMap_ne_zero_of_ne_zero hy)]

/-- **The order of a finite product is the sum of the orders.** -/
theorem intOrd_prod {ι : Type*} (s : Finset ι) (g : ι → B) (hg : ∀ i ∈ s, g i ≠ 0) :
    intOrd K v (∏ i ∈ s, g i) = ∑ i ∈ s, intOrd K v (g i) := by
  unfold intOrd
  rw [map_prod]
  exact ord_prod s _ fun i hi => algebraMap_ne_zero_of_ne_zero (hg i hi)

/-- **An element positive at the prime is exactly an element of the prime.** -/
theorem intOrd_pos_iff_mem {y : B} (hy : y ≠ 0) : 0 < intOrd K v y ↔ y ∈ v.asIdeal :=
  (mem_iff_ord_pos (K := K) v hy).symm

/-- **An element outside the prime has order zero.** -/
theorem intOrd_eq_zero_of_notMem {y : B} (h : y ∉ v.asIdeal) : intOrd K v y = 0 := by
  have hy : y ≠ 0 := fun hz => h (hz ▸ v.asIdeal.zero_mem)
  exact le_antisymm (not_lt.mp fun hlt => h ((intOrd_pos_iff_mem hy).mp hlt)) (intOrd_nonneg y)

/-- **A unit has order zero at every prime.** -/
theorem intOrd_eq_zero_of_isUnit {y : B} (hy : IsUnit y) : intOrd K v y = 0 :=
  intOrd_eq_zero_of_notMem fun hmem => v.isPrime.ne_top (v.asIdeal.eq_top_of_isUnit_mem hmem hy)

/-- **The order of a difference is at least the smaller of the two orders.** -/
theorem min_intOrd_le_intOrd_sub {y z : B} (h : y - z ≠ 0) :
    min (intOrd K v y) (intOrd K v z) ≤ intOrd K v (y - z) := by
  unfold intOrd
  rw [map_sub (algebraMap B K)]
  exact min_ord_le_ord_sub (by rw [← map_sub]; exact algebraMap_ne_zero_of_ne_zero h)

/-- **A strictly shallower term fixes the order of a difference.** -/
theorem intOrd_sub_of_lt {y z : B} (hy : y ≠ 0) (h : intOrd K v y < intOrd K v z) :
    intOrd K v (y - z) = intOrd K v y := by
  unfold intOrd
  rw [map_sub]
  exact ord_sub_of_ord_lt (algebraMap_ne_zero_of_ne_zero hy) h

/-- **A strictly shallower term fixes the order of a sum.** -/
theorem intOrd_add_of_lt {y z : B} (hy : y ≠ 0) (h : intOrd K v y < intOrd K v z) :
    intOrd K v (y + z) = intOrd K v y := by
  unfold intOrd
  rw [map_add]
  exact ord_add_of_ord_lt (algebraMap_ne_zero_of_ne_zero hy) h

/-- **The order at a prime is invariant under an automorphism fixing that prime.** -/
theorem intOrd_smul_eq {G : Type*} [Group G] [MulSemiringAction G B] {σ : G}
    (hσ : σ • v.asIdeal = v.asIdeal) (y : B) : intOrd K v (σ • y) = intOrd K v y :=
  ord_smul_eq hσ y

/-! ### Vanishing to a prescribed order -/

/-- Membership in a power of the prime is the zero-safe form of "the order is at least `j`": it
makes no exception for the zero element and is preserved by the automorphisms fixing the prime. -/
theorem mem_pow_iff_le_intOrd {y : B} (hy : y ≠ 0) (j : ℕ) :
    y ∈ v.asIdeal ^ j ↔ (j : ℤ) ≤ intOrd K v y :=
  mem_pow_iff_le_ord (K := K) v hy j

/-- An element vanishing to order at least `j` lies in the `j`-th power of the prime. -/
theorem mem_pow_of_le_intOrd {y : B} {j : ℕ} (h : (j : ℤ) ≤ intOrd K v y) : y ∈ v.asIdeal ^ j := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact Ideal.zero_mem _
  · exact (mem_pow_iff_le_intOrd (K := K) hy j).mpr h

/-- An element of the `j`-th power of the prime which is nonzero has order at least `j`. -/
theorem le_intOrd_of_mem_pow {y : B} (hy : y ≠ 0) {j : ℕ} (h : y ∈ v.asIdeal ^ j) :
    (j : ℤ) ≤ intOrd K v y :=
  (mem_pow_iff_le_intOrd (K := K) hy j).mp h

end Rigidity.RET
