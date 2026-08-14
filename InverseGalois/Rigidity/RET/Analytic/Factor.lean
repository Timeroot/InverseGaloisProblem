/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootCover

/-!
# Recognising a factor of a two-variable polynomial from its specializations

A monic divisor of a family of equations can be recognised one parameter at a time.  Division with
remainder by a monic polynomial is available over any commutative ring, and it commutes with
specialization, so if the specialization of a monic `Q` divides the specialization of `P` for
infinitely many values of the parameter, the remainder `P %ₘ Q` specializes to zero infinitely
often; its coefficients are then polynomials with infinitely many roots, hence zero.

The candidate divisor itself is built from prescribed lower coefficients, with a leading term
`X ^ m` supplied to make it monic of the intended degree.

## Main results

* `Rigidity.RET.Analytic.ofCoeffs` — the monic polynomial with prescribed lower coefficients, with
  its coefficient, degree and specialization formulas.
* `Rigidity.RET.Analytic.dvd_of_forall_spec_dvd` — a monic polynomial dividing infinitely many
  specializations divides the family.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

/-! ### Assembling a monic family from its coefficients -/

/-- The monic two-variable polynomial of degree `m` with prescribed coefficients below `m`. -/
def ofCoeffs (m : ℕ) (p : ℕ → Polynomial ℂ) : Polynomial (Polynomial ℂ) :=
  X ^ m + ∑ k ∈ Finset.range m, C (p k) * X ^ k

theorem coeff_ofCoeffs (m : ℕ) (p : ℕ → Polynomial ℂ) (j : ℕ) :
    (ofCoeffs m p).coeff j = (if j = m then 1 else 0) + (if j < m then p j else 0) := by
  rw [ofCoeffs, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff]
  congr 1
  rw [Finset.sum_congr rfl fun k _ => by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]]
  rw [Finset.sum_ite_eq (Finset.range m) j p]
  simp only [Finset.mem_range]

theorem natDegree_ofCoeffs_le (m : ℕ) (p : ℕ → Polynomial ℂ) :
    (ofCoeffs m p).natDegree ≤ m := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_ofCoeffs, if_neg (by omega), if_neg (by omega), add_zero]

theorem coeff_ofCoeffs_self (m : ℕ) (p : ℕ → Polynomial ℂ) : (ofCoeffs m p).coeff m = 1 := by
  rw [coeff_ofCoeffs, if_pos rfl, if_neg (lt_irrefl m), add_zero]

theorem monic_ofCoeffs (m : ℕ) (p : ℕ → Polynomial ℂ) : (ofCoeffs m p).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one m (natDegree_ofCoeffs_le m p)
    (coeff_ofCoeffs_self m p)

theorem natDegree_ofCoeffs (m : ℕ) (p : ℕ → Polynomial ℂ) : (ofCoeffs m p).natDegree = m :=
  le_antisymm (natDegree_ofCoeffs_le m p)
    (Polynomial.le_natDegree_of_ne_zero (by rw [coeff_ofCoeffs_self]; exact one_ne_zero))

theorem coeff_spec_ofCoeffs (m : ℕ) (p : ℕ → Polynomial ℂ) (z : ℂ) (j : ℕ) :
    (spec (ofCoeffs m p) z).coeff j
      = (if j = m then 1 else 0) + (if j < m then (p j).eval z else 0) := by
  show ((ofCoeffs m p).map (Polynomial.evalRingHom z)).coeff j = _
  rw [Polynomial.coeff_map, coeff_ofCoeffs]
  split_ifs <;> simp

/-! ### Recognising a divisor from its specializations -/

/-- **A monic family whose specializations divide those of another family at infinitely many
parameters divides it.** -/
theorem dvd_of_forall_spec_dvd {P Q : Polynomial (Polynomial ℂ)} (hQ : Q.Monic)
    {T : Set ℂ} (hT : T.Infinite) (h : ∀ z ∈ T, spec Q z ∣ spec P z) : Q ∣ P := by
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hQ]
  have hspec : ∀ z ∈ T, spec (P %ₘ Q) z = 0 := by
    intro z hz
    show (P %ₘ Q).map (Polynomial.evalRingHom z) = 0
    rw [Polynomial.map_modByMonic _ hQ]
    exact (Polynomial.modByMonic_eq_zero_iff_dvd (spec_monic hQ z)).2 (h z hz)
  refine Polynomial.ext fun j => ?_
  have hzero : (P %ₘ Q).coeff j = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ (hT.mono ?_)
    intro z hz
    have h2 : ((P %ₘ Q).coeff j).eval z = (spec (P %ₘ Q) z).coeff j := by
      show _ = ((P %ₘ Q).map (Polynomial.evalRingHom z)).coeff j
      rw [Polynomial.coeff_map]
      rfl
    show ((P %ₘ Q).coeff j).eval z = 0
    rw [h2, hspec z hz, Polynomial.coeff_zero]
  rw [hzero, Polynomial.coeff_zero]

end Rigidity.RET.Analytic

end
