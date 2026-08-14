/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Coefficients of a product of linear factors

A finite family of complex numbers determines the monic polynomial having exactly those numbers as
its roots.  Two properties of its coefficients are needed to turn a family of analytic roots back
into an algebraic object: the coefficients are bounded in terms of a bound on the roots, and they
depend holomorphically on the roots.

Both are proved by the same induction on the family, peeling off one linear factor at a time.
Multiplying by `X - w` replaces the coefficient in degree `k` by the difference of the coefficient
in degree `k - 1` and `w` times the coefficient in degree `k`; the bound multiplies by `1 + ‖w‖`,
and differentiability is preserved because the new coefficient is a polynomial expression in the
old ones and in `w`.

## Main results

* `Rigidity.RET.Analytic.norm_coeff_prod_X_sub_C_le` — every coefficient of a product of linear
  factors is bounded by `(1 + B) ^ card` when all the roots are bounded by `B`.
* `Rigidity.RET.Analytic.differentiableAt_coeff_prod_X_sub_C` — the coefficients depend
  holomorphically on holomorphically varying roots.
* `Rigidity.RET.Analytic.monic_prod_X_sub_C` and
  `Rigidity.RET.Analytic.natDegree_prod_X_sub_C` — the product is monic of degree the cardinality.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

variable {ι : Type*}

/-- A product of monic linear factors is monic. -/
theorem monic_prod_X_sub_C (s : Finset ι) (w : ι → ℂ) :
    (∏ i ∈ s, (X - C (w i))).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (w i)

/-- A product of monic linear factors has degree the number of factors. -/
theorem natDegree_prod_X_sub_C (s : Finset ι) (w : ι → ℂ) :
    (∏ i ∈ s, (X - C (w i))).natDegree = s.card := by
  rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (w i)]
  simp

/-- **The coefficients of a product of linear factors are bounded by a bound on its roots.** -/
theorem norm_coeff_prod_X_sub_C_le {B : ℝ} (hB : 0 ≤ B) (w : ι → ℂ) (s : Finset ι)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ B) (k : ℕ) :
    ‖(∏ i ∈ s, (X - C (w i))).coeff k‖ ≤ (1 + B) ^ s.card := by
  classical
  induction s using Finset.induction generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, Polynomial.coeff_one]
    split <;> simp
  | @insert a s ha ih =>
    have hws : ∀ i ∈ s, ‖w i‖ ≤ B := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hwa : ‖w a‖ ≤ B := hw a (Finset.mem_insert_self a s)
    have hpos : (0 : ℝ) ≤ (1 + B) ^ s.card := by positivity
    have hprod : (∏ i ∈ insert a s, (X - C (w i)))
        = (∏ i ∈ s, (X - C (w i))) * (X - C (w a)) := by
      rw [Finset.prod_insert ha, mul_comm]
    rw [hprod, Finset.card_insert_of_notMem ha, pow_succ]
    match k with
    | 0 =>
      rw [Polynomial.mul_coeff_zero]
      have h0 : ((X : Polynomial ℂ) - C (w a)).coeff 0 = -w a := by simp
      rw [h0, norm_mul, norm_neg]
      have h1 : ‖(∏ i ∈ s, (X - C (w i))).coeff 0‖ * ‖w a‖ ≤ (1 + B) ^ s.card * B :=
        mul_le_mul (ih hws 0) hwa (norm_nonneg _) hpos
      nlinarith [hpos, norm_nonneg (w a)]
    | (k + 1) =>
      rw [Polynomial.coeff_mul_X_sub_C]
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_mul]
      have h1 := ih hws k
      have h2 : ‖(∏ i ∈ s, (X - C (w i))).coeff (k + 1)‖ * ‖w a‖ ≤ (1 + B) ^ s.card * B :=
        mul_le_mul (ih hws (k + 1)) hwa (norm_nonneg _) hpos
      nlinarith

/-- **The coefficients of a product of linear factors depend holomorphically on the roots.** -/
theorem differentiableAt_coeff_prod_X_sub_C (s : Finset ι) (w : ι → ℂ → ℂ) {z₀ : ℂ}
    (hw : ∀ i ∈ s, DifferentiableAt ℂ (w i) z₀) (k : ℕ) :
    DifferentiableAt ℂ (fun z => (∏ i ∈ s, (X - C (w i z))).coeff k) z₀ := by
  classical
  induction s using Finset.induction generalizing k with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiableAt_const _
  | @insert a s ha ih =>
    have hws : ∀ i ∈ s, DifferentiableAt ℂ (w i) z₀ := fun i hi =>
      hw i (Finset.mem_insert_of_mem hi)
    have hwa : DifferentiableAt ℂ (w a) z₀ := hw a (Finset.mem_insert_self a s)
    have hprod : ∀ z : ℂ, (∏ i ∈ insert a s, (X - C (w i z)))
        = (∏ i ∈ s, (X - C (w i z))) * (X - C (w a z)) := fun z => by
      rw [Finset.prod_insert ha, mul_comm]
    simp only [hprod]
    match k with
    | 0 =>
      have hrw : (fun z => ((∏ i ∈ s, (X - C (w i z))) * (X - C (w a z))).coeff 0)
          = fun z => (∏ i ∈ s, (X - C (w i z))).coeff 0 * -w a z := by
        funext z
        rw [Polynomial.mul_coeff_zero]
        simp
      rw [hrw]
      exact (ih hws 0).mul hwa.neg
    | (k + 1) =>
      have hrw : (fun z => ((∏ i ∈ s, (X - C (w i z))) * (X - C (w a z))).coeff (k + 1))
          = fun z => (∏ i ∈ s, (X - C (w i z))).coeff k
              - (∏ i ∈ s, (X - C (w i z))).coeff (k + 1) * w a z := by
        funext z
        exact Polynomial.coeff_mul_X_sub_C
      rw [hrw]
      exact (ih hws k).sub ((ih hws (k + 1)).mul hwa)

end Rigidity.RET.Analytic

end
