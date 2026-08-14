/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootCover

/-!
# Roots of a monic family are bounded by a polynomial in the parameter

A root of a monic complex polynomial cannot be much larger than its coefficients: if the absolute
value of a root exceeded both one and the sum of the absolute values of the lower coefficients,
the leading term would dominate the rest of the polynomial and the value could not vanish.  This is
the Cauchy bound.

Applied to a monic family of equations over the complex line, whose coefficients are polynomials in
the parameter, the bound says that the roots over a parameter `z` are bounded by a fixed polynomial
in `‖z‖`.  Two consequences matter for the analytic study of the family: the roots stay bounded as
the parameter approaches a degeneracy, so nothing escapes to infinity there, and they grow at most
polynomially as the parameter itself goes to infinity.

## Main results

* `Rigidity.RET.Analytic.exists_bound_eval` — the values of a complex polynomial are bounded by a
  constant times `(1 + ‖z‖)` to its degree.
* `Rigidity.RET.Analytic.norm_le_of_monic_eval_eq_zero` — the Cauchy bound for the roots of a monic
  complex polynomial.
* `Rigidity.RET.Analytic.exists_root_bound` — every root of a monic family over the complex line is
  bounded by a fixed polynomial in the absolute value of the parameter.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

/-! ### Polynomial growth of polynomial values -/

/-- **The values of a complex polynomial grow at most like its degree.** -/
theorem exists_bound_eval (q : Polynomial ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖q.eval z‖ ≤ C * (1 + ‖z‖) ^ q.natDegree := by
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1), ‖q.coeff i‖,
    Finset.sum_nonneg fun i _ => norm_nonneg _, fun z => ?_⟩
  have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow]
  have h1 : ‖z‖ ^ i ≤ (1 + ‖z‖) ^ q.natDegree :=
    le_trans (pow_le_pow_left₀ (norm_nonneg z) (by linarith) i)
      (pow_le_pow_right₀ hz1 (Finset.mem_range_succ_iff.mp hi))
  exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

/-- **A finite sum of polynomial values grows at most polynomially.** -/
theorem exists_bound_sum (q : ℕ → Polynomial ℂ) (s : Finset ℕ) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ z : ℂ, ∑ i ∈ s, ‖(q i).eval z‖ ≤ C * (1 + ‖z‖) ^ d := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, 0, le_refl 0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨C₁, d₁, hC₁, h₁⟩ := ih
    obtain ⟨C₂, hC₂, h₂⟩ := exists_bound_eval (q a)
    refine ⟨C₁ + C₂, max d₁ (q a).natDegree, by linarith, fun z => ?_⟩
    have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have m1 : C₁ * (1 + ‖z‖) ^ d₁ ≤ C₁ * (1 + ‖z‖) ^ max d₁ (q a).natDegree :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz1 (le_max_left _ _)) hC₁
    have m2 : C₂ * (1 + ‖z‖) ^ (q a).natDegree
        ≤ C₂ * (1 + ‖z‖) ^ max d₁ (q a).natDegree :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz1 (le_max_right _ _)) hC₂
    rw [Finset.sum_insert ha, add_mul]
    linarith [h₁ z, h₂ z]

/-! ### The Cauchy bound -/

/-- **The Cauchy bound**: a root of a monic complex polynomial is bounded by one and by the sum of
the absolute values of the lower coefficients. -/
theorem norm_le_of_monic_eval_eq_zero {p : Polynomial ℂ} (hp : p.Monic) (hdeg : 0 < p.natDegree)
    {w : ℂ} (hw : p.eval w = 0) :
    ‖w‖ ≤ max 1 (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) := by
  by_contra hcon
  push_neg at hcon
  have h1 : (1 : ℝ) < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hcon
  have h2 : (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) < ‖w‖ :=
    lt_of_le_of_lt (le_max_right _ _) hcon
  have hsum : (0 : ℂ)
      = (∑ i ∈ Finset.range p.natDegree, p.coeff i * w ^ i) + w ^ p.natDegree := by
    have h := Polynomial.eval_eq_sum_range (p := p) w
    rw [hw, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at h
    exact h
  have hwn : w ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, p.coeff i * w ^ i := by
    linear_combination -hsum
  have hnorm : ‖w‖ ^ p.natDegree
      ≤ (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) * ‖w‖ ^ (p.natDegree - 1) := by
    have he : ‖w‖ ^ p.natDegree = ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * w ^ i‖ := by
      rw [← norm_pow, hwn, norm_neg]
    rw [he, Finset.sum_mul]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ h1.le (by have := Finset.mem_range.mp hi; omega)) (norm_nonneg _)
  have hpm : ‖w‖ ^ (p.natDegree - 1) * ‖w‖ = ‖w‖ ^ p.natDegree := by
    rw [← pow_succ]
    congr 1
    omega
  have hpos : (0 : ℝ) < ‖w‖ ^ (p.natDegree - 1) := pow_pos (by linarith) _
  have hprod := mul_pos (sub_pos.mpr h2) hpos
  have hexp : (‖w‖ - ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) * ‖w‖ ^ (p.natDegree - 1)
      = ‖w‖ ^ p.natDegree
        - (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) * ‖w‖ ^ (p.natDegree - 1) := by
    rw [sub_mul, mul_comm ‖w‖ (‖w‖ ^ (p.natDegree - 1)), hpm]
  rw [hexp] at hprod
  linarith

/-! ### Roots of a family -/

/-- **The roots of a monic family over the complex line are bounded by a polynomial in the
parameter.** -/
theorem exists_root_bound (P : Polynomial (Polynomial ℂ)) (hP : P.Monic)
    (hdeg : 0 < P.natDegree) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
      ∀ z w : ℂ, (spec P z).eval w = 0 → ‖w‖ ≤ C * (1 + ‖z‖) ^ d := by
  obtain ⟨C, d, hC, hbd⟩ := exists_bound_sum (fun i => P.coeff i) (Finset.range P.natDegree)
  refine ⟨1 + C, d, by linarith, fun z w hw => ?_⟩
  have hz1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg z])
  have hA0 : (0 : ℝ) ≤ (1 + ‖z‖) ^ d := le_trans zero_le_one hz1
  have hcoeff : ∀ i, (spec P z).coeff i = (P.coeff i).eval z := fun i => by
    simp [spec, Polynomial.coeff_map]
  have hmain := norm_le_of_monic_eval_eq_zero (spec_monic hP z)
    (by rw [natDegree_spec hP z]; exact hdeg) hw
  rw [natDegree_spec hP z] at hmain
  simp only [hcoeff] at hmain
  refine le_trans hmain (max_le ?_ ?_)
  · have h := mul_le_mul (by linarith : (1 : ℝ) ≤ 1 + C) hz1 zero_le_one
      (by linarith : (0 : ℝ) ≤ 1 + C)
    simpa using h
  · linarith [hbd z]

end Rigidity.RET.Analytic

end
