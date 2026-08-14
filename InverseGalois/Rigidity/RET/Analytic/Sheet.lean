/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootSection
import InverseGalois.Rigidity.RET.Analytic.RootBound
import InverseGalois.Rigidity.RET.Analytic.Extension
import InverseGalois.Rigidity.RET.Analytic.Coeff
import InverseGalois.Rigidity.RET.Analytic.Factor

/-!
# A sheet of the root cover is cut out by an algebraic factor

Selecting, over each parameter outside a finite set, part of the fibre of a monic family of
equations gives a monic polynomial in the second variable whose roots are the selected ones.  If
the selection is locally given by continuous branches — which is what a subset of the root cover
that is open and closed supplies — then that polynomial is the specialization of an honest
algebraic factor of the family.

Three inputs conspire.  A continuous branch of the roots is holomorphic wherever the specialized
equation is separable, so the coefficients of the selection are holomorphic off the finite set.
The Cauchy bound keeps every root, and hence every coefficient of the selection, under control near
the exceptional parameters, so the coefficients extend holomorphically across them; the same bound
makes them grow at most polynomially, so the extensions are polynomials.  Finally a monic
polynomial whose specializations divide those of the family at infinitely many parameters divides
the family.

## Main results

* `Rigidity.RET.Analytic.exists_monic_factor_of_local_sections` — a selection of roots given
  locally by continuous branches is cut out by a monic algebraic factor of the family.
-/

open Polynomial Topology Filter

noncomputable section

namespace Rigidity.RET.Analytic

/-- **A locally continuous selection of roots is cut out by a monic factor of the family.**  The
selection is recorded as a monic polynomial `F z` in the second variable for each parameter `z`
outside the exceptional set; the hypotheses say that it divides the specialized equation and that
it factors locally into continuous branches. -/
theorem exists_monic_factor_of_local_sections
    {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) (hdeg : 0 < P.natDegree)
    {S : Set ℂ} (hS : S.Finite) (hsep : ∀ z ∉ S, (spec P z).Separable)
    (m : ℕ) (F : ℂ → Polynomial ℂ) (hFdvd : ∀ z ∉ S, F z ∣ spec P z)
    (hloc : ∀ z₀ ∉ S, ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ Sᶜ ∧
      ∃ s : Fin m → ℂ → ℂ, (∀ i, ContinuousOn (s i) V) ∧
        (∀ i, ∀ z ∈ V, (spec P z).eval (s i z) = 0) ∧
        (∀ z ∈ V, F z = ∏ i : Fin m, (X - C (s i z)))) :
    ∃ Q : Polynomial (Polynomial ℂ), Q.Monic ∧ Q.natDegree = m ∧ Q ∣ P ∧
      ∀ z ∉ S, spec Q z = F z := by
  classical
  obtain ⟨Cr, d, hCr, hrb⟩ := exists_root_bound P hP hdeg
  -- Off the exceptional set the selection is monic of the expected degree.
  have hFmonic : ∀ z ∉ S, (F z).Monic ∧ (F z).natDegree = m := by
    intro z hz
    obtain ⟨V, hV, hzV, hVS, s, hcont, hroot, hFeq⟩ := hloc z hz
    rw [hFeq z hzV]
    refine ⟨monic_prod_X_sub_C _ _, ?_⟩
    rw [natDegree_prod_X_sub_C]
    simp
  -- The Cauchy bound controls every coefficient of the selection.
  have hFbound : ∀ z ∉ S, ∀ k, ‖(F z).coeff k‖ ≤ (1 + Cr * (1 + ‖z‖) ^ d) ^ m := by
    intro z hz k
    obtain ⟨V, hV, hzV, hVS, s, hcont, hroot, hFeq⟩ := hloc z hz
    rw [hFeq z hzV]
    have hB : (0 : ℝ) ≤ Cr * (1 + ‖z‖) ^ d := by positivity
    have h := norm_coeff_prod_X_sub_C_le hB (fun i => s i z) Finset.univ
      (fun i _ => hrb z (s i z) (hroot i z hzV)) k
    simpa using h
  set g : ℕ → ℂ → ℂ := fun k z => if z ∈ S then 0 else (F z).coeff k with hgdef
  -- Holomorphy off the exceptional set.
  have hgdiff : ∀ k, DifferentiableOn ℂ (g k) Sᶜ := by
    intro k z₀ hz₀
    obtain ⟨V, hV, hzV, hVS, s, hcont, hroot, hFeq⟩ := hloc z₀ hz₀
    have hsdiff : ∀ i, DifferentiableAt ℂ (s i) z₀ := fun i =>
      differentiableAt_of_isRoot hV (hcont i) (fun z hz => hroot i z hz) hzV
        (Polynomial.Separable.aeval_derivative_ne_zero (hsep z₀ hz₀) (hroot i z₀ hzV))
    have hbase : DifferentiableAt ℂ (fun z => (∏ i : Fin m, (X - C (s i z))).coeff k) z₀ :=
      differentiableAt_coeff_prod_X_sub_C Finset.univ s (fun i _ => hsdiff i) k
    have heq : g k =ᶠ[𝓝 z₀] fun z => (∏ i : Fin m, (X - C (s i z))).coeff k := by
      filter_upwards [hV.mem_nhds hzV] with z hz
      simp only [hgdef, if_neg (hVS hz), hFeq z hz]
    exact (hbase.congr_of_eventuallyEq heq).differentiableWithinAt
  -- Local boundedness at each exceptional parameter.
  have hgbdd : ∀ k, ∀ c ∈ S, ∃ C ε : ℝ, 0 < ε ∧
      ∀ z ∈ Metric.ball c ε, z ≠ c → ‖g k z‖ ≤ C := by
    intro k c _
    have hbase : (0 : ℝ) ≤ 1 + Cr * (2 + ‖c‖) ^ d := by
      have := mul_nonneg hCr (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 + ‖c‖) d)
      linarith
    refine ⟨(1 + Cr * (2 + ‖c‖) ^ d) ^ m, 1, one_pos, fun z hz _ => ?_⟩
    by_cases hzS : z ∈ S
    · simp only [hgdef, if_pos hzS, norm_zero]
      exact pow_nonneg hbase m
    · simp only [hgdef, if_neg hzS]
      refine le_trans (hFbound z hzS k) ?_
      have hzn : ‖z‖ ≤ 1 + ‖c‖ := by
        have h1 : dist z c < 1 := Metric.mem_ball.mp hz
        have h2 : ‖z‖ - ‖c‖ ≤ ‖z - c‖ := norm_sub_norm_le z c
        rw [← dist_eq_norm] at h2
        linarith
      have h1 : (1 + ‖z‖) ^ d ≤ (2 + ‖c‖) ^ d :=
        pow_le_pow_left₀ (by positivity) (by linarith) d
      have h2 : Cr * (1 + ‖z‖) ^ d ≤ Cr * (2 + ‖c‖) ^ d := mul_le_mul_of_nonneg_left h1 hCr
      have h3 : (0 : ℝ) ≤ Cr * (1 + ‖z‖) ^ d :=
        mul_nonneg hCr (pow_nonneg (by positivity) d)
      exact pow_le_pow_left₀ (by linarith) (by linarith) m
  -- Polynomial growth at infinity.
  have hgg : ∀ k, ∀ z ∉ S, (0 : ℝ) ≤ ‖z‖ →
      ‖g k z‖ ≤ (1 + Cr) ^ m * (1 + ‖z‖) ^ (d * m) := by
    intro k z hzS _
    simp only [hgdef, if_neg hzS]
    refine le_trans (hFbound z hzS k) ?_
    have hA : (1 : ℝ) ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg z])
    have hA0 : (0 : ℝ) ≤ (1 + ‖z‖) ^ d := le_trans zero_le_one hA
    have hstep : 1 + Cr * (1 + ‖z‖) ^ d ≤ (1 + Cr) * (1 + ‖z‖) ^ d := by nlinarith
    have hnn : (0 : ℝ) ≤ Cr * (1 + ‖z‖) ^ d := mul_nonneg hCr hA0
    have h2 := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + Cr * (1 + ‖z‖) ^ d) hstep m
    rw [mul_pow, ← pow_mul] at h2
    exact h2
  -- Each coefficient is a polynomial in the parameter.
  have hpoly : ∀ k, ∃ q : Polynomial ℂ, ∀ z ∉ S, (F z).coeff k = q.eval z := by
    intro k
    obtain ⟨q, _, hq⟩ := exists_polynomial_of_bounded_of_growth (n := d * m) (R := 0)
      hS (hgdiff k) (hgbdd k) (hgg k)
    refine ⟨q, fun z hz => ?_⟩
    have h := hq z hz
    simpa [hgdef, if_neg hz] using h
  choose q hq using hpoly
  have hspec : ∀ z ∉ S, spec (ofCoeffs m q) z = F z := by
    intro z hz
    obtain ⟨hFm, hFd⟩ := hFmonic z hz
    refine Polynomial.ext fun j => ?_
    rw [coeff_spec_ofCoeffs]
    rcases lt_trichotomy j m with hj | hj | hj
    · rw [if_neg (by omega), if_pos hj, zero_add, ← hq j z hz]
    · subst hj
      rw [if_pos rfl, if_neg (lt_irrefl _), add_zero]
      have hlead := hFm.coeff_natDegree
      rw [hFd] at hlead
      exact hlead.symm
    · rw [if_neg (by omega), if_neg (by omega), add_zero]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  refine ⟨ofCoeffs m q, monic_ofCoeffs m q, natDegree_ofCoeffs m q, ?_, hspec⟩
  refine dvd_of_forall_spec_dvd (monic_ofCoeffs m q) hS.infinite_compl fun z hz => ?_
  rw [hspec z hz]
  exact hFdvd z hz

end Rigidity.RET.Analytic

end
