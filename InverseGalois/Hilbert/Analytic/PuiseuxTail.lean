/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.BranchAnalytic
import InverseGalois.Hilbert.Analytic.LaurentInfra
import InverseGalois.Hilbert.Analytic.ComplexSeparableReduction
import InverseGalois.Hilbert.Analytic.RamifiedSection

/-!
# Puiseux tail bounds for complex algebraic branches at infinity

This file develops analytic theory toward the *tail-bound* half of
`DorgeBauer.real_branch_full_holomorphic_continuation` — the uniform bound of a holomorphic
algebraic branch minus its principal part on complex spheres at infinity.

The continuation half (existence of the single-valued holomorphic branch `H` on the tail
balls, agreeing with the real branch) is already available as
`DorgeBauer.real_branch_holo_continuation_tail`.

Here we build reusable pieces:

* `complex_poly_eval_norm_le` — a polynomial-growth bound for evaluation of a complex
  polynomial (the complex analogue of `DorgeBauer.real_poly_eval_abs_le`).
* `complex_root_branch_poly_growth` — a complex root `H z` of the monic family grows at most
  polynomially in `‖z‖` (the complex analogue of `DorgeBauer.real_root_branch_poly_growth`),
  the growth input for the removable-singularity / Laurent step of the Puiseux expansion.
-/

open Filter Topology

namespace DorgeBauer

/-
**Polynomial-growth bound for a complex polynomial evaluation.**  The complex analogue
of `real_poly_eval_abs_le`: the value `‖p.eval z‖` is bounded by the sum of coefficient
norms times `(1 + ‖z‖) ^ (deg p)`.
-/
lemma complex_poly_eval_norm_le (p : Polynomial ℂ) (z : ℂ) :
    ‖p.eval z‖ ≤ (∑ j ∈ Finset.range (p.natDegree + 1), ‖p.coeff j‖) * (1 + ‖z‖) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  refine' le_trans (norm_sum_le _ _) _
  norm_num [Finset.sum_mul _ _ _]
  exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg z]) _ |> le_trans <|
      pow_le_pow_right₀ (by linarith [norm_nonneg z]) <| Finset.mem_range_succ_iff.mp hi)
    (norm_nonneg _)

/-
**Polynomial growth of a complex algebraic branch.**  A complex root `H z` of the monic
specialization `P(z, ·)` grows at most polynomially in `‖z‖`: there are constants `C ≥ 0`
and `N` (depending only on `P`) with `‖H z‖ ≤ C · (1 + ‖z‖) ^ N` for all `z ∈ S`.  This is
the uniform Cauchy root bound applied along the complex branch and is the complex analogue of
`real_root_branch_poly_growth`; it is the growth input controlling the pole order of the
substituted branch at infinity in the Puiseux/Laurent expansion.
-/
lemma complex_root_branch_poly_growth
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic) (hP_deg : 1 ≤ P.natDegree)
    (S : Set ℂ) (H : ℂ → ℂ)
    (hroot : ∀ z ∈ S, (P.map (evalIntPolyComplex z)).eval (H z) = 0) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ z ∈ S, ‖H z‖ ≤ C * (1 + ‖z‖) ^ N := by
  -- Let's choose $N$ to be the maximum degree of the coefficients of $P$.
  set N := Finset.sup (Finset.range P.natDegree) (fun i => ((P.coeff i).map (Int.castRingHom ℂ)).natDegree) with hN_def
  -- By the properties of the polynomial $P$, we know that its coefficients are bounded by some constant $C$.
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ z ∈ S, ∀ i < P.natDegree,
        ‖((P.coeff i).map (Int.castRingHom ℂ)).eval z‖ ≤ C * (1 + ‖z‖) ^ N := by
    have h_coeff_bound : ∀ i < P.natDegree, ∃ C_i : ℝ, ∀ z ∈ S,
        ‖((P.coeff i).map (Int.castRingHom ℂ)).eval z‖ ≤ C_i * (1 + ‖z‖) ^ N := by
      intro i hi
      use ∑ j ∈ Finset.range ((Polynomial.map (Int.castRingHom ℂ) (P.coeff i)).natDegree + 1),
        ‖((Polynomial.map (Int.castRingHom ℂ) (P.coeff i)).coeff j)‖
      intro z hz
      have h_coeff_bound :
          ‖((P.coeff i).map (Int.castRingHom ℂ)).eval z‖ ≤
            (∑ j ∈ Finset.range ((Polynomial.map (Int.castRingHom ℂ) (P.coeff i)).natDegree + 1),
              ‖((Polynomial.map (Int.castRingHom ℂ) (P.coeff i)).coeff j)‖) *
              (1 + ‖z‖) ^ ((Polynomial.map (Int.castRingHom ℂ) (P.coeff i)).natDegree) := by
        convert complex_poly_eval_norm_le _ _ using 1
      exact h_coeff_bound.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith [norm_nonneg z])
          (Finset.le_sup (f := fun i => Polynomial.natDegree (Polynomial.map (Int.castRingHom ℂ) (P.coeff i)))
            (Finset.mem_range.mpr hi)))
        (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    choose! C hC using h_coeff_bound
    exact ⟨∑ i ∈ Finset.range P.natDegree, |C i|, fun z hz i hi =>
      le_trans (hC i hi z hz) (mul_le_mul_of_nonneg_right
        (le_trans (le_abs_self _)
          (Finset.single_le_sum (fun i _ => abs_nonneg (C i)) (Finset.mem_range.mpr hi)))
        (by positivity))⟩
  -- Apply the Cauchy root bound to the polynomial $P(z, \cdot)$.
  have h_cauchy : ∀ z ∈ S, ‖H z‖ ≤ 1 + P.natDegree * C * (1 + ‖z‖) ^ N := by
    intro z hz
    have h_cauchy : ∀ i < P.natDegree, ‖((P.map (evalIntPolyComplex z)).coeff i)‖ ≤ C * (1 + ‖z‖) ^ N := by
      intro i hi
      specialize hC z hz i hi
      simp_all [Polynomial.coeff_map]
      convert hC using 1
    have := @cauchy_root_bound_max (Polynomial.map (evalIntPolyComplex z) P)
    simp_all [mul_assoc]
    exact this (by exact Polynomial.Monic.map (evalIntPolyComplex z) hP_monic) (hroot z hz) h_cauchy
  refine' ⟨1 + P.natDegree * |C|, N, _, _⟩
  · positivity
  · intro z hz
    specialize h_cauchy z hz
    cases abs_cases C <;>
      nlinarith [show 0 ≤ (P.natDegree : ℝ) * (1 + ‖z‖) ^ N by positivity,
        show (1 + ‖z‖) ^ N ≥ 1 by exact one_le_pow₀ (by linarith [norm_nonneg z])]

/-
**The continuation `H` is a genuine root of the complex family on each tail ball.**

The holomorphic continuation `H` of the real branch `g` agrees with `g` on the real ray
(`hagree`) where `g` is a root of the real family (`hroot`).  Since the composed function
`z ↦ (P.map (evalIntPolyComplex z)).eval (H z)` is holomorphic on the ball `ball x (x/2)`
and vanishes on the real segment through its centre (an accumulation set), the identity
theorem forces it to vanish on the whole ball.  This is the analytic continuation of the
algebraic identity off the real axis, and the first step toward the Puiseux analysis.
-/
lemma H_root_on_ball
    (P : Polynomial (Polynomial ℤ))
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (T₁ : ℝ) (H : ℂ → ℂ) (hT1a : 2 * (T₀ : ℝ) ≤ T₁) (hT1b : (2 : ℝ) ≤ T₁)
    (hcont : ∀ x : ℝ, T₁ ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2)))
    (hagree : ∀ y : ℝ, T₁ / 2 ≤ y → H (y : ℂ) = (g y : ℂ))
    (x : ℝ) (hx : T₁ ≤ x) :
    ∀ z ∈ Metric.ball (x : ℂ) (x / 2),
      (P.map (evalIntPolyComplex z)).eval (H z) = 0 := by
  have hF_root_real : ∀ y : ℝ, x - x / 2 < y ∧ y < x + x / 2 →
      (P.map (evalIntPolyComplex (y : ℂ))).eval (H (y : ℂ)) = 0 := by
    intros y hy
    rw [hagree y (by linarith)]
    convert congr_arg ((↑) : ℝ → ℂ)
        (hroot y (by linarith [show (T₀ : ℝ) ≤ y by linarith])) using 1
    norm_num [evalIntPolyComplex_ofReal]
  have hF_zero : AnalyticOnNhd ℂ (fun z : ℂ => (P.map (evalIntPolyComplex z)).eval (H z))
      (Metric.ball (x : ℂ) (x / 2)) := by
    apply_rules [DifferentiableOn.analyticOnNhd, Metric.isOpen_ball]
    have hF_zero : DifferentiableOn ℂ (fun z : ℂ => (P.map (evalIntPolyComplex z)).eval (H z))
        (Metric.ball (x : ℂ) (x / 2)) := by
      have hH_diff : DifferentiableOn ℂ H (Metric.ball (x : ℂ) (x / 2)) := by
        exact hcont x hx |> fun h => h.differentiableOn
      convert (evalIntPolyComplex_eval_contDiff P |> ContDiff.differentiable <| by norm_num) |>
        Differentiable.comp_differentiableOn <| differentiableOn_id.prodMk hH_diff using 1
    exact hF_zero
  apply hF_zero.eqOn_zero_of_preconnected_of_frequently_eq_zero
  exact convex_ball _ _ |> Convex.isPreconnected
  exact Metric.mem_ball_self (by linarith)
  rw [Metric.nhdsWithin_basis_ball.frequently_iff]
  intro ε ε_pos
  refine' ⟨↑ (x + Min.min ε (x / 2) / 2), _, _⟩ <;> norm_num
  · refine ⟨?_, ?_⟩
    · rw [abs_of_nonneg (by linarith [show 0 ≤ min ε (x / 2) by exact le_min ε_pos.le (by linarith)])]
      linarith [min_le_left ε (x / 2), min_le_right ε (x / 2)]
    · linarith [show 0 < min ε (x / 2) by exact lt_min ε_pos (by linarith)]
  · have hmin_pos : 0 < Min.min ε (x / 2) := lt_min ε_pos (by linarith)
    convert hF_root_real (x + Min.min ε (x / 2) / 2)
      ⟨by linarith, by linarith [min_le_left ε (x / 2), min_le_right ε (x / 2)]⟩ using 1
    norm_num

/-
**Polynomial growth of the continuation on the tail spheres.**

Combining `H_root_on_ball` (H is a root of the complex family on the balls) with
`complex_root_branch_poly_growth` (a complex algebraic branch grows at most polynomially),
the continuation `H` obeys a uniform bound `‖H z‖ ≤ C · (1 + ‖z‖) ^ N` on every tail sphere
`sphere x (x/2)` (x ≥ T₁), since each such sphere lies in the closure of `ball x (x/2)`
where `H` is a root of the family.  This is the growth input controlling the pole order of
the branch at infinity in the Puiseux/Laurent step.
-/
lemma H_poly_growth_on_spheres
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic) (hP_deg : 1 ≤ P.natDegree)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (T₁ : ℝ) (H : ℂ → ℂ) (hT1a : 2 * (T₀ : ℝ) ≤ T₁) (hT1b : (2 : ℝ) ≤ T₁)
    (hcont : ∀ x : ℝ, T₁ ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2)))
    (hagree : ∀ y : ℝ, T₁ / 2 ≤ y → H (y : ℂ) = (g y : ℂ)) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
      ∀ x : ℝ, T₁ ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2), ‖H z‖ ≤ C * (1 + ‖z‖) ^ N := by
  -- By `H_root_on_ball`, `H` is a root of the complex family on each `closedBall (x : ℂ) (x / 2)` for `x ≥ T₁`.
  have hH_root : ∀ x : ℝ, T₁ ≤ x → ∀ z ∈ Metric.closedBall (x : ℂ) (x / 2),
      (P.map (evalIntPolyComplex z)).eval (H z) = 0 := by
    intros x hx z hz
    have hH_root : ∀ z ∈ Metric.ball (x : ℂ) (x / 2), (P.map (evalIntPolyComplex z)).eval (H z) = 0 := by
      apply H_root_on_ball P T₀ g hroot T₁ H hT1a hT1b hcont hagree x hx
    have h_cont : ContinuousOn (fun z => (P.map (evalIntPolyComplex z)).eval (H z))
        (Metric.closedBall (x : ℂ) (x / 2)) := by
      have h_cont : ContinuousOn H (Metric.closedBall (x : ℂ) (x / 2)) := by
        convert hcont x hx |> DiffContOnCl.continuousOn using 1
        rw [closure_ball _ (by linarith)]
      have h_cont : ContinuousOn (fun p : ℂ × ℂ => (P.map (evalIntPolyComplex p.1)).eval p.2)
          (Metric.closedBall (x : ℂ) (x / 2) ×ˢ Set.univ) := by
        convert evalIntPolyComplex_eval_contDiff P |> ContDiff.continuous |> Continuous.continuousOn using 1
      exact h_cont.comp (continuousOn_id.prodMk ‹_›) fun z hz => ⟨hz, Set.mem_univ _⟩
    have h_cont : ∀ z ∈ Metric.closedBall (x : ℂ) (x / 2),
        (P.map (evalIntPolyComplex z)).eval (H z) = 0 := by
      intro z hz
      have h_seq : ∃ seq : ℕ → ℂ, (∀ n, seq n ∈ Metric.ball (x : ℂ) (x / 2)) ∧
          Filter.Tendsto seq Filter.atTop (nhds z) := by
        have h_seq : z ∈ closure (Metric.ball (x : ℂ) (x / 2)) := by
          rw [closure_ball] <;> norm_num [show x ≠ 0 by linarith] at *
          simp_all only
        rwa [mem_closure_iff_seq_limit] at h_seq
      obtain ⟨seq, hseq₁, hseq₂⟩ := h_seq
      refine tendsto_nhds_unique (h_cont.continuousWithinAt hz |> fun h =>
          h.tendsto.comp <| Filter.tendsto_inf.mpr ⟨hseq₂, Filter.tendsto_principal.mpr <|
            Filter.Eventually.of_forall fun n => by
              simpa using hseq₁ n |> fun h => Metric.mem_closedBall.mpr <| le_of_lt h⟩)
        (tendsto_const_nhds.congr' ?_)
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      simp_all only [Metric.mem_closedBall, Metric.mem_ball, Function.comp_apply]
    exact h_cont z hz
  obtain ⟨C, N, hC, hCbound⟩ := DorgeBauer.complex_root_branch_poly_growth P hP_monic hP_deg
    { z : ℂ | ∃ x : ℝ, T₁ ≤ x ∧ z ∈ Metric.closedBall (x : ℂ) (x / 2) } H
    (fun z ⟨x, hx₁, hx₂⟩ => hH_root x hx₁ z hx₂)
  exact ⟨C, N, hC, fun x hx z hz => hCbound z ⟨x, hx, Metric.sphere_subset_closedBall hz⟩⟩

/-
**Removable-singularity factorisation of a finite-order pole.**

If `F` is holomorphic on a punctured disk `{ w | 0 < ‖w‖ < ρ }` and obeys a finite-order pole
bound `‖F w‖ ≤ Cf / ‖w‖ ^ Kf`, then `w ↦ w ^ Kf · F w` is bounded near `0`, so Riemann's
removable-singularity theorem produces a genuinely holomorphic `G` on the *full* disk
`ball 0 ρ` with `F w = G w / w ^ Kf` on the punctured disk.  This is the analytic core of the
convergent-Laurent step: `G` then has an ordinary convergent power series, whose first `Kf`
coefficients form the finite principal part of `F`.
-/
lemma removable_pole_factor
    (ρ Cf : ℝ) (Kf : ℕ) (F : ℂ → ℂ)
    (hρ : 0 < ρ) (_hCf : 0 ≤ Cf)
    (hFan : AnalyticOnNhd ℂ F {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < ρ})
    (hFgrow : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → ‖F w‖ ≤ Cf / ‖w‖ ^ Kf) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) ρ) ∧
      (∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → F w = G w / w ^ Kf) := by
  refine' ⟨_, _, _⟩
  exact Function.update (fun w => w ^ Kf * F w) 0 (limUnder (nhdsWithin 0 { 0 } ᶜ) (fun w => w ^ Kf * F w))
  · refine' DifferentiableOn.analyticOnNhd _ (Metric.isOpen_ball)
    refine' Complex.differentiableOn_update_limUnder_of_bddAbove _ _ _
    · exact Metric.ball_mem_nhds _ hρ
    · refine' DifferentiableOn.mul (differentiableOn_pow _) (hFan.differentiableOn.mono _)
      exact fun x hx => ⟨norm_pos_iff.mpr hx.2, by simpa using hx.1⟩
    · refine' ⟨Cf, Set.forall_mem_image.2 fun w hw => _⟩
      simp_all
      exact le_trans (mul_le_mul_of_nonneg_left (hFgrow w hw.2 hw.1) (by positivity))
        (by rw [mul_div_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hw.2))])
  · intro w hw₁ hw₂
    rw [Function.update_of_ne (by simp_all only [norm_pos_iff, ne_eq, not_false_eq_true])]
    rw [mul_div_cancel_left₀ _ (pow_ne_zero _ (by simp_all only [norm_pos_iff, ne_eq, not_false_eq_true]))]

/-
**`cpow` term identity for the Puiseux substitution.**

For `z` in the right half-plane (`0 < z.re`) and `e ≥ 1`, writing `w = z⁻¹ ^ (1/e)`, the ratio
of natural powers `w^j / w^Kf` equals `z ^ ((Kf - j)/e)` (a real exponent, as a complex power).
This is the algebraic core of re-expressing the `w`-Laurent expansion as a `z`-Puiseux one.
-/
lemma laurent_cpow_term (z : ℂ) (hz : 0 < z.re) (e : ℕ) (_he : 1 ≤ e) (j Kf : ℕ) :
    (z⁻¹ ^ ((e : ℂ)⁻¹)) ^ j / (z⁻¹ ^ ((e : ℂ)⁻¹)) ^ Kf
      = z ^ ((((Kf : ℝ) - j) / e : ℝ) : ℂ) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num at hz
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_nat_mul]
  rw [Complex.cpow_def_of_ne_zero, Complex.cpow_def_of_ne_zero] <;> norm_num [hz0]
  rw [← Complex.exp_sub, Complex.log_inv]
  ring_nf
  · rw [Complex.cpow_def_of_ne_zero hz0]
    ring_nf
  · grind only [Complex.arg_eq_pi_iff]

/-
**Division/substitution identity.**

Algebraic manipulation turning a Taylor expansion of `G(w)` (with `w = z⁻¹ ^ (1/e)`) divided by
`w^Kf` into a `z`-Puiseux sum with real exponents `(Kf - m)/e`.
-/
lemma laurent_sphere_identity (e Kf n : ℕ) (he : 1 ≤ e) (c : ℕ → ℂ) (Rw Gval : ℂ)
    (z : ℂ) (hz : 0 < z.re)
    (hG : Gval = (∑ m ∈ Finset.range n, c m * (z⁻¹ ^ ((e : ℂ)⁻¹)) ^ m)
        + (z⁻¹ ^ ((e : ℂ)⁻¹)) ^ n * Rw) :
    Gval / (z⁻¹ ^ ((e : ℂ)⁻¹)) ^ Kf
      = (∑ m ∈ Finset.range n, c m * z ^ ((((Kf : ℝ) - m) / e : ℝ) : ℂ))
        + z ^ ((((Kf : ℝ) - n) / e : ℝ) : ℂ) * Rw := by
  rw [hG, add_div, Finset.sum_div]
  grind only [laurent_cpow_term, #ad38, #c8bc]

/-
**An analytic function whose high Taylor coefficients vanish is a polynomial.**

If `G` is analytic on `ball 0 ρ` and `iteratedDeriv m G 0 = 0` for all `m > Kf`, then on the
whole ball `G` equals its degree-`≤ Kf` Taylor polynomial.
-/
lemma laurent_G_poly_of_vanishing (ρ : ℝ) (_hρ : 0 < ρ) (G : ℂ → ℂ) (Kf : ℕ)
    (hG : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) ρ))
    (hvan : ∀ m : ℕ, Kf < m → iteratedDeriv m G 0 = 0) :
    ∀ w : ℂ, ‖w‖ < ρ →
      G w = ∑ m ∈ Finset.range (Kf + 1),
        (iteratedDeriv m G 0 / (m.factorial : ℂ)) * w ^ m := by
  intro w hw
  have := @Complex.taylorSeries_eq_on_ball
  specialize this (show DifferentiableOn ℂ G (Metric.ball 0 ρ) from hG.differentiableOn)
    (show w ∈ Metric.ball 0 ρ from by simpa using hw)
  rw [← this, tsum_eq_sum]
  · exact Finset.sum_congr rfl fun n hn => by simp [div_eq_inv_mul, mul_comm, mul_left_comm]
  · intro n hn
    rw [hvan n (by simpa using hn)]
    simp

/-
**Ramified single-valued root section on a punctured disk (monodromy core).**

This is the *deep* content of `monodromy_ramification_index`, isolated so that the
finite-order pole bound becomes provable glue (see `root_pole_bound`).

The holomorphic branch `H` is defined and single-valued only on the tail balls
`ball x (x/2)` strung along the positive real axis; it is a root of the algebraic family
`P.map (evalIntPolyComplex z)`.  Continuing `H` around the (non-simply-connected) annulus
at infinity `{ z | R < ‖z‖ }` permutes the finitely many root branches, and the monodromy
of the generator of `π₁ ≃ ℤ` is a permutation of finite order `e` (the *ramification
index*).  Trivializing this monodromy via the `e`-fold covering `w ↦ w⁻ᵉ` yields a genuinely
**single-valued** holomorphic function `F` on a punctured disk `{ w | 0 < ‖w‖ < ρ }` around
the origin.  Two facts are recorded here:

* `F` is a genuine root of the specialised family at `z = (w⁻¹) ^ e` (the covering-space
  relation, pulled back through `w ↦ w⁻ᵉ`);
* on the tail spheres `F (z⁻¹ ^ (1/e)) = H z` (the substitution relation).

**Ramified single-valued root section over a *separable* covering (pure monodromy core).**

With separability supplied as a hypothesis — so `DorgeBauer.rootProj` is a genuine covering
map over the annulus at infinity `{ z | B < ‖z‖ }` (`DorgeBauer.rootProj_isCoveringMapOn`) —
this is the pure fundamental-group / covering-space content of `ramified_root_section`,
stripped of the algebraic squarefree reduction (which is now
`ComplexSeparableReduction.exists_complex_separable_reduction`, a proved lemma). -/
lemma separable_ramified_root_section
    (Q : Polynomial (Polynomial ℤ)) (hQ_monic : Q.Monic) (B : ℝ) (hB : 1 ≤ B)
    (hQsep : ∀ z : ℂ, B < ‖z‖ → (Q.map (evalIntPolyComplex z)).Separable)
    (T₁ : ℝ) (H : ℂ → ℂ) (hT1B : 2 * B < T₁)
    (hcont : ∀ x : ℝ, T₁ ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2)))
    (hHroot : ∀ x : ℝ, T₁ ≤ x → ∀ z ∈ Metric.ball (x : ℂ) (x / 2),
        (Q.map (evalIntPolyComplex z)).eval (H z) = 0) :
    ∃ (e : ℕ) (ρ : ℝ) (F : ℂ → ℂ) (Tr : ℝ),
      1 ≤ e ∧ 0 < ρ ∧ B < Tr ∧ T₁ ≤ Tr ∧
      AnalyticOnNhd ℂ F {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < ρ} ∧
      (∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ →
          (Q.map (evalIntPolyComplex ((w⁻¹) ^ e))).eval (F w) = 0) ∧
      (∀ x : ℝ, Tr ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
          H z = F (z⁻¹ ^ ((e : ℂ)⁻¹))) := by
  --This follows from the fact that the branch `H` matches `g` on the positive real axis and `g` is periodic with period `2 * Real.pi * Complex.I * e`.
  obtain ⟨e, g, he, hg⟩ := DorgeBauer.exists_periodic_exp_lift Q hQ_monic B hB hQsep (Complex.log (T₁ : ℂ)) (by
    rw [Complex.log_re]
    norm_num
    exact Real.log_lt_log (by linarith) (by linarith)) (H (T₁ : ℂ)) (by
    convert hHroot T₁ le_rfl (T₁ : ℂ) _ using 1 <;> norm_num [Complex.exp_log, show T₁ ≠ 0 by linarith]
    linarith)
  refine' ⟨e, Real.exp (- (Real.log B) / e), fun w => g (- (e : ℂ) * Complex.log w), T₁, he, _, _, _, _, _⟩
  · positivity
  · linarith
  · linarith
  · -- Apply `root_comp_holomorphic` with the given conditions.
    have h_analytic : AnalyticOnNhd ℂ (fun w => g (-(e : ℂ) * Complex.log w))
        {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < Real.exp (-(Real.log B) / e)} := by
      have hφ : DifferentiableOn ℂ (fun w => (w⁻¹) ^ e)
          {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < Real.exp (-(Real.log B) / e)} := by
        exact DifferentiableOn.pow (differentiableOn_id.inv fun w hw => by
          simp_all only [Metric.mem_ball, norm_pos_iff, ne_eq, Set.mem_setOf_eq, id_eq,
            not_false_eq_true]) _
      have hF : ContinuousOn (fun w => g (-(e : ℂ) * Complex.log w))
          {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < Real.exp (-(Real.log B) / e)} := by
        convert DorgeBauer.periodic_log_comp_continuous g B hB e he hg.1 hg.2.2.2 using 1
      have hroot : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < Real.exp (-(Real.log B) / e) →
          (Q.map (evalIntPolyComplex ((w⁻¹) ^ e))).eval (g (-(e : ℂ) * Complex.log w)) = 0 := by
        intros w hw_pos hw_lt
        have h_exp : Complex.exp (-(e : ℂ) * Complex.log w) = (w⁻¹) ^ e := by
          have := Complex.exp_int_mul (-Complex.log w) e
          simp_all [Complex.exp_neg, Complex.exp_log]
        rw [← h_exp, hg.2.2.1]
        have := Real.log_lt_log hw_pos hw_lt
        norm_num [Complex.log_re] at *
        rw [lt_div_iff₀] at this <;> first | positivity | linarith
      have hopen : IsOpen { w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < Real.exp (-Real.log B / e) } :=
        isOpen_Ioi.preimage continuous_norm |> IsOpen.inter <| isOpen_Iio.preimage continuous_norm
      have := DorgeBauer.root_comp_holomorphic Q
        { w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < Real.exp (-Real.log B / e) } hopen
        (fun w => w⁻¹ ^ e) (fun w => g (-↑e * Complex.log w)) hφ hF
        (fun w hw => hroot w hw.1 hw.2) (fun w hw => ?_)
      · exact this.analyticOnNhd hopen
      · convert hQsep (w⁻¹ ^ e) _ using 1
        simp_all
        rw [lt_inv_comm₀] <;> try positivity
        · refine' lt_of_lt_of_le (pow_lt_pow_left₀ hw.2 (norm_nonneg _) (by positivity)) _
          rw [← Real.exp_nat_mul, mul_comm, div_mul_cancel₀ _ (by positivity), Real.exp_neg,
            Real.exp_log (by positivity)]
        · exact pow_pos (norm_pos_iff.mpr hw.1) _
    exact h_analytic
  · refine' ⟨_, _⟩
    · intro w hw₁ hw₂
      convert hg.2.2.1 (- (e : ℂ) * Complex.log w) _ using 1 <;>
        norm_num [Complex.exp_neg, Complex.exp_log, hw₁.ne']
      ring_nf
      · rw [Complex.exp_nat_mul, Complex.exp_log (by
            simp_all only [Metric.mem_ball, norm_pos_iff, ne_eq, not_false_eq_true])]
        ring_nf
      · rw [Complex.log_re]
        have := Real.log_lt_log hw₁ hw₂
        norm_num at *
        nlinarith [show (e : ℝ) ≥ 1 by norm_cast, mul_div_cancel₀ (-Real.log B) (by positivity : (e : ℝ) ≠ 0)]
    · intro x hx z hz
      have h_eq : H z = g (Complex.log z) := by
        apply DorgeBauer.branch_match_tail Q B hB hQsep T₁ hT1B H hcont hHroot g hg.1 hg.2.2.1 hg.2.1 x hx z hz
      have h_eq' : -(e : ℂ) * Complex.log (z⁻¹ ^ ((e : ℂ)⁻¹)) = Complex.log z := by
        apply DorgeBauer.cpow_neg_e_log e he z (by
        norm_num [Complex.normSq, Complex.norm_def] at *
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos] at hz <;> nlinarith [sq_nonneg (z.re - x), sq_nonneg z.im])
      rw [h_eq, ← h_eq']

lemma ramified_root_section
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (_hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (_hnp : ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x)
    (T₁ : ℝ) (H : ℂ → ℂ) (hT1a : 2 * (T₀ : ℝ) ≤ T₁) (_hT1b : (2 : ℝ) ≤ T₁)
    (hcont : ∀ x : ℝ, T₁ ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2)))
    (_hagree : ∀ y : ℝ, T₁ / 2 ≤ y → H (y : ℂ) = (g y : ℂ))
    (hHroot : ∀ x : ℝ, T₁ ≤ x → ∀ z ∈ Metric.ball (x : ℂ) (x / 2),
        (P.map (evalIntPolyComplex z)).eval (H z) = 0) :
    ∃ (e : ℕ) (ρ : ℝ) (F : ℂ → ℂ) (Tr : ℝ),
      1 ≤ e ∧ 0 < ρ ∧
      (2 * (T₀ : ℝ)) ≤ Tr ∧ (2 : ℝ) ≤ Tr ∧ T₁ ≤ Tr ∧
      AnalyticOnNhd ℂ F {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < ρ} ∧
      (∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ →
          (P.map (evalIntPolyComplex ((w⁻¹) ^ e))).eval (F w) = 0) ∧
      (∀ x : ℝ, Tr ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
          H z = F (z⁻¹ ^ ((e : ℂ)⁻¹))) := by
  -- `P` has positive `Y`-degree: a monic constant would have no roots, contradicting `hroot`.
  have hP_deg : 1 ≤ P.natDegree := by
    by_contra h
    push_neg at h
    interval_cases hd : P.natDegree
    have hP1 : P = 1 := by
      have hlc : P.coeff 0 = 1 := by
        have hm := hP_monic
        rwa [Polynomial.Monic, Polynomial.leadingCoeff, hd] at hm
      have hC := Polynomial.eq_C_of_natDegree_eq_zero hd
      rw [hC, hlc, map_one]
    have hev := hroot (T₀ : ℝ) le_rfl
    rw [hP1] at hev
    simp at hev
  -- Separable radical reduction: `Q = radical P` is monic, divides `P`, has the same roots,
  -- and is separable on the annulus `{ z | B < ‖z‖ }`.
  obtain ⟨Q, B, hQmon, hQdvd, hB, hQsep, hiff⟩ :=
    ComplexSeparableReduction.exists_complex_separable_reduction P hP_monic hP_deg
  -- Enlarge the threshold so tail balls sit inside the annulus `{ ‖z‖ > B }`.
  set T₁' : ℝ := max T₁ (2 * B + 1) with hT1'def
  have hT1'a : T₁ ≤ T₁' := le_max_left _ _
  have hT1'B : 2 * B < T₁' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hcont' : ∀ x : ℝ, T₁' ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2)) :=
    fun x hx => hcont x (le_trans hT1'a hx)
  have hHrootQ : ∀ x : ℝ, T₁' ≤ x → ∀ z ∈ Metric.ball (x : ℂ) (x / 2),
      (Q.map (evalIntPolyComplex z)).eval (H z) = 0 :=
    fun x hx z hz => (hiff z (H z)).mpr (hHroot x (le_trans hT1'a hx) z hz)
  -- Pure monodromy core over the separable covering.
  obtain ⟨e, ρ, F, Tr, he, hρ, hBTr, hT1Tr, hFan, hFrootQ, hrel⟩ :=
    separable_ramified_root_section Q hQmon B hB hQsep T₁' H hT1'B hcont' hHrootQ
  have hTrge : T₁ ≤ Tr := le_trans hT1'a hT1Tr
  refine ⟨e, ρ, F, Tr, he, hρ, ?_, ?_, hTrge, hFan, ?_, hrel⟩
  · linarith [hT1a]
  · linarith
  · exact fun w hw0 hwρ => (hiff ((w⁻¹) ^ e) (F w)).mp (hFrootQ w hw0 hwρ)

/-
**Finite-order pole bound for a ramified root section.**

A function `F` on a punctured disk `{ w | 0 < ‖w‖ < ρ }` (with `ρ ≤ 1`) that is, at each `w`,
a root of the *monic* specialised family at `z = (w⁻¹) ^ e`, automatically obeys a
finite-order pole bound `‖F w‖ ≤ Cf / ‖w‖ ^ Kf`. -/
lemma root_pole_bound
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic) (hP_deg : 1 ≤ P.natDegree)
    (e : ℕ) (ρ : ℝ) (_hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (F : ℂ → ℂ)
    (hFroot : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ →
        (P.map (evalIntPolyComplex ((w⁻¹) ^ e))).eval (F w) = 0) :
    ∃ (Cf : ℝ) (Kf : ℕ), 0 ≤ Cf ∧
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → ‖F w‖ ≤ Cf / ‖w‖ ^ Kf := by
  -- Step 1: Coefficient growth bound
  obtain ⟨C, N, hC_nonneg, hC_bound⟩ :
      ∃ C N, 0 ≤ C ∧ ∀ z : ℂ, (P.map (evalIntPolyComplex z)).natDegree = P.natDegree ∧
        ∀ i < (P.map (evalIntPolyComplex z)).natDegree,
          ‖(P.map (evalIntPolyComplex z)).coeff i‖ ≤ C * (1 + ‖z‖) ^ N := by
    obtain ⟨C, N, hC_nonneg, hC_bound⟩ :
        ∃ C N, 0 ≤ C ∧ ∀ i < P.natDegree, ∀ z : ℂ,
          ‖((P.coeff i).map (Int.castRingHom ℂ)).eval z‖ ≤ C * (1 + ‖z‖) ^ N := by
      use ∑ i ∈ Finset.range P.natDegree,
            ∑ j ∈ Finset.range
                ((P.coeff i |> Polynomial.map (Int.castRingHom ℂ) |> Polynomial.natDegree) + 1),
              ‖ (P.coeff i |> Polynomial.map (Int.castRingHom ℂ) |> Polynomial.coeff) j‖,
        ∑ i ∈ Finset.range P.natDegree,
          ((P.coeff i |> Polynomial.map (Int.castRingHom ℂ) |> Polynomial.natDegree))
      refine' ⟨Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _, fun i hi z => _⟩
      refine' le_trans _ (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum
          (fun i _ => Finset.sum_nonneg fun j _ =>
            norm_nonneg (Polynomial.coeff (Polynomial.map (Int.castRingHom ℂ) (P.coeff i)) j))
          (Finset.mem_range.mpr hi))
        (by positivity))
      refine' le_trans (complex_poly_eval_norm_le _ _) _
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg z])
        (Finset.single_le_sum
          (fun i _ => Nat.zero_le (Polynomial.natDegree (Polynomial.map (Int.castRingHom ℂ) (P.coeff i))))
          (Finset.mem_range.mpr hi)))
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    refine' ⟨C, N, hC_nonneg, fun z => ⟨_, _⟩⟩
    · rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
      simp_all only [norm_pos_iff, ne_eq, inv_pow, Polynomial.Monic.leadingCoeff, map_one,
        one_ne_zero, not_false_eq_true]
    · intro i hi
      specialize hC_bound i
      simp_all [Polynomial.coeff_map]
      convert hC_bound z using 1
  -- Step 2: Cauchy bound per w
  have h_cauchy_bound : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → ‖F w‖ ≤ 1 + P.natDegree * (C * (1 + ‖w⁻¹ ^ e‖) ^ N) := by
    intros w hw_pos hw_lt_ρ
    have hQz_monic : (P.map (evalIntPolyComplex (w⁻¹ ^ e))).Monic := by
      exact hP_monic.map _
    have hQz_deg : (P.map (evalIntPolyComplex (w⁻¹ ^ e))).natDegree = P.natDegree := by
      exact hC_bound _ |>.1
    have hQz_root : (P.map (evalIntPolyComplex (w⁻¹ ^ e))).IsRoot (F w) := by
      exact hFroot w hw_pos hw_lt_ρ
    have hQz_bound : ∀ i < (P.map (evalIntPolyComplex (w⁻¹ ^ e))).natDegree,
        ‖(P.map (evalIntPolyComplex (w⁻¹ ^ e))).coeff i‖ ≤ C * (1 + ‖w⁻¹ ^ e‖) ^ N := by
      exact hC_bound _ |>.2
    grind only [ComplexSeparableReduction.exists_complex_separable_reduction,
      cauchy_root_bound_max, #693d, #a720, #0d9f]
  -- Step 3: Turn ‖z‖ into a pole in ‖w‖
  have h_pole_bound : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ →
      1 + P.natDegree * (C * (1 + ‖w⁻¹ ^ e‖) ^ N) ≤ (1 + P.natDegree * C * 2 ^ N) / ‖w‖ ^ (e * N) := by
    intros w hw_pos hw_lt_ρ
    have h_norm_bound : (1 + ‖w⁻¹ ^ e‖) ^ N ≤ 2 ^ N / ‖w‖ ^ (e * N) := by
      have h_norm_bound : (1 + ‖w⁻¹ ^ e‖) ≤ 2 / ‖w‖ ^ e := by
        norm_num +zetaDelta at *
        rw [le_div_iff₀ (pow_pos (norm_pos_iff.mpr hw_pos) _)]
        nlinarith [pow_le_pow_of_le_one (norm_nonneg w) (by linarith) (show e ≥ 0 by positivity),
          inv_mul_cancel₀ (ne_of_gt (pow_pos (norm_pos_iff.mpr hw_pos) e))]
      convert pow_le_pow_left₀ (by positivity) h_norm_bound N using 1
      ring
    rw [le_div_iff₀ (by positivity)] at *
    nlinarith [show 0 ≤ (P.natDegree : ℝ) * C by positivity,
      show ‖w‖ ^ (e * N) ≤ 1 by exact pow_le_one₀ (by positivity) (by linarith)]
  exact ⟨1 + P.natDegree * C * 2 ^ N, e * N, by positivity,
    fun w hw hw' => le_trans (h_cauchy_bound w hw hw') (h_pole_bound w hw hw')⟩

/-- **Monodromy of the algebraic function over the annulus at infinity (ramification
index form).**

This is the first of the two deep analytic inputs behind `puiseux_tail_of_root_growth`.  It
is now assembled from the isolated monodromy core `ramified_root_section` (the genuinely deep
covering-space input) and the provable Cauchy pole bound `root_pole_bound`. -/
lemma monodromy_ramification_index
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (hnp : ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x)
    (T₁ : ℝ) (H : ℂ → ℂ) (hT1a : 2 * (T₀ : ℝ) ≤ T₁) (hT1b : (2 : ℝ) ≤ T₁)
    (hcont : ∀ x : ℝ, T₁ ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2)))
    (hagree : ∀ y : ℝ, T₁ / 2 ≤ y → H (y : ℂ) = (g y : ℂ))
    (hHroot : ∀ x : ℝ, T₁ ≤ x → ∀ z ∈ Metric.ball (x : ℂ) (x / 2),
        (P.map (evalIntPolyComplex z)).eval (H z) = 0)
    (C : ℝ) (N : ℕ) (_hC : 0 ≤ C)
    (_hgrowth : ∀ x : ℝ, T₁ ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
        ‖H z‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ (e : ℕ) (ρ Cf : ℝ) (Kf : ℕ) (F : ℂ → ℂ) (Tr : ℝ),
      1 ≤ e ∧ 0 < ρ ∧ 0 ≤ Cf ∧
      (2 * (T₀ : ℝ)) ≤ Tr ∧ (2 : ℝ) ≤ Tr ∧ T₁ ≤ Tr ∧
      AnalyticOnNhd ℂ F {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < ρ} ∧
      (∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → ‖F w‖ ≤ Cf / ‖w‖ ^ Kf) ∧
      (∀ x : ℝ, Tr ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
          H z = F (z⁻¹ ^ ((e : ℂ)⁻¹))) := by
  -- Degree of `P` is at least one: it has the complex root `H (T₁)` at `z = T₁`.
  have hP_deg : 1 ≤ P.natDegree := by
    by_contra hdeg
    push_neg at hdeg
    have hz0 : (P.map (evalIntPolyComplex (T₁ : ℂ))).eval (H (T₁ : ℂ)) = 0 :=
      hHroot T₁ le_rfl (T₁ : ℂ) (Metric.mem_ball_self (by linarith))
    have hmoniceval : (P.map (evalIntPolyComplex (T₁ : ℂ))).eval (H (T₁ : ℂ)) = 1 := by
      have hpeq : P = 1 := by
        have := hP_monic.natDegree_eq_zero.mp (Nat.lt_one_iff.mp hdeg)
        exact this
      simp [hpeq]
    rw [hmoniceval] at hz0
    exact one_ne_zero hz0
  -- Deep monodromy core: the ramified single-valued root section on a punctured disk.
  obtain ⟨e, ρ₀, F, Tr, he, hρ₀, hTra, hTrb, hTrT1, hFan₀, hFroot, hrel⟩ :=
    ramified_root_section P hP_monic T₀ g hg hroot hnp T₁ H hT1a hT1b hcont hagree hHroot
  -- Shrink the radius to `≤ 1` so the Cauchy pole bound applies.
  set ρ : ℝ := min ρ₀ 1 with hρdef
  have hρ0 : 0 < ρ := lt_min hρ₀ one_pos
  have hρle₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρle1 : ρ ≤ 1 := min_le_right _ _
  have hFroot' : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ →
      (P.map (evalIntPolyComplex ((w⁻¹) ^ e))).eval (F w) = 0 :=
    fun w hw0 hwρ => hFroot w hw0 (lt_of_lt_of_le hwρ hρle₀)
  obtain ⟨Cf, Kf, hCf, hbound⟩ :=
    root_pole_bound P hP_monic hP_deg e ρ hρ0 hρle1 F hFroot'
  refine ⟨e, ρ, Cf, Kf, F, Tr, he, hρ0, hCf, hTra, hTrb, hTrT1, ?_, hbound, hrel⟩
  exact hFan₀.mono (fun w hw => ⟨hw.1, lt_of_lt_of_le hw.2 hρle₀⟩)

/-
**Norm bound for a real complex power on a tail sphere.**

For `z` on `sphere x (x/2)` with `2 ≤ x`, and any real exponent `σ ≤ s'`, the complex power
`z ^ σ` is bounded by `2^|s'| · x^{s'}`.  (On the sphere `‖z‖ = θ·x` with `θ ∈ [1/2, 2]`.)
-/
lemma laurent_tail_term_bound (z : ℂ) (x σ s' : ℝ) (hx : 2 ≤ x)
    (hz : z ∈ Metric.sphere (x : ℂ) (x / 2)) (hσ : σ ≤ s') :
    ‖z ^ ((σ : ℝ) : ℂ)‖ ≤ (2 : ℝ) ^ |s'| * x ^ s' := by
  have h_norm_bound : ‖z‖ ^ σ ≤ ‖z‖ ^ s' := by
    apply_rules [Real.rpow_le_rpow_of_exponent_le]
    have := norm_sub_le (z : ℂ) (z - x)
    norm_num at *
    linarith [abs_of_nonneg (by positivity : 0 ≤ x)]
  -- Write `‖z‖` as `θ * x` with `θ = ‖z‖ / x ∈ [1/2, 2]`.
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, ‖z‖ = θ * x ∧ 1 / 2 ≤ θ ∧ θ ≤ 2 := by
    refine' ⟨‖z‖ / x, _, _, _⟩
    · rw [div_mul_cancel₀ _ (by positivity)]
    · have := norm_sub_le (z : ℂ) (z - x)
      norm_num at *
      rw [le_div_iff₀] <;> linarith [abs_of_nonneg (by positivity : 0 ≤ x)]
    · rw [div_le_iff₀ (by positivity)]
      have := norm_add_le (z - x) x
      simp_all [Complex.normSq, Complex.norm_def]
      grind
  -- Now bound `θ ^ s'`. Since `1/2 ≤ θ ≤ 2`, we have `θ ^ s' ≤ 2 ^ |s'|`.
  have h_theta_bound : θ ^ s' ≤ 2 ^ |s'| := by
    by_cases hs' : 0 ≤ s'
    · rw [abs_of_nonneg hs']
      exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    · rw [abs_of_neg (not_le.mp hs'), Real.rpow_neg (by linarith)]
      rw [← Real.inv_rpow (by linarith)]
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  convert h_norm_bound.trans _ using 1
  · rw [← Complex.norm_cpow_real]
  · rw [hθ.1, Real.mul_rpow (by linarith) (by linarith)]
    exact mul_le_mul_of_nonneg_right h_theta_bound (by positivity)

/-
**Reality of the Laurent/Taylor coefficients.**

The Taylor coefficients of the removable-singularity extension `G` at `0` are real, because
`G` takes real values on the positive real segment (it equals a real branch value there).
-/
lemma laurent_coeff_real
    (ρ : ℝ) (Kf : ℕ) (F G : ℂ → ℂ) (hρ : 0 < ρ)
    (hG : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) ρ))
    (hFG : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → F w = G w / w ^ Kf)
    (e : ℕ) (he : 1 ≤ e) (H : ℂ → ℂ) (g : ℝ → ℝ) (T₁ Tr : ℝ)
    (hTrb : 2 ≤ Tr) (hTrT1 : T₁ ≤ Tr)
    (hagree : ∀ y : ℝ, T₁ / 2 ≤ y → H (y : ℂ) = (g y : ℂ))
    (hrel : ∀ x : ℝ, Tr ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
        H z = F (z⁻¹ ^ ((e : ℂ)⁻¹))) (m : ℕ) :
    (iteratedDeriv m G 0).im = 0 := by
  have hr : (0:ℝ) < min ρ ((3 * Tr / 2) ^ (-(1 : ℝ) / e)) := lt_min hρ (by positivity)
  apply DorgeBauer.iteratedDeriv_im_zero_of_real_on_pos G
      (min ρ ((3 * Tr / 2) ^ (-(1 : ℝ) / e))) hr
      (hG.mono (Metric.ball_subset_ball (min_le_left _ _))) (by
  intro t ht ht'
  have := hrel ((2 / 3) * t ^ (- (e : ℝ))) ?_
      ((3 * ((2 / 3) * t ^ (- (e : ℝ))) / 2 : ℝ) : ℂ) ?_ <;> norm_num at *
  · rw [hFG] at this
    · convert congr_arg Complex.im
        (show G t = (g (3 * (2 / 3 * (t ^ e) ⁻¹) / 2) : ℂ) * t ^ Kf from ?_) using 1
      · norm_cast
      · convert congr_arg (fun x : ℂ => x * t ^ Kf) this.symm using 1
        · rw [show (2 / (3 * (2 / 3 * (t ^ e : ℂ) ⁻¹))) = (t ^ e : ℂ) by
            ring_nf
            norm_num [ht.ne']]
          norm_cast
          norm_num [ht.ne', ht.le]
          rw [← Complex.cpow_natCast, ← Complex.cpow_mul, mul_inv_cancel₀ (by
            norm_cast
            linarith), Complex.cpow_one]
          norm_num [ht.ne']
          · norm_num [Complex.log_im]
            rw [Complex.arg_ofReal_of_nonneg ht.le]
            norm_num
            linarith [Real.pi_pos]
          · norm_num [Complex.log_im]
            rw [Complex.arg_ofReal_of_nonneg ht.le]
            norm_num
            linarith [Real.pi_pos]
        · convert congr_arg (fun x : ℂ => x * t ^ Kf)
            (hagree (3 * (2 / 3 * (t ^ e) ⁻¹) / 2) ?_ |> Eq.symm) using 1
          · norm_num [Complex.ofReal_cpow, ht.le]
          · have h_exp : t ^ e < (3 * Tr / 2) ^ (-1 : ℝ) :=
              lt_of_lt_of_le (pow_lt_pow_left₀ ht'.2 (by positivity) (by positivity))
                (by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
                    div_mul_cancel₀ _ (by positivity)])
            rw [Real.rpow_neg_one] at h_exp
            nlinarith [inv_mul_cancel₀ (show (3 * Tr / 2) ≠ 0 by positivity),
              inv_mul_cancel₀ (show (t ^ e) ≠ 0 by positivity), pow_pos ht e]
    · norm_num [ht.ne']
    · convert ht'.1 using 1
      ring_nf
      norm_num [ht.ne']
      rw [abs_of_pos ht, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        mul_inv_cancel₀ (by positivity), Real.rpow_one]
  · have h_exp : t ^ e < (3 * Tr / 2) ^ (-1 : ℝ) :=
      lt_of_lt_of_le (pow_lt_pow_left₀ ht'.2 (by positivity) (by positivity))
        (by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
            div_mul_cancel₀ _ (by positivity)])
    norm_num [Real.rpow_neg_one] at *
    rw [lt_div_iff₀] at h_exp <;> nlinarith [pow_pos ht e, mul_inv_cancel₀ (ne_of_gt (pow_pos ht e))]
  · ring_nf
    norm_num [ht.le]
    rw [abs_of_pos ht]) m

/-
**On-sphere Puiseux expansion of `H` of a given order.** -/
lemma laurent_H_expansion_of_G
    (ρ : ℝ) (Kf : ℕ) (F G : ℂ → ℂ) (hρ : 0 < ρ)
    (hG : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) ρ))
    (hFG : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → F w = G w / w ^ Kf)
    (e : ℕ) (he : 1 ≤ e) (H : ℂ → ℂ) (Tr : ℝ) (hTrb : 2 ≤ Tr)
    (hrel : ∀ x : ℝ, Tr ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
        H z = F (z⁻¹ ^ ((e : ℂ)⁻¹))) (n : ℕ) :
    ∃ (R : ℂ → ℂ) (T M : ℝ), Tr ≤ T ∧ 2 ≤ T ∧ 0 ≤ M ∧
      ∀ x : ℝ, T ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
        H z = (∑ m ∈ Finset.range n,
              (iteratedDeriv m G 0 / (m.factorial : ℂ)) * z ^ ((((Kf : ℝ) - m) / e : ℝ) : ℂ))
            + z ^ ((((Kf : ℝ) - n) / e : ℝ) : ℂ) * R (z⁻¹ ^ ((e : ℂ)⁻¹))
          ∧ ‖R (z⁻¹ ^ ((e : ℂ)⁻¹))‖ ≤ M := by
  obtain ⟨R, δ, M', hδ, hM', htay, hRb⟩ := analytic_taylor_remainder_bound G (hG 0 (Metric.mem_ball_self hρ)) n

  obtain ⟨T, hT⟩ : ∃ T : ℝ, Tr ≤ T ∧ 2 ≤ T ∧ ∀ x : ℝ, T ≤ x → ∀ z : ℂ,
      z ∈ Metric.sphere (x : ℂ) (x / 2) → ‖z⁻¹ ^ ((e : ℂ)⁻¹)‖ < min δ ρ := by

    obtain ⟨T, hT⟩ : ∃ T : ℝ, Tr ≤ T ∧ 2 ≤ T ∧ ∀ x : ℝ, T ≤ x → ∀ z : ℂ,
        z ∈ Metric.sphere (x : ℂ) (x / 2) → ‖z⁻¹‖ < (min δ ρ) ^ e := by
      refine' ⟨Tr + 2 + (min δ ρ ^ e) ⁻¹ * 2, _, _, _⟩
      · linarith [inv_nonneg.2 (pow_nonneg (le_min hδ.le hρ.le) e)]
      · exact le_add_of_le_of_nonneg (by linarith) (by positivity)
      · intro x hx z hz
        have hz_norm : ‖z‖ ≥ x / 2 := by
          have := norm_sub_le (z : ℂ) (z - x)
          norm_num at *
          linarith [abs_le.mp this]
        norm_num at *
        rw [inv_eq_one_div, div_lt_iff₀] <;>
          nlinarith [show 0 < min δ ρ ^ e by positivity,
            inv_mul_cancel₀ (show (min δ ρ ^ e) ≠ 0 by positivity)]
    refine' ⟨T, hT.1, hT.2.1, fun x hx z hz => _⟩
    convert Real.rpow_lt_rpow (by positivity) (hT.2.2 x hx z hz)
      (inv_pos.mpr (by positivity : 0 < (e : ℝ))) using 1
    · rw [← Complex.norm_cpow_real]
      norm_num
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_inv_cancel₀ (by positivity), Real.rpow_one]
  refine' ⟨R, T, M', hT.1, hT.2.1, hM', _⟩
  intro x hx z hz
  have hz_pos : 0 < z.re := by
    have hz_re : Complex.re z ≥ x - x / 2 := by
      have hz_re : ‖z - x‖ = x / 2 := by
        exact hz
      have hz_re : |Complex.re z - x| ≤ x / 2 := by
        exact hz_re ▸ Complex.abs_re_le_norm (z - x) |> le_trans (by norm_num)
      linarith [abs_le.mp hz_re]
    linarith
  have hw_pos : 0 < ‖z⁻¹ ^ ((e : ℂ)⁻¹)‖ := by
    by_cases hz_zero : z = 0 <;> simp_all [Complex.cpow_def]
  have hw_δ : ‖z⁻¹ ^ ((e : ℂ)⁻¹)‖ < δ := by
    exact lt_of_lt_of_le (hT.2.2 x hx z hz) (min_le_left _ _)
  have hw_ρ : ‖z⁻¹ ^ ((e : ℂ)⁻¹)‖ < ρ := by
    exact lt_of_lt_of_le (hT.2.2 x hx z hz) (min_le_right _ _)
  have hH_val : H z = G (z⁻¹ ^ ((e : ℂ)⁻¹)) / (z⁻¹ ^ ((e : ℂ)⁻¹)) ^ Kf := by
    rw [hrel x (by linarith) z hz, hFG _ hw_pos hw_ρ]
  have hG_val : G (z⁻¹ ^ ((e : ℂ)⁻¹)) =
      ∑ m ∈ Finset.range n, (iteratedDeriv m G 0 / (m.factorial : ℂ)) * (z⁻¹ ^ ((e : ℂ)⁻¹)) ^ m +
        (z⁻¹ ^ ((e : ℂ)⁻¹)) ^ n * R (z⁻¹ ^ ((e : ℂ)⁻¹)) := by
    exact htay _ hw_δ
  have hR_bound : ‖R (z⁻¹ ^ ((e : ℂ)⁻¹))‖ ≤ M' := by
    exact hRb _ hw_δ
  exact ⟨by
    convert laurent_sphere_identity e Kf n he
      (fun m => iteratedDeriv m G 0 / (m.factorial : ℂ)) (R (z⁻¹ ^ (e : ℂ) ⁻¹))
      (G (z⁻¹ ^ (e : ℂ) ⁻¹)) z hz_pos (by rw [hG_val]) using 1, hR_bound⟩

/-
**A function analytic on `Ioi T₀` equal to a polynomial on a tail is that polynomial.**

If `g` is `C^∞` on `Ici T₀`, real-analytic on `Ioi T₀`, and equals `q.eval` on `[T, ∞)` for
some `T > T₀`, then `g = q.eval` on all of `Ici T₀`.
-/
lemma eq_poly_of_tail_of_analytic (T₀ : ℤ) (g : ℝ → ℝ) (q : Polynomial ℝ) (T : ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hgana : AnalyticOnNhd ℝ g (Set.Ioi (T₀ : ℝ)))
    (hT : (T₀ : ℝ) < T)
    (htail : ∀ y : ℝ, T ≤ y → g y = q.eval y) :
    ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x := by
  -- By the identity theorem for analytic functions, if two analytic functions agree on a set with an accumulation point, they are equal everywhere. Here, $g$ and $q.eval$ agree on $[T, \infty)$, which has $T$ as an accumulation point.
  have h_eq_on_Ioi : ∀ x : ℝ, x > T₀ → g x = q.eval x := by
    have h_eq_on_Ioi : AnalyticOnNhd ℝ (fun x => q.eval x) (Set.Ioi (T₀ : ℝ)) := by
      apply_rules [ContDiff.analyticOnNhd]
      simpa only [Polynomial.eval_eq_sum_range] using
        ContDiff.sum fun i hi => ContDiff.mul (contDiff_const) (contDiff_id.pow i)
    apply hgana.eqOn_of_preconnected_of_eventuallyEq h_eq_on_Ioi
    exact isPreconnected_Ioi
    exact Set.mem_Ioi.mpr (show (T₀ : ℝ) < T + 1 by linarith)
    filter_upwards [lt_mem_nhds (show T + 1 > T by linarith)] with x hx using htail x hx.le
  intro x hx
  cases lt_or_eq_of_le hx <;> simp_all
  -- By continuity of $g$ at $x$, we have $\lim_{y \to x^+} g(y) = g(x)$.
  have h_cont_right : Filter.Tendsto g (nhdsWithin x (Set.Ioi x)) (nhds (g x)) := by
    have := hg.continuousOn x (by norm_num)
    exact this.mono_left (nhdsWithin_mono _ <| Set.Ioi_subset_Ici_self)
  exact tendsto_nhds_unique h_cont_right (Filter.Tendsto.congr'
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun y hy => by rw [h_eq_on_Ioi y hy])
    (q.continuous.continuousWithinAt))

/-
**A non-natural Puiseux exponent exists (from non-polynomiality).**

If `g` is not (eventually) a polynomial, then some Taylor coefficient of `G` with a
non-natural exponent `(Kf-m)/e` is nonzero.  Otherwise all exponents would be natural and
`H` (hence `g`) would be a polynomial, contradicting `hnp`.
-/
lemma laurent_nonnat_exp
    (T₀ : ℤ) (g : ℝ → ℝ) (ρ : ℝ) (Kf : ℕ) (F G : ℂ → ℂ) (hρ : 0 < ρ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hgana : AnalyticOnNhd ℝ g (Set.Ioi (T₀ : ℝ)))
    (hG : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) ρ))
    (hFG : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → F w = G w / w ^ Kf)
    (_hFan : AnalyticOnNhd ℂ F {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < ρ})
    (e : ℕ) (he : 1 ≤ e) (H : ℂ → ℂ) (T₁ Tr : ℝ)
    (hTrb : 2 ≤ Tr) (hTrT1 : T₁ ≤ Tr) (_hT1T0 : (T₀ : ℝ) < T₁)
    (hagree : ∀ y : ℝ, T₁ / 2 ≤ y → H (y : ℂ) = (g y : ℂ))
    (hnp : ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x)
    (hrel : ∀ x : ℝ, Tr ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
        H z = F (z⁻¹ ^ ((e : ℂ)⁻¹))) :
    ∃ m : ℕ, iteratedDeriv m G 0 ≠ 0 ∧ ∀ i : ℕ, (((Kf : ℝ) - m) / e) ≠ (i : ℝ) := by
  contrapose! hnp
  simp_all [Polynomial.eval_eq_sum_range]
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T₀ < T ∧ ∀ y : ℝ, T ≤ y →
      g y = ∑ m ∈ Finset.range (Kf + 1),
        (iteratedDeriv m G 0 / (m.factorial : ℂ)).re * y ^ ((Kf - m) / e : ℕ) := by
    -- Choose a threshold $T$ such that for all $y \geq T$, $y^{-1/e} < \rho$.
    obtain ⟨T, hT⟩ : ∃ T : ℝ, T₀ < T ∧ ∀ y : ℝ, T ≤ y →
        (y : ℂ)⁻¹ ^ ((e : ℂ)⁻¹) ∈ Metric.ball 0 ρ ∧ 0 < ‖(y : ℂ)⁻¹ ^ ((e : ℂ)⁻¹)‖ := by
      -- Choose $T$ such that for all $y \geq T$, $y^{-1/e} < \rho$.
      obtain ⟨T, hT⟩ : ∃ T : ℝ, T₀ < T ∧ ∀ y : ℝ, T ≤ y → (y : ℝ)⁻¹ ^ (1 / e : ℝ) < ρ := by
        have h_lim : Filter.Tendsto (fun y : ℝ => y⁻¹ ^ (1 / e : ℝ)) Filter.atTop (nhds 0) := by
          exact le_trans (Filter.Tendsto.rpow (tendsto_inv_atTop_zero) tendsto_const_nhds <|
            Or.inr <| by positivity) <| by norm_num [show e ≠ 0 by positivity]
        exact Filter.eventually_atTop.mp (h_lim.eventually (gt_mem_nhds hρ)) |>
          fun ⟨T, hT⟩ ↦ ⟨Max.max (T₀ + 1) T, by norm_num,
            fun y hy ↦ hT y <| le_trans (le_max_right _ _) hy⟩
      refine' ⟨Max.max T 1, _, _⟩ <;> norm_num [hT]
      exact fun y hy₁ hy₂ => ⟨by simpa [abs_of_nonneg (by linarith : 0 ≤ y)] using hT.2 y hy₁, by positivity⟩
    refine' ⟨Max.max T (Max.max Tr ((3 * Tr) / 2 + 1)), _, _⟩ <;> norm_num at *
    · exact Or.inl hT.1
    · intro y hy₁ hy₂ hy₃
      have hH : H (y : ℂ) = ∑ m ∈ Finset.range (Kf + 1),
          (iteratedDeriv m G 0 / (m.factorial : ℂ)) * y ^ (((Kf : ℝ) - m) / e : ℂ) := by
        convert hrel (2 * y / 3) (by linarith) (y : ℂ) _ using 1
        · rw [hFG]
          · rw [laurent_G_poly_of_vanishing ρ hρ G Kf hG]
            · rw [Finset.sum_div _ _ _]
              refine' Finset.sum_congr rfl fun m hm => _
              rw [← Complex.cpow_nat_mul]
              ring_nf
              rw [Complex.cpow_sub] <;> norm_num
              ring_nf
              · norm_num [Complex.cpow_def_of_ne_zero, show y ≠ 0 by linarith]
                ring_nf
                rw [Complex.log_inv]
                norm_num [← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add]
                ring_nf
                rw [Complex.arg_ofReal_of_nonneg (by linarith)]
                linarith [Real.pi_pos]
              · linarith
            · intro m hm
              specialize hnp m
              contrapose! hnp
              refine ⟨hnp, fun i hi => ?_⟩
              rw [div_eq_iff (by positivity)] at hi
              nlinarith [show (Kf : ℝ) + 1 ≤ m by norm_cast, show (e : ℝ) ≥ 1 by norm_cast]
            · convert hT.2 y hy₁ |>.1 using 1
              norm_num [Complex.norm_cpow_of_ne_zero, show y ≠ 0 by linarith]
          · norm_num [Complex.cpow_def]
            split_ifs <;> norm_num [Complex.exp_ne_zero]
            linarith
          · convert hT.2 y hy₁ |>.1 using 1
            norm_num [Complex.norm_cpow_of_ne_zero, show y ≠ 0 by linarith]
        · norm_num [Complex.normSq, Complex.norm_def]
          ring_nf
          norm_num [show y ≥ 0 by linarith]
      convert congr_arg Complex.re hH using 1
      · rw [hagree y (by linarith)]
        norm_num
      · rw [Complex.re_sum]
        refine' Finset.sum_congr rfl fun m hm => _
        by_cases hm' : iteratedDeriv m G 0 = 0 <;> simp_all [Complex.cpow_def]
        ring_nf
        obtain ⟨i, hi⟩ := hnp m hm'
        rw [div_eq_iff (by positivity)] at hi
        norm_cast at *
        simp_all
        ring_nf
        rw [show Kf = m + i * e by linarith [Nat.sub_add_cancel hm]]
        norm_num [Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, show e ≠ 0 by linarith]
        ring_nf
        split_ifs <;>
          simp_all [Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, mul_assoc,
            mul_comm, mul_left_comm, ne_of_gt (zero_lt_one.trans_le he)]
        ring_nf
        norm_num [Complex.arg_ofReal_of_nonneg (by linarith : 0 ≤ y), Real.exp_nat_mul,
          Real.exp_log (by linarith : 0 < y)]
        ring
  obtain ⟨q, hq⟩ : ∃ q : Polynomial ℝ, ∀ y : ℝ, T ≤ y → g y = q.eval y := by
    use ∑ m ∈ Finset.range (Kf + 1),
      Polynomial.C ((iteratedDeriv m G 0 / (m.factorial : ℂ)).re) * Polynomial.X ^ ((Kf - m) / e)
    simp_all [Polynomial.eval_finset_sum]
  exact ⟨q, fun x hx => by
    rw [eq_poly_of_tail_of_analytic T₀ g q T hg hgana hT.1 hq x hx, Polynomial.eval_eq_sum_range]⟩

open Classical in
/-- Polynomial (integer-exponent) part of the Puiseux expansion of `H`, of order `n`. -/
noncomputable def laurentPoly (G : ℂ → ℂ) (e Kf n : ℕ) : Polynomial ℝ :=
  ∑ m ∈ ((Finset.range n).filter
      (fun k => ∃ i : ℕ, ((Kf : ℝ) - (k : ℝ)) / (e : ℝ) = (i : ℝ)) : Finset ℕ),
    Polynomial.C ((iteratedDeriv m G 0 / (Nat.factorial m : ℂ)).re) * Polynomial.X ^ ((Kf - m) / e)

open Classical in
/-- Finite set of genuinely non-natural Puiseux exponents of `H`, of order `n`. -/
noncomputable def laurentI (G : ℂ → ℂ) (e Kf n : ℕ) : Finset ℝ :=
  (((Finset.range n).filter
    (fun k => iteratedDeriv k G 0 ≠ 0 ∧ ∀ i : ℕ, ((Kf : ℝ) - (k : ℝ)) / (e : ℝ) ≠ (i : ℝ)) :
      Finset ℕ)).image (fun m => ((Kf : ℝ) - (m : ℝ)) / (e : ℝ))

open Classical in
/-- Coefficient function for the non-natural Puiseux part. -/
noncomputable def laurentA (G : ℂ → ℂ) (e Kf n : ℕ) : ℝ → ℝ :=
  fun σ => ∑ m ∈ ((Finset.range n).filter
    (fun k => (iteratedDeriv k G 0 ≠ 0 ∧ ∀ i : ℕ, ((Kf : ℝ) - (k : ℝ)) / (e : ℝ) ≠ (i : ℝ))
      ∧ ((Kf : ℝ) - (k : ℝ)) / (e : ℝ) = σ) : Finset ℕ),
    (iteratedDeriv m G 0 / (Nat.factorial m : ℂ)).re

/-
**The principal part reassembles the order-`n` Puiseux partial sum.**

The integer-exponent polynomial part plus the non-natural fractional part together equal the
full order-`n` partial sum `∑_{m<n} c_m z^{(Kf-m)/e}`.
-/
lemma laurent_principal_eq (G : ℂ → ℂ) (e Kf n : ℕ) (he : 1 ≤ e) (z : ℂ) (_hz : z ≠ 0)
    (hreal : ∀ m, (iteratedDeriv m G 0).im = 0) :
    ((laurentPoly G e Kf n).map (algebraMap ℝ ℂ)).eval z
      + ∑ σ ∈ laurentI G e Kf n, (laurentA G e Kf n σ : ℂ) * z ^ (σ : ℂ)
      = ∑ m ∈ Finset.range n,
          (iteratedDeriv m G 0 / (m.factorial : ℂ)) * z ^ ((((Kf : ℝ) - m) / e : ℝ) : ℂ) := by
  unfold laurentI laurentA laurentPoly
  rw [Finset.sum_image]
  · simp
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    refine' Finset.sum_congr rfl fun x hx => _
    split_ifs <;> simp_all [Complex.ext_iff]
    · rcases ‹_› with ⟨i, hi⟩
      rw [div_eq_iff (by positivity)] at hi
      norm_cast at *
      simp_all
      rw [Int.subNatNat_eq_coe] at hi
      norm_num [show Kf - x = i * e by exact Nat.sub_eq_of_eq_add <| by linarith]
      norm_cast
      simp [Nat.mul_div_cancel _ he]
      norm_num [Rat.mkRat_eq_div, mul_div_cancel_right₀, show e ≠ 0 by linarith]
    · rw [Finset.sum_eq_single x] <;> simp_all [Complex.ext_iff]
      intro b hb hb' hb'' hb''' hb''''
      simp_all [div_eq_mul_inv]
  · intro m hm m' hm' h
    simp_all [div_eq_iff, ne_of_gt (zero_lt_one.trans_le he)]

/-
**Convergent Laurent expansion of the ramified branch, with uniform growth bounds.**

This is the second of the two deep analytic inputs behind `puiseux_tail_of_root_growth`.

Given the ramification data produced by `monodromy_ramification_index` — a single-valued
holomorphic function `F` on a punctured disk `{ w | 0 < ‖w‖ < ρ }` with a finite-order pole
bound `‖F w‖ ≤ Cf / ‖w‖ ^ Kf`, and the substitution relation `F (z⁻¹ ^ (1/e)) = H z` on the
tail spheres — the finite-order pole guarantees a **convergent** Laurent expansion
`F w = ∑_{n ≥ -Kf} cₙ wⁿ` on the punctured disk, converging with uniform bounds on circles.
Substituting `w = z⁻¹ ^ (1/e)` re-expresses this as a convergent Puiseux series for `H` in
fractional powers of `z`: the finitely many terms with `n < 0` split into the polynomial part
`poly` (exponents `-n/e ∈ ℕ`) and the genuinely fractional principal part `∑_{σ ∈ I} a σ · z^σ`
(exponents `-n/e ∉ ℕ`), while the terms with `n ≥ 0` sum to a tail bounded by `A · x^{s'}` on
the sphere `sphere x (x/2)`.  Non-polynomiality of `g` (`hnp`), transported through the
real-axis agreement `hagree`, forces the top exponent `s := max I` to be genuinely
*non-natural* (`s ∉ ℕ`; note `s` may be a negative integer) with a nonzero coefficient
`a s ≠ 0`. -/
lemma convergent_laurent_tail_bound
    (P : Polynomial (Polynomial ℤ)) (_hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hgana : AnalyticOnNhd ℝ g (Set.Ioi (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (hnp : ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x)
    (T₁ : ℝ) (H : ℂ → ℂ) (hT1a : 2 * (T₀ : ℝ) ≤ T₁) (hT1b : (2 : ℝ) ≤ T₁)
    (_hcont : ∀ x : ℝ, T₁ ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2)))
    (hagree : ∀ y : ℝ, T₁ / 2 ≤ y → H (y : ℂ) = (g y : ℂ))
    (_hHroot : ∀ x : ℝ, T₁ ≤ x → ∀ z ∈ Metric.ball (x : ℂ) (x / 2),
        (P.map (evalIntPolyComplex z)).eval (H z) = 0)
    (e : ℕ) (ρ Cf : ℝ) (Kf : ℕ) (F : ℂ → ℂ) (Tr : ℝ)
    (he : 1 ≤ e) (hρ : 0 < ρ) (hCf : 0 ≤ Cf)
    (hTra : (2 * (T₀ : ℝ)) ≤ Tr) (hTrb : (2 : ℝ) ≤ Tr) (hTrT1 : T₁ ≤ Tr)
    (hFan : AnalyticOnNhd ℂ F {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < ρ})
    (hFgrow : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → ‖F w‖ ≤ Cf / ‖w‖ ^ Kf)
    (hrel : ∀ x : ℝ, Tr ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
        H z = F (z⁻¹ ^ ((e : ℂ)⁻¹))) :
    ∃ (poly : Polynomial ℝ) (I : Finset ℝ) (a : ℝ → ℝ) (s s' A T : ℝ),
      s ∈ I ∧ (∀ σ ∈ I, σ ≤ s) ∧ (∀ i : ℕ, s ≠ (i : ℝ)) ∧ a s ≠ 0 ∧ s' < s ∧
      0 ≤ A ∧ (2 * (T₀ : ℝ)) ≤ T ∧ (2 : ℝ) ≤ T ∧ T₁ ≤ T ∧
      (∀ x : ℝ, T ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
        ‖H z - (poly.map (algebraMap ℝ ℂ)).eval z - ∑ σ ∈ I, (a σ : ℂ) * z ^ (σ : ℂ)‖
          ≤ A * x ^ s') := by
  obtain ⟨G, hGan, hFG⟩ := removable_pole_factor ρ Cf Kf F hρ hCf hFan hFgrow
  obtain ⟨m', hm'ne, hm'nn⟩ :
      ∃ m' : ℕ, iteratedDeriv m' G 0 ≠ 0 ∧ ∀ i : ℕ, ((Kf : ℝ) - (m' : ℝ)) / (e : ℝ) ≠ (i : ℝ) ∧
        ∀ m < m', ¬(iteratedDeriv m G 0 ≠ 0 ∧
          ∀ i : ℕ, ((Kf : ℝ) - (m : ℝ)) / (e : ℝ) ≠ (i : ℝ)) := by
    have h_exists_m' : ∃ m' : ℕ, iteratedDeriv m' G 0 ≠ 0 ∧
        ∀ i : ℕ, ((Kf : ℝ) - (m' : ℝ)) / (e : ℝ) ≠ (i : ℝ) := by
      have hT1T0 : (T₀ : ℝ) < T₁ := by
        rcases T₀ with ⟨_ | _ | T₀⟩ <;> norm_num at * <;> linarith
      apply DorgeBauer.laurent_nonnat_exp T₀ g ρ Kf F G hρ hg hgana hGan hFG hFan e he H T₁ Tr
        hTrb hTrT1 hT1T0 hagree hnp hrel
    obtain ⟨m', hm'⟩ :
        ∃ m' : ℕ, iteratedDeriv m' G 0 ≠ 0 ∧ ∀ i : ℕ, ((Kf : ℝ) - (m' : ℝ)) / (e : ℝ) ≠ (i : ℝ) ∧
          ∀ m < m', ¬(iteratedDeriv m G 0 ≠ 0 ∧
            ∀ i : ℕ, ((Kf : ℝ) - (m : ℝ)) / (e : ℝ) ≠ (i : ℝ)) := by
      have h_well_founded : WellFounded (fun m n : ℕ => m < n) := by
        exact wellFounded_lt
      have := h_well_founded.has_min
        { m | iteratedDeriv m G 0 ≠ 0 ∧ ∀ i : ℕ, (Kf - m : ℝ) / e ≠ i }
        ⟨h_exists_m'.choose, h_exists_m'.choose_spec⟩
      exact ⟨this.choose, this.choose_spec.1.1,
        fun i => ⟨this.choose_spec.1.2 i, fun m hm => fun h => this.choose_spec.2 m h hm⟩⟩
    use m'
  obtain ⟨R, T, M, hTrT, hT2, hM, hexp⟩ :
      ∃ R : ℂ → ℂ, ∃ T : ℝ, ∃ M : ℝ, Tr ≤ T ∧ 2 ≤ T ∧ 0 ≤ M ∧
        ∀ x : ℝ, T ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
          H z = (∑ m ∈ Finset.range (Kf + m' + 1),
                (iteratedDeriv m G 0 / (Nat.factorial m : ℂ)) * z ^ ((((Kf : ℝ) - m) / e : ℝ) : ℂ)) +
              z ^ ((((Kf : ℝ) - (Kf + m' + 1)) / e : ℝ) : ℂ) * R (z⁻¹ ^ ((e : ℂ)⁻¹)) ∧
            ‖R (z⁻¹ ^ ((e : ℂ)⁻¹))‖ ≤ M := by
    convert laurent_H_expansion_of_G ρ Kf F G hρ hGan hFG e he H Tr hTrb hrel (Kf + m' + 1) using 1
    norm_cast
  refine' ⟨laurentPoly G e Kf (Kf + m' + 1), laurentI G e Kf (Kf + m' + 1),
    laurentA G e Kf (Kf + m' + 1), (Kf - m' : ℝ) / e, (Kf - (Kf + m' + 1) : ℝ) / e,
    2 ^ |(Kf - (Kf + m' + 1) : ℝ) / e| * M, T, _, _, _, _, _⟩
  · refine' Finset.mem_image.mpr ⟨m', _, _⟩ <;> norm_num [hm'ne, hm'nn]
  · intro σ hσ
    unfold laurentI at hσ
    obtain ⟨m, hm₁, rfl⟩ := Finset.mem_image.mp hσ
    simp_all [Finset.mem_filter, Finset.mem_range]
    obtain ⟨a, ⟨ha₁, ha₂, ha₃⟩, rfl⟩ := hm₁
    gcongr
    exact le_of_not_gt fun h => (hm'nn 0 |>.2 a h ha₂).elim fun x hx => ha₃ x hx
  · exact fun i => hm'nn i |>.1
  · unfold laurentA
    rw [Finset.sum_eq_single m'] <;> simp +contextual [hm'ne, hm'nn]
    · have hreal : ∀ m : ℕ, (iteratedDeriv m G 0).im = 0 := by
        apply laurent_coeff_real ρ Kf F G hρ hGan hFG e he H g T₁ Tr hTrb hTrT1 hagree hrel
      exact ⟨fun h => hm'ne <| Complex.ext h <| hreal m', Nat.factorial_ne_zero _⟩
    · intro b hb₁ hb₂ hb₃ hb₄ hb₅
      specialize hm'nn b
      simp_all [div_eq_iff, ne_of_gt (zero_lt_one.trans_le he)]
  · have hss' : (Kf - (Kf + m' + 1) : ℝ) / e < (Kf - m' : ℝ) / e := by
      apply (div_lt_div_iff_of_pos_right (by positivity : 0 < (e : ℝ))).2
      linarith
    refine' ⟨_, _, _, _, _, _⟩
    any_goals linarith [show (e : ℝ) ≥ 1 by norm_cast, show (m' : ℝ) ≥ 0 by positivity, hss']
    · positivity
    · intro x hx z hz
      rw [hexp x hx z hz |>.1, sub_sub]
      rw [laurent_principal_eq G e Kf (Kf + m' + 1) he z (by
        rintro rfl
        norm_num at hz
        linarith [abs_of_nonneg (by linarith : 0 ≤ x)]) (by
        apply laurent_coeff_real ρ Kf F G hρ hGan hFG e he H g T₁ Tr hTrb hTrT1 hagree hrel)]
      simp +zetaDelta at *
      refine' le_trans (mul_le_mul_of_nonneg_left (hexp x hx z hz |>.2) (by positivity)) _
      convert mul_le_mul_of_nonneg_right (laurent_tail_term_bound z x
        ((Kf - (Kf + m' + 1) : ℝ) / e) ((Kf - (Kf + m' + 1) : ℝ) / e)
        (by linarith) hz le_rfl) hM using 1
      ring_nf
      · norm_num [mul_comm]
      · ring

/-
**Real algebraic branches are real-analytic on the open ray.** -/
lemma real_branch_analytic
    (P : Polynomial (Polynomial ℤ)) (_hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0) :
    AnalyticOnNhd ℝ g (Set.Ioi (T₀ : ℝ)) := by
  contrapose! hroot
  contrapose! hg
  intro h_cont_diff
  have h_analytic : AnalyticOnNhd ℝ g (Set.Ioi (T₀ : ℝ)) := by
    intro x hx
    have := h_cont_diff x (Set.mem_Ici.mpr hx.out.le)
    exact (this.contDiffAt (Ici_mem_nhds hx)).analyticAt
  contradiction

/-- **Isolated Puiseux tail core (root + growth given form).**

This is the crisp irreducible analytic residual behind `sphere_bound_of_continuation`, with
the two provable groundwork facts supplied as explicit hypotheses:

* `hHroot` — `H` is a genuine root of the complex family on each tail ball (proved as
  `H_root_on_ball`);
* `hgrowth` — `H` has uniform polynomial growth on the tail spheres (proved as
  `H_poly_growth_on_spheres`). -/
lemma puiseux_tail_of_root_growth
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (hnp : ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x)
    (T₁ : ℝ) (H : ℂ → ℂ) (hT1a : 2 * (T₀ : ℝ) ≤ T₁) (hT1b : (2 : ℝ) ≤ T₁)
    (hcont : ∀ x : ℝ, T₁ ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2)))
    (hagree : ∀ y : ℝ, T₁ / 2 ≤ y → H (y : ℂ) = (g y : ℂ))
    (hHroot : ∀ x : ℝ, T₁ ≤ x → ∀ z ∈ Metric.ball (x : ℂ) (x / 2),
        (P.map (evalIntPolyComplex z)).eval (H z) = 0)
    (C : ℝ) (N : ℕ) (hC : 0 ≤ C)
    (hgrowth : ∀ x : ℝ, T₁ ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
        ‖H z‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ (poly : Polynomial ℝ) (I : Finset ℝ) (a : ℝ → ℝ) (s s' A T : ℝ),
      s ∈ I ∧ (∀ σ ∈ I, σ ≤ s) ∧ (∀ i : ℕ, s ≠ (i : ℝ)) ∧ a s ≠ 0 ∧ s' < s ∧
      0 ≤ A ∧ (2 * (T₀ : ℝ)) ≤ T ∧ (2 : ℝ) ≤ T ∧ T₁ ≤ T ∧
      (∀ x : ℝ, T ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
        ‖H z - (poly.map (algebraMap ℝ ℂ)).eval z - ∑ σ ∈ I, (a σ : ℂ) * z ^ (σ : ℂ)‖
          ≤ A * x ^ s') := by
  -- Step 1: monodromy over the annulus at infinity gives the ramification index `e` and a
  -- single-valued holomorphic function `F` on a punctured disk with a finite-order pole.
  obtain ⟨e, ρ, Cf, Kf, F, Tr, he, hρ, hCf, hTra, hTrb, hTrT1, hFan, hFgrow, hrel⟩ :=
    monodromy_ramification_index P hP_monic T₀ g hg hroot hnp T₁ H hT1a hT1b hcont hagree
      hHroot C N hC hgrowth
  -- Step 2: the finite-order pole yields a convergent Laurent/Puiseux expansion, and the
  -- uniform growth bounds give the tail estimate.
  exact convergent_laurent_tail_bound P hP_monic T₀ g hg
    (real_branch_analytic P hP_monic T₀ g hg hroot) hroot hnp T₁ H hT1a hT1b hcont hagree
    hHroot e ρ Cf Kf F Tr he hρ hCf hTra hTrb hTrT1 hFan hFgrow hrel

/-- **Deep Newton–Puiseux tail bound (continuation-given form).**

This is the isolated deep analytic core remaining behind
`DorgeBauer.real_branch_full_holomorphic_continuation`.  It takes the holomorphic
continuation `H` of the real branch `g` (already available, on the tail balls, from
`DorgeBauer.real_branch_holo_continuation_tail`) as *given* and asserts the existence of the
finite Puiseux principal part (`poly` for the non-negative integer exponents, `∑_{σ ∈ I} a σ
· z^σ` for the rest, top exponent `s := max I` non-natural with `a s ≠ 0`, rate `s' < s`)
together with the uniform tail bound `‖H − principal part‖ ≤ A · x^{s'}` on the complex
spheres `sphere x (x/2)` for real `x ≥ T`. -/
lemma sphere_bound_of_continuation
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (hnp : ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x)
    (T₁ : ℝ) (H : ℂ → ℂ) (hT1a : 2 * (T₀ : ℝ) ≤ T₁) (hT1b : (2 : ℝ) ≤ T₁)
    (hcont : ∀ x : ℝ, T₁ ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2)))
    (hagree : ∀ y : ℝ, T₁ / 2 ≤ y → H (y : ℂ) = (g y : ℂ)) :
    ∃ (poly : Polynomial ℝ) (I : Finset ℝ) (a : ℝ → ℝ) (s s' A T : ℝ),
      s ∈ I ∧ (∀ σ ∈ I, σ ≤ s) ∧ (∀ i : ℕ, s ≠ (i : ℝ)) ∧ a s ≠ 0 ∧ s' < s ∧
      0 ≤ A ∧ (2 * (T₀ : ℝ)) ≤ T ∧ (2 : ℝ) ≤ T ∧ T₁ ≤ T ∧
      (∀ x : ℝ, T ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
        ‖H z - (poly.map (algebraMap ℝ ℂ)).eval z - ∑ σ ∈ I, (a σ : ℂ) * z ^ (σ : ℂ)‖
          ≤ A * x ^ s') := by
  -- `P` must have positive degree: a monic constant would have no roots, contradicting `hroot`.
  have hP_deg : 1 ≤ P.natDegree := by
    by_contra h
    push_neg at h
    interval_cases hd : P.natDegree
    have hP1 : P = 1 := by
      have hlc : P.coeff 0 = 1 := by
        have hm := hP_monic
        rwa [Polynomial.Monic, Polynomial.leadingCoeff, hd] at hm
      have hC := Polynomial.eq_C_of_natDegree_eq_zero hd
      rw [hC, hlc, map_one]
    have hev := hroot (T₀ : ℝ) le_rfl
    rw [hP1] at hev
    simp at hev
  -- Derive the two provable groundwork facts and apply the isolated Puiseux core.
  obtain ⟨C, N, hC, hgrowth⟩ :=
    H_poly_growth_on_spheres P hP_monic hP_deg T₀ g hroot T₁ H hT1a hT1b hcont hagree
  exact puiseux_tail_of_root_growth P hP_monic T₀ g hg hroot hnp T₁ H hT1a hT1b hcont hagree
    (fun x hx => H_root_on_ball P T₀ g hroot T₁ H hT1a hT1b hcont hagree x hx) C N hC hgrowth

/-- **Assembled deep input under an explicit separability hypothesis.**

Under the extra hypothesis that the complex family `P.map (evalIntPolyComplex z)` is
separable for all `‖z‖ > B`, this proves the full conclusion of
`DorgeBauer.real_branch_full_holomorphic_continuation` by assembling:

* the holomorphic-continuation half `DorgeBauer.real_branch_holo_continuation_tail`
  (giving a single `H`, holomorphic up to the boundary on every right-half tail ball,
  agreeing with `g` on the real ray), and
* the isolated Newton–Puiseux tail bound `sphere_bound_of_continuation`. -/
theorem real_branch_full_holomorphic_continuation_of_sep
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ) (B : ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (hnp : ¬ ∃ q : Polynomial ℝ, ∀ x : ℝ, (T₀ : ℝ) ≤ x → g x = q.eval x)
    (hsep : ∀ z : ℂ, B < ‖z‖ → (P.map (evalIntPolyComplex z)).Separable) :
    ∃ (poly : Polynomial ℝ) (I : Finset ℝ) (a : ℝ → ℝ) (s s' A T : ℝ) (H : ℂ → ℂ),
      s ∈ I ∧ (∀ σ ∈ I, σ ≤ s) ∧ (∀ i : ℕ, s ≠ (i : ℝ)) ∧ a s ≠ 0 ∧ s' < s ∧
      0 ≤ A ∧ (2 * (T₀ : ℝ)) ≤ T ∧ (2 : ℝ) ≤ T ∧
      (∀ x : ℝ, T ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2))) ∧
      (∀ y : ℝ, T / 2 ≤ y → H (y : ℂ) = (g y : ℂ)) ∧
      (∀ x : ℝ, T ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
        ‖H z - (poly.map (algebraMap ℝ ℂ)).eval z - ∑ σ ∈ I, (a σ : ℂ) * z ^ (σ : ℂ)‖
          ≤ A * x ^ s') := by
  obtain ⟨T₁, H, hT1a, hT1b, hcont, hagree⟩ :=
    real_branch_holo_continuation_tail P hP_monic T₀ g B hg.continuousOn hroot hsep
  obtain ⟨poly, I, a, s, s', A, T, hsI, hstop, hsnat, has, hss', hA, hTa, hTb, hTT1, hbound⟩ :=
    sphere_bound_of_continuation P hP_monic T₀ g hg hroot hnp T₁ H hT1a hT1b hcont hagree
  refine ⟨poly, I, a, s, s', A, T, H, hsI, hstop, hsnat, has, hss', hA, hTa, hTb, ?_, ?_, hbound⟩
  · exact fun x hx => hcont x (le_trans hTT1 hx)
  · exact fun y hy => hagree y (le_trans (by linarith [hTT1] : T₁ / 2 ≤ T / 2) hy)

end DorgeBauer
