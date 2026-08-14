/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Hilbert.Analytic.DorgeBauerBranches

/-!
# Analytic and complex-branch infrastructure for Dörge–Bauer

This file contains the complex-analytic and finite Puiseux-principal-part tools used by the
Newton–Puiseux stage of the Dörge–Bauer proof.  They are separated from the algebraic,
counting, and real-branch infrastructure in `DorgeBauer.lean` so downstream analytic files
can depend on a focused interface.

The results here do not assert existence of a convergent Newton–Puiseux expansion.  Instead,
they establish the direct finite-principal-part computation, derivative estimates from a
holomorphic extension, and local holomorphic continuation at a simple root.
-/

open Polynomial ResolventConstruction

noncomputable section

/- **Deep analytic classification kernel: the Newton–Puiseux dichotomy for one branch.**

A single smooth real branch `g` that is a genuine real root of `P` on a tail `[T₀, ∞)` is
either

* **bad** — *exactly a real polynomial* `q` on the tail (`g = q` there); or
* **good** — it carries a Newton–Puiseux leading derivative asymptotic
  `g⁽ᵐ⁾(x) ∼ c · (descPochhammer ℝ m).eval s · x^{s−m}` for all high `m` (`m ≥ m₀`), with
  a nonzero coefficient `c ≠ 0` and a non-natural exponent `s ∉ ℕ`.

This is the honest analytic core of the dichotomy: the branch's Puiseux expansion at
infinity either has only finitely many non-negative-integer exponents (bad, a polynomial)
or has a surviving non-integer exponent, whose top instance governs all high derivatives
(good). -/

section PuiseuxDataComputation
open Filter Topology

/-- **Dominant-term derivative asymptotic for a finite real Puiseux polynomial.**

For a finite real-power sum `F(x) = ∑_{σ ∈ I} a σ · x^σ` whose top exponent `s := max I`
lies in `I`, every iterated derivative is governed by the leading term:
`F⁽ᵐ⁾(x) / x^{s−m} → a s · (descPochhammer ℝ m).eval s`  as `x → ∞`.
(The lower exponents `σ < s` contribute `a σ · (descPochhammer ℝ m).eval σ · x^{σ−s} → 0`.) -/
lemma finite_puiseux_deriv_asymptotic
    (I : Finset ℝ) (a : ℝ → ℝ) (s : ℝ)
    (hsI : s ∈ I) (hstop : ∀ σ ∈ I, σ ≤ s) (m : ℕ) :
    Filter.Tendsto
      (fun x => iteratedDeriv m (fun y => ∑ σ ∈ I, a σ * y ^ σ) x / x ^ (s - (m : ℝ)))
      Filter.atTop (nhds (a s * Polynomial.eval s (descPochhammer ℝ m))) := by
  have h_eq : ∀ x : ℝ, 0 < x → iteratedDeriv m (fun y ↦ ∑ σ ∈ I, a σ * y ^ σ) x
      = ∑ σ ∈ I, a σ * Polynomial.eval σ (descPochhammer ℝ m) * x ^ (σ - (m:ℝ)) := by
    intro x hx
    clear hsI hstop
    induction I using Finset.induction with
    | empty => simp
    | insert σ' I' hσ' ih =>
      have hrpow : ∀ σ : ℝ, ContDiffAt ℝ (m:ℕ) (fun y : ℝ ↦ y ^ σ) x := fun σ ↦ by
        have : ContDiffAt ℝ (m:ℕ∞) (fun y : ℝ ↦ y ^ σ) x :=
          Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)
        exact_mod_cast this
      have hterm : ContDiffAt ℝ (m:ℕ) (fun y ↦ a σ' * y ^ σ') x :=
        (contDiffAt_const).mul (hrpow σ')
      have hsum : ContDiffAt ℝ (m:ℕ) (fun y ↦ ∑ σ ∈ I', a σ * y ^ σ) x := by
        apply ContDiffAt.sum
        intro σ hσ
        exact (contDiffAt_const).mul (hrpow σ)
      have hfun : (fun y ↦ ∑ σ ∈ insert σ' I', a σ * y ^ σ)
          = (fun y ↦ a σ' * y ^ σ') + (fun y ↦ ∑ σ ∈ I', a σ * y ^ σ) := by
        funext y
        simp [Finset.sum_insert hσ']
      rw [hfun, iteratedDeriv_add hterm hsum, ih, Finset.sum_insert hσ']
      congr 1
      rw [iteratedDeriv_const_mul (a σ') (hrpow σ'), iteratedDeriv_eq_iterate,
        Real.iter_deriv_rpow_const]
      ring
  have h_ev : (fun x ↦ iteratedDeriv m (fun y ↦ ∑ σ ∈ I, a σ * y ^ σ) x / x ^ (s - (m : ℝ)))
      =ᶠ[atTop] (fun x ↦ ∑ σ ∈ I, a σ * Polynomial.eval σ (descPochhammer ℝ m) * x ^ (σ - s)) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [h_eq x hx, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [mul_div_assoc, ← Real.rpow_sub hx, sub_sub_sub_cancel_right]
  rw [tendsto_congr' h_ev]
  have h_lim : Tendsto (fun x ↦ ∑ σ ∈ I, a σ * Polynomial.eval σ (descPochhammer ℝ m) * x ^ (σ - s))
      atTop (nhds (∑ σ ∈ I, if σ = s then a σ * Polynomial.eval σ (descPochhammer ℝ m) else 0)) := by
    apply tendsto_finset_sum
    intro σ hσ
    by_cases hσs : σ = s
    · rw [if_pos hσs, hσs]
      apply Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      rw [sub_self, Real.rpow_zero, mul_one]
    · rw [if_neg hσs]
      have hlt : σ - s < 0 := by
        have := hstop σ hσ
        rcases lt_or_eq_of_le this with h | h
        · linarith
        · exact absurd h hσs
      have ht : Tendsto (fun x : ℝ ↦ x ^ (σ - s)) atTop (nhds 0) := by
        have := tendsto_rpow_neg_atTop (y := s - σ) (by linarith)
        simpa [neg_sub] using this
      simpa using ht.const_mul (a σ * Polynomial.eval σ (descPochhammer ℝ m))
  have hval : (∑ σ ∈ I, if σ = s then a σ * Polynomial.eval σ (descPochhammer ℝ m) else 0)
      = a s * Polynomial.eval s (descPochhammer ℝ m) := by
    rw [Finset.sum_ite_eq' I s (fun σ ↦ a σ * Polynomial.eval σ (descPochhammer ℝ m))]
    simp [hsI]
  rwa [hval] at h_lim

/-- The `m`-th iterated derivative of the evaluation of a real polynomial is the
evaluation of the `m`-th formal derivative. -/
lemma iteratedDeriv_polynomial_eval (q : Polynomial ℝ) (m : ℕ) :
    iteratedDeriv m (fun y => q.eval y) = fun x => (Polynomial.derivative^[m] q).eval x := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [Function.iterate_succ']
    simp only [Function.comp_apply]
    exact Polynomial.deriv _

/-- Above its degree, every iterated derivative of a real polynomial vanishes. -/
lemma iteratedDeriv_polynomial_eval_zero (q : Polynomial ℝ) (m : ℕ)
    (h : q.natDegree < m) (x : ℝ) :
    iteratedDeriv m (fun y => q.eval y) x = 0 := by
  rw [iteratedDeriv_polynomial_eval, Polynomial.iterate_derivative_eq_zero h]
  simp

/-
**Real iterated derivatives are the real restriction of the holomorphic iterated
derivatives.**  If a real function `R` on an open real interval `(x−r, x+r)` is the
restriction of a function `G` that is holomorphic on the complex ball `ball x r`
(`G(y) = R(y)` for real `y` in the interval), then every real iterated derivative of `R`
is the real part / real restriction of the corresponding complex iterated derivative of
`G`:  `iteratedDeriv m G ↑y = ↑(iteratedDeriv m R y)` for all `y` in the interval.

This is the elementary real↔complex bridge used to transfer Cauchy's estimate on the
holomorphic extension into a bound on the real derivatives.  It is proved by induction on
`m`: at each step the complex derivative of the holomorphic iterate, restricted to the real
line (`HasDerivAt.comp_ofReal`), agrees with the real derivative of the real iterate
(`Complex.ofReal` is a continuous linear map), and holomorphic iterates stay holomorphic on
the open ball (`DifferentiableOn.analyticOnNhd`, `AnalyticOnNhd.deriv`).
-/
lemma iteratedDeriv_ofReal_eq_of_holo
    (R : ℝ → ℝ) (G : ℂ → ℂ) (x r : ℝ) (hr : 0 < r)
    (hGdiff : DifferentiableOn ℂ G (Metric.ball (x : ℂ) r))
    (hRsmooth : ContDiffOn ℝ ⊤ R (Set.Ioo (x - r) (x + r)))
    (hagree : ∀ y : ℝ, y ∈ Set.Ioo (x - r) (x + r) → G (y : ℂ) = (R y : ℂ))
    (m : ℕ) :
    ∀ y : ℝ, y ∈ Set.Ioo (x - r) (x + r) →
      iteratedDeriv m G (y : ℂ) = ((iteratedDeriv m R y : ℝ) : ℂ) := by
  have := hr
  have := hRsmooth
  induction' m with m ih <;> simp_all [iteratedDeriv_succ]
  intro y hy₁ hy₂
  have h := ih y hy₁ hy₂
  simp_all [Complex.ext_iff]
  have h_deriv : HasDerivAt (fun y ↦ iteratedDeriv m G y) (deriv (iteratedDeriv m G) y) y := by
    have h_an : AnalyticOnNhd ℂ (iteratedDeriv m G) (Metric.ball (x : ℂ) r) := by
      have h_deriv_eq : AnalyticOnNhd ℂ G (Metric.ball (x : ℂ) r) :=
        hGdiff.analyticOnNhd Metric.isOpen_ball
      refine Nat.recOn m ?_ ?_ <;> simp_all [iteratedDeriv_succ]
      exact fun n hn ↦ hn.deriv
    convert h_an.differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds <|
      show (y : ℂ) ∈ Metric.ball (x : ℂ) r from ?_) |> DifferentiableAt.hasDerivAt using 1
    simp [Complex.dist_eq, Complex.normSq, Complex.norm_def]
    rw [Real.sqrt_mul_self_eq_abs, abs_lt]
    constructor <;> linarith
  have h_deriv_real : HasDerivAt (fun y : ℝ ↦ (iteratedDeriv m G y).re)
      ((deriv (iteratedDeriv m G) y).re) y ∧
      HasDerivAt (fun y : ℝ ↦ (iteratedDeriv m G y).im) ((deriv (iteratedDeriv m G) y).im) y := by
    have h_dr : HasDerivAt (fun y : ℝ ↦ iteratedDeriv m G y)
        (deriv (iteratedDeriv m G) y) y := h_deriv.comp_ofReal
    refine ⟨?_, ?_⟩
    · simpa using Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h_dr
    · simpa using Complex.imCLM.hasFDerivAt.comp_hasDerivAt y h_dr
  have h_deriv_real_eq : HasDerivAt (fun y : ℝ ↦ iteratedDeriv m R y)
      ((deriv (iteratedDeriv m G) y).re) y ∧
      HasDerivAt (fun y : ℝ ↦ 0) ((deriv (iteratedDeriv m G) y).im) y := by
    refine ⟨?_, ?_⟩
    · exact h_deriv_real.1.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
        (Ioo_mem_nhds hy₁ hy₂) fun z hz ↦ by rw [ih z hz.1 hz.2 |>.1])
    · exact h_deriv_real.2.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
        (Ioo_mem_nhds hy₁ hy₂) fun z hz ↦ by rw [ih z hz.1 hz.2 |>.2])
  refine ⟨?_, ?_⟩
  · rw [← h_deriv_real_eq.1.deriv]
  · simpa using h_deriv_real_eq.2.deriv.symm

/-
**Cauchy estimate for a real function via a holomorphic extension.**  If a real function
`R` on the open interval `(x−r, x+r)` is the restriction of a function `G` that is
holomorphic on `ball x r`, continuous on its closure (`DiffContOnCl`), and bounded by `M`
on the boundary sphere, then the `m`-th real iterated derivative of `R` at `x` obeys the
classical Cauchy bound `|R⁽ᵐ⁾(x)| ≤ m! · M / r^m`.

This is the analytic engine that turns a holomorphic Puiseux representation of an algebraic
branch (bounded by a power `|G(z)| ≤ A·|z|^{s'}` on complex tail balls) into the per-order
remainder bounds `|R⁽ᵐ⁾(x)| ≤ C_m·x^{s'−m}`.  It combines Mathlib's Cauchy estimate
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` with the real↔complex bridge
`iteratedDeriv_ofReal_eq_of_holo`.
-/
lemma abs_iteratedDeriv_le_of_holo_extension
    (R : ℝ → ℝ) (G : ℂ → ℂ) (x r M : ℝ) (m : ℕ)
    (hr : 0 < r)
    (hDC : DiffContOnCl ℂ G (Metric.ball (x : ℂ) r))
    (hRsmooth : ContDiffOn ℝ ⊤ R (Set.Ioo (x - r) (x + r)))
    (hagree : ∀ y : ℝ, y ∈ Set.Ioo (x - r) (x + r) → G (y : ℂ) = (R y : ℂ))
    (hbound : ∀ z ∈ Metric.sphere (x : ℂ) r, ‖G z‖ ≤ M) :
    |iteratedDeriv m R x| ≤ (m.factorial : ℝ) * M / r ^ m := by
  have h_cauchy : ‖iteratedDeriv m G (x : ℂ)‖ ≤ (m.factorial : ℝ) * M / r ^ m := by
    apply_rules [Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le]
  convert h_cauchy using 1
  rw [iteratedDeriv_ofReal_eq_of_holo R G x r hr hDC.differentiableOn hRsmooth hagree m x
    ⟨by linarith, by linarith⟩]
  norm_num

/- **Deep Newton–Puiseux input (principal-part form): existence of the finite Puiseux
principal part of a non-polynomial real algebraic branch.** (Background note.)

This is the cleaned-up, *computational* form of the deep analytic input behind
`real_root_branch_puiseux_data`.  For a smooth real branch `g` of the monic family
`P(x, ·)` on a tail `[T₀, ∞)` that is *not* eventually a real polynomial, it asserts the
existence of a *polynomial part* `poly(x)` (the natural-exponent, integer-power part of the
expansion) together with a finite non-integer Puiseux part `F(x) = ∑_{σ ∈ I} a σ · x^σ`,
with a top exponent `s := max I` that is non-natural (`s ∉ ℕ`) and has nonzero coefficient
`a s ≠ 0`, such that the remainder `g − poly − F` decays faster than the leading term in
*every* derivative order: `(g − poly − F)⁽ᵐ⁾(x) = o(x^{s−m})` as `x → ∞`.

The polynomial part separates the integer-power terms from the top non-integer exponent
that detects the non-polynomial character of `g`. -/
/-- The polynomial-plus-Puiseux principal part is holomorphic on the relevant closed ball. -/
theorem puiseux_principal_part_diffContOnCl
    (x : ℝ) (hx : 2 ≤ x) (poly : Polynomial ℂ) (I : Finset ℝ) (a : ℝ → ℂ) :
    DiffContOnCl ℂ (fun z : ℂ => poly.eval z + ∑ σ ∈ I, a σ * z ^ (σ : ℂ))
      (Metric.ball (x : ℂ) (x / 2)) := by
  apply DifferentiableOn.diffContOnCl
  have hcl : closure (Metric.ball (x : ℂ) (x / 2)) = Metric.closedBall (x : ℂ) (x / 2) := by
    rw [closure_ball]
    positivity
  rw [hcl]
  have hslit : ∀ z ∈ Metric.closedBall (x : ℂ) (x / 2), z ∈ Complex.slitPlane := by
    intro z hz
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    have h2 : |z.re - x| ≤ ‖z - x‖ := by simpa using Complex.abs_re_le_norm (z - x)
    have := abs_le.mp (h2.trans hz)
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    linarith [this.1]
  apply DifferentiableOn.add (poly.differentiable.differentiableOn)
  have hrw : (fun z : ℂ ↦ ∑ σ ∈ I, a σ * z ^ (σ : ℂ))
      = ∑ σ ∈ I, (fun z : ℂ ↦ a σ * z ^ (σ : ℂ)) := by
    ext z
    simp [Finset.sum_apply]
  rw [hrw]
  apply DifferentiableOn.sum
  intro σ hσ
  apply DifferentiableOn.const_mul
  intro z hz
  exact (DifferentiableAt.cpow differentiableAt_id (differentiableAt_const _)
    (hslit z hz)).differentiableWithinAt

/-- **Complex evaluation of the integer-coefficient family.**  The complex analogue of
`evalIntPolyReal`: map the integer coefficients into `ℂ` and evaluate the outer polynomial at
a complex point `z`.  This is the ambient map whose holomorphic root branches provide the
complex continuation of the real branches. -/
noncomputable def evalIntPolyComplex (z : ℂ) : Polynomial ℤ →+* ℂ :=
  (Polynomial.evalRingHom z).comp (Polynomial.mapRingHom (Int.castRingHom ℂ))

/-- The complex family `(z, w) ↦ P.map (evalIntPolyComplex z) |>.eval w` is holomorphic
(`ContDiff ℂ ⊤`) in both variables, being a polynomial expression.  This is the complex
analogue of `evalIntPolyReal_eval_contDiff` and is the smoothness input for the complex
implicit-function step. -/
lemma evalIntPolyComplex_eval_contDiff (P : Polynomial (Polynomial ℤ)) :
    ContDiff ℂ ⊤ (fun p : ℂ × ℂ => (P.map (evalIntPolyComplex p.1)).eval p.2) := by
  unfold evalIntPolyComplex
  simp [Polynomial.eval_map]
  rw [Polynomial.as_sum_range_C_mul_X_pow P]
  simp [Polynomial.eval₂_finset_sum]
  refine ContDiff.sum fun i _ ↦ ContDiff.mul ?_ ?_
  · simp [Polynomial.eval_eq_sum_range]
    exact ContDiff.sum fun _ _ ↦ ContDiff.mul (contDiff_const) (contDiff_fst.pow _)
  · exact contDiff_snd.pow i

/-
On the real axis the complex family agrees with the complexification of the real family:
`(P.map (evalIntPolyComplex x)).eval y = ((P.map (evalIntPolyReal x)).eval y : ℂ)` for real
`x, y`.  This bridges the real root branch to its complex continuation.
-/
lemma evalIntPolyComplex_ofReal (P : Polynomial (Polynomial ℤ)) (x y : ℝ) :
    (P.map (evalIntPolyComplex (x : ℂ))).eval (y : ℂ)
      = (((P.map (evalIntPolyReal x)).eval y : ℝ) : ℂ) := by
  unfold evalIntPolyComplex evalIntPolyReal
  simp [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]

/-- Real-axis agreement for the `Y`-derivative of the complex family: for real `x, y`,
`(P.map (evalIntPolyComplex x)).derivative.eval y = ((P.map (evalIntPolyReal x)).derivative.eval y : ℂ)`.
Together with `evalIntPolyComplex_ofReal` this shows a *simple* real root of the real family
is a *simple* complex root of the complex family, feeding `complex_branch_at_simple_root`. -/
lemma evalIntPolyComplex_derivative_ofReal (P : Polynomial (Polynomial ℤ)) (x y : ℝ) :
    (P.map (evalIntPolyComplex (x : ℂ))).derivative.eval (y : ℂ)
      = (((P.map (evalIntPolyReal x)).derivative.eval y : ℝ) : ℂ) := by
  rw [Polynomial.derivative_map, Polynomial.derivative_map,
    ← evalIntPolyComplex_ofReal P.derivative x y]

/-- **Local holomorphic branch at a simple complex root.**  The complex analogue of
`real_branch_at_simple_root`: if `w₀` is a *simple* complex root of the specialization
`P.map (evalIntPolyComplex z₀)` (root with nonzero `Y`-derivative), then there is a
holomorphic (`ContDiffAt ℂ ⊤`) function `φ` near `z₀` with `φ z₀ = w₀` that is a genuine root
of the complex family in a neighbourhood of `z₀`.  This is the complex implicit-function-
theorem step underlying the holomorphic continuation of a real branch off the real axis. -/
lemma complex_branch_at_simple_root (P : Polynomial (Polynomial ℤ)) (z₀ w₀ : ℂ)
    (hroot : (P.map (evalIntPolyComplex z₀)).eval w₀ = 0)
    (hsimple : (P.map (evalIntPolyComplex z₀)).derivative.eval w₀ ≠ 0) :
    ∃ φ : ℂ → ℂ, φ z₀ = w₀ ∧ ContDiffAt ℂ ⊤ φ z₀ ∧
      ∀ᶠ z : ℂ in nhds z₀, (P.map (evalIntPolyComplex z)).eval (φ z) = 0 := by
  set F : ℂ × ℂ → ℂ := fun p ↦ (P.map (evalIntPolyComplex p.1)).eval p.2
  have hdiffF : Differentiable ℂ F := (evalIntPolyComplex_eval_contDiff P).differentiable (by norm_num)
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, HasFDerivAt F (fderiv ℂ F (z₀, w₀)) (z₀, w₀) ∧
      ContDiffAt ℂ ⊤ φ z₀ ∧ φ z₀ = w₀ ∧ ∀ᶠ z in nhds z₀, F (z, φ z) = F (z₀, w₀) := by
    have h_implicit : IsContDiffImplicitAt ⊤ F (fderiv ℂ F (z₀, w₀)) (z₀, w₀) := by
      constructor
      · exact (hdiffF _).hasFDerivAt
      · exact evalIntPolyComplex_eval_contDiff P |> ContDiff.contDiffAt
      · have hL : ∀ z, (fderiv ℂ F (z₀, w₀)).comp (ContinuousLinearMap.inr ℂ ℂ ℂ) z =
            (Polynomial.derivative (P.map (evalIntPolyComplex z₀))).eval w₀ * z := by
          have hderiv : deriv (fun w ↦ (P.map (evalIntPolyComplex z₀)).eval w) w₀ =
              (fderiv ℂ F (z₀, w₀)).comp (ContinuousLinearMap.inr ℂ ℂ ℂ) 1 := by
            convert HasDerivAt.deriv _ using 1
            have hFdiff : HasFDerivAt F (fderiv ℂ F (z₀, w₀)) (z₀, w₀) :=
              (hdiffF (z₀, w₀)).hasFDerivAt
            convert HasFDerivAt.hasDerivAt (HasFDerivAt.comp w₀ hFdiff
              (HasFDerivAt.prodMk (hasFDerivAt_const _ _) (hasFDerivAt_id _))) using 1
          intro z
          have hmid : (fderiv ℂ F (z₀, w₀)).comp (ContinuousLinearMap.inr ℂ ℂ ℂ) z =
              deriv (fun w ↦ (P.map (evalIntPolyComplex z₀)).eval w) w₀ * z := by
            rw [hderiv, mul_comm]
            convert (ContinuousLinearMap.map_smul ((fderiv ℂ F (z₀, w₀)).comp
              (ContinuousLinearMap.inr ℂ ℂ ℂ)) z 1) using 1
            norm_num
          convert hmid using 1
          norm_num [Polynomial.derivative_eval]
        constructor
        · exact fun z w hzw ↦ mul_left_cancel₀ hsimple <| by simp_all
        · refine fun z ↦ ⟨z / (Polynomial.eval w₀ (Polynomial.derivative
            (Polynomial.map (evalIntPolyComplex z₀) P))), ?_⟩
          rw [hL, mul_div_cancel₀ _ hsimple]
      · decide +revert
    refine ⟨h_implicit.implicitFunction, ?_, ?_, ?_, ?_⟩
    · exact h_implicit.hasFDerivAt
    · exact h_implicit.contDiffAt_implicitFunction
    · convert h_implicit.eventually_implicitFunction_apply_eq.self_of_nhds using 1
      simp
    · exact h_implicit.apply_implicitFunction
  grind

/-- **Local holomorphic continuation of a real branch off the real axis.**  If the real
specialization `P.map (evalIntPolyReal x₀)` is *separable* and `w₀` is a real root of it,
then there is a holomorphic function `φ : ℂ → ℂ` on a complex neighbourhood of `x₀` with
`φ x₀ = w₀` that is a genuine root of the *complex* family `P.map (evalIntPolyComplex z)`
there.  This packages `complex_branch_at_simple_root` with the two real-axis bridges
(`evalIntPolyComplex_ofReal`, `evalIntPolyComplex_derivative_ofReal`) and the
separability⇒simple-root fact, giving the local complex continuation of the real branch —
the local core toward `real_branch_full_holomorphic_continuation`. -/
lemma real_branch_local_holomorphic_continuation
    (P : Polynomial (Polynomial ℤ)) (x₀ w₀ : ℝ)
    (hsep : (P.map (evalIntPolyReal x₀)).Separable)
    (hroot0 : (P.map (evalIntPolyReal x₀)).eval w₀ = 0) :
    ∃ φ : ℂ → ℂ, ContDiffAt ℂ ⊤ φ (x₀ : ℂ) ∧ φ (x₀ : ℂ) = (w₀ : ℂ) ∧
      ∀ᶠ z : ℂ in nhds (x₀ : ℂ), (P.map (evalIntPolyComplex z)).eval (φ z) = 0 := by
  have hroot : (P.map (evalIntPolyComplex (x₀ : ℂ))).eval (w₀ : ℂ) = 0 := by
    rw [evalIntPolyComplex_ofReal, hroot0]
    simp
  have hsimple : (P.map (evalIntPolyComplex (x₀ : ℂ))).derivative.eval (w₀ : ℂ) ≠ 0 := by
    rw [evalIntPolyComplex_derivative_ofReal]
    simpa using eval_derivative_ne_zero_of_separable hsep hroot0
  obtain ⟨φ, hφ0, hφcd, hφroot⟩ :=
    complex_branch_at_simple_root P (x₀ : ℂ) (w₀ : ℂ) hroot hsimple
  exact ⟨φ, hφcd, hφ0, hφroot⟩

/-
**Holomorphic extensions of a real branch are automatically root-branches.**

If `H` is holomorphic on the right-half tail ball `ball x (x/2)` (centre a real `x` with
`2·T₀ ≤ x` and `2 ≤ x`) and agrees, on the real diameter `(x/2, 3x/2)`, with a real branch
`g` that is a genuine root of the family `P(·, ·)` on `[T₀, ∞)`, then `H` is a genuine root of
the *complex* family `P.map (evalIntPolyComplex z)` on the entire ball.

This is the identity-theorem (analytic-continuation) core of the holomorphic continuation:
once *any* holomorphic extension of the real branch exists, the root property propagates off
the real axis for free.  Proof: the map `Φ z := (P.map (evalIntPolyComplex z)).eval (H z)` is
holomorphic on the (connected) ball and vanishes on the real diameter — a set that
accumulates at the centre `x` — so by the identity theorem `Φ ≡ 0` on the ball.
-/
lemma complex_branch_root_of_holo_extension
    (P : Polynomial (Polynomial ℤ)) (T₀ : ℤ) (g : ℝ → ℝ)
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (x : ℝ) (hxT : 2 * (T₀ : ℝ) ≤ x) (hx2 : (2 : ℝ) ≤ x)
    (H : ℂ → ℂ)
    (hHolo : DifferentiableOn ℂ H (Metric.ball (x : ℂ) (x / 2)))
    (hHag : ∀ y : ℝ, |y - x| < x / 2 → H (y : ℂ) = (g y : ℂ)) :
    ∀ z ∈ Metric.ball (x : ℂ) (x / 2),
      (P.map (evalIntPolyComplex z)).eval (H z) = 0 := by
  set Φ : ℂ → ℂ := fun z ↦ (P.map (evalIntPolyComplex z)).eval (H z)
  -- Apply the identity theorem for holomorphic functions.
  have h_id : AnalyticOnNhd ℂ Φ (Metric.ball (x : ℂ) (x / 2)) ∧
      (∀ y : ℝ, |y - x| < x / 2 → Φ (y : ℂ) = 0) := by
    constructor
    · apply DifferentiableOn.analyticOnNhd
      · have hcd : Differentiable ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2) :=
          (evalIntPolyComplex_eval_contDiff P).differentiable (by norm_num)
        convert hcd.comp_differentiableOn (differentiableOn_id.prodMk hHolo) using 1
      · exact Metric.isOpen_ball
    · intro y hy
      have hy' : (T₀ : ℝ) ≤ y := by linarith [abs_lt.mp hy]
      convert congr_arg ((↑) : ℝ → ℂ) (hroot y hy') using 1
      convert evalIntPolyComplex_ofReal P y (g y) using 1
      simp_all only [Φ]
  have h_id : ∀ z ∈ Metric.ball (x : ℂ) (x / 2), Φ z = 0 := by
    intro z hz
    have h_acc : ∃ᶠ y in nhdsWithin (x : ℂ) { (x : ℂ) }ᶜ, Φ y = 0 := by
      rw [Metric.nhdsWithin_basis_ball.frequently_iff]
      intro ε ε_pos
      refine ⟨↑ (x + Min.min ε (x / 2) / 2), ?_, ?_⟩ <;>
        norm_num [abs_of_pos, ε_pos, hx2]
      · refine ⟨?_, by positivity⟩
        rw [abs_of_nonneg (by positivity)]
        linarith [min_le_left ε (x / 2), min_le_right ε (x / 2)]
      · convert h_id.2 (x + Min.min ε (x / 2) / 2) _ using 1
        · norm_num [Complex.ofReal_add, Complex.ofReal_div]
        · have hmin : 0 < Min.min ε (x / 2) := by positivity
          rw [abs_of_nonneg] <;>
            linarith [min_le_left ε (x / 2), min_le_right ε (x / 2)]
    refine h_id.left.eqOn_zero_of_preconnected_of_frequently_eq_zero (z₀ := ↑x)
      (convex_ball _ _).isPreconnected ?_ h_acc hz
    simp only [Metric.mem_ball, dist_self]
    linarith
  exact h_id

/-
**Uniqueness / gluing of holomorphic extensions of a real branch.**

If `H₁` is holomorphic on `ball x₁ r₁` and `H₂` on `ball x₂ r₂`, and both agree on their
respective real diameters with the *same* real function `g`, and the two open balls share a
real point `(y₀ : ℂ)` (with `y₀` real), then `H₁` and `H₂` agree on the entire (convex, hence
connected) intersection `ball x₁ r₁ ∩ ball x₂ r₂`.

This is the gluing step that turns the local holomorphic continuations on overlapping tail
balls into a single-valued function: on the overlap both branches equal `g` on a real
segment accumulating at `y₀`, so by the identity theorem they coincide throughout the
overlap.
-/
lemma holo_extension_unique_on_inter
    (g : ℝ → ℝ) (x₁ x₂ r₁ r₂ y₀ : ℝ)
    (H₁ H₂ : ℂ → ℂ)
    (hH₁ : DifferentiableOn ℂ H₁ (Metric.ball (x₁ : ℂ) r₁))
    (hH₂ : DifferentiableOn ℂ H₂ (Metric.ball (x₂ : ℂ) r₂))
    (hag₁ : ∀ y : ℝ, |y - x₁| < r₁ → H₁ (y : ℂ) = (g y : ℂ))
    (hag₂ : ∀ y : ℝ, |y - x₂| < r₂ → H₂ (y : ℂ) = (g y : ℂ))
    (hy₁ : |y₀ - x₁| < r₁) (hy₂ : |y₀ - x₂| < r₂) :
    Set.EqOn H₁ H₂ (Metric.ball (x₁ : ℂ) r₁ ∩ Metric.ball (x₂ : ℂ) r₂) := by
  set D : ℂ → ℂ := fun z ↦ H₁ z - H₂ z
  -- By the identity theorem, since `D` is holomorphic on the intersection of the two balls and
  -- vanishes on a set with an accumulation point, `D` is identically zero on the intersection.
  have hD_zero : ∀ z ∈ Metric.ball (x₁ : ℂ) r₁ ∩ Metric.ball (x₂ : ℂ) r₂, D z = 0 := by
    have h_acc : ∃ᶠ z in nhdsWithin (y₀ : ℂ) { (y₀ : ℂ) }ᶜ, D z = 0 := by
      rw [Metric.nhdsWithin_basis_ball.frequently_iff]
      intro ε ε_pos
      obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ y : ℝ, |y - y₀| < δ → |y - x₁| < r₁ ∧ |y - x₂| < r₂ := by
        exact Metric.mem_nhds_iff.mp (IsOpen.mem_nhds
          (isOpen_lt (continuous_abs.comp (continuous_sub_right _)) continuous_const |>
            IsOpen.inter <| isOpen_lt (continuous_abs.comp (continuous_sub_right _)) continuous_const)
          ⟨hy₁, hy₂⟩)
      refine ⟨y₀ + Min.min ε δ / 2, ?_, ?_⟩ <;> norm_num
      · refine ⟨?_, by positivity⟩
        rw [abs_of_nonneg (by positivity)]
        linarith [min_le_left ε δ, min_le_right ε δ]
      · simp only [D]
        have hmin : 0 < Min.min ε δ := by positivity
        have hlt : |y₀ + Min.min ε δ / 2 - y₀| < δ := by
          rw [abs_of_nonneg] <;>
            linarith [min_le_left ε δ, min_le_right ε δ]
        convert sub_eq_zero.mpr (hag₁ (y₀ + Min.min ε δ / 2) (hδ _ hlt).1 |> Eq.trans <|
          hag₂ (y₀ + Min.min ε δ / 2) (hδ _ hlt).2 |> Eq.symm) using 1
        norm_num [Complex.ext_iff]
    apply_rules [AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero]
    · exact DifferentiableOn.analyticOnNhd (hH₁.mono (Set.inter_subset_left) |>
        DifferentiableOn.sub <| hH₂.mono (Set.inter_subset_right))
        (Metric.isOpen_ball.inter Metric.isOpen_ball)
    · exact Convex.isPreconnected (convex_ball _ _ |> fun h ↦ h.inter (convex_ball _ _))
    · simp_all [Complex.dist_eq, Complex.normSq, Complex.norm_def]
      refine ⟨?_, ?_⟩ <;> rwa [Real.sqrt_mul_self_eq_abs]
  exact fun z hz ↦ sub_eq_zero.mp (hD_zero z hz)

/-
**Local holomorphic continuation of a real branch, agreeing with `g` on the real axis.**

Strengthening of `real_branch_local_holomorphic_continuation`: if the real specialization
`P.map (evalIntPolyReal x₀)` is *separable* and `g` is a smooth real function that is a
genuine root of the family near `x₀` with `g x₀ = w₀`, then the local holomorphic branch `φ`
of the *complex* family at `(x₀, w₀)` in fact *agrees with `g`* on the real axis near `x₀`
(`φ (x : ℂ) = (g x : ℂ)` for real `x` near `x₀`).

This is the local input to the gluing step (`holo_extension_unique_on_inter`): the complex
continuation restricted to the real axis really is (the complexification of) `g`, not some
other root branch.  Proof: `φ₀ x := φ (x : ℂ)` and `g` are both smooth real root branches of
the family through the *simple* root `(x₀, w₀)`; writing the difference of the two
vanishing evaluations as `(g x - φ₀ x) · (∂_w F near (x₀, w₀))` and using that the bracket is
nonzero near `x₀` (continuity, `hsimple`), we get `g x = φ₀ x` near `x₀`.
-/
lemma real_branch_local_holomorphic_continuation_agrees
    (P : Polynomial (Polynomial ℤ)) (x₀ w₀ : ℝ)
    (hsep : (P.map (evalIntPolyReal x₀)).Separable)
    (g : ℝ → ℝ) (hg : ContDiffAt ℝ ⊤ g x₀) (hgval : g x₀ = w₀)
    (hgroot : ∀ᶠ x : ℝ in nhds x₀, (P.map (evalIntPolyReal x)).eval (g x) = 0) :
    ∃ φ : ℂ → ℂ, ContDiffAt ℂ ⊤ φ (x₀ : ℂ) ∧ φ (x₀ : ℂ) = (w₀ : ℂ) ∧
      (∀ᶠ x : ℝ in nhds x₀, φ (x : ℂ) = (g x : ℂ)) ∧
      (∀ᶠ z : ℂ in nhds (x₀ : ℂ), (P.map (evalIntPolyComplex z)).eval (φ z) = 0) := by
  have hw0root : (P.map (evalIntPolyReal x₀)).eval w₀ = 0 := by
    simpa [hgval] using hgroot.self_of_nhds
  -- Choose any `φ` that satisfies the conditions.
  obtain ⟨φ, hφ⟩ := real_branch_local_holomorphic_continuation P x₀ w₀ hsep hw0root
  have h_implicit : IsContDiffImplicitAt ⊤ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2)
      (fderiv ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2) (x₀, w₀)) (x₀, w₀) := by
    constructor
    · have h_diff := (evalIntPolyComplex_eval_contDiff P).differentiable (by norm_num) (x₀, w₀)
      exact h_diff.hasFDerivAt
    · exact evalIntPolyComplex_eval_contDiff P |> ContDiff.contDiffAt
    · have hDne : (P.map (evalIntPolyComplex (x₀ : ℂ))).derivative.eval (w₀ : ℂ) ≠ 0 := by
        have hDne_real : (P.map (evalIntPolyReal x₀)).derivative.eval w₀ ≠ 0 :=
          eval_derivative_ne_zero_of_separable hsep hw0root
        convert hDne_real using 1
        rw [← Complex.ofReal_inj]
        norm_num [evalIntPolyComplex_ofReal, evalIntPolyComplex_derivative_ofReal]
      have hDfd : (fderiv ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2)
          (x₀, w₀)) (0, 1) = (P.map (evalIntPolyComplex (x₀ : ℂ))).derivative.eval (w₀ : ℂ) := by
        have hDfd_deriv : (fderiv ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2)
            (x₀, w₀)) (0, 1) = (deriv (fun y : ℂ ↦ (P.map (evalIntPolyComplex (x₀ : ℂ))).eval y) (w₀ : ℂ)) := by
          rw [deriv]
          have hcomp : (fun y : ℂ ↦ eval y (Polynomial.map (evalIntPolyComplex ↑x₀) P)) =
              (fun p : ℂ × ℂ ↦ eval p.2 (Polynomial.map (evalIntPolyComplex p.1) P)) ∘
                (fun y : ℂ ↦ (↑x₀, y)) := by
            ext
            simp
          rw [hcomp, fderiv_comp] <;> norm_num
          · rw [HasDerivAt.deriv (by simpa using HasDerivAt.prodMk (hasDerivAt_const _ _) (hasDerivAt_id _))]
          · convert evalIntPolyComplex_eval_contDiff P |> ContDiff.contDiffAt |>
              ContDiffAt.differentiableAt <| by norm_num using 1
          · exact differentiableAt_const _ |> DifferentiableAt.prodMk <| differentiableAt_id
        convert hDfd_deriv using 1
        simp
      constructor
      · intro a b hab
        simp_all [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
        have hDa : (fderiv ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2)
            (x₀, w₀)) (0, a) = a * (P.map (evalIntPolyComplex (x₀ : ℂ))).derivative.eval (w₀ : ℂ) := by
          convert congr_arg (fun x ↦ a * x) hDfd using 1
          · rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul]
            norm_num [Prod.smul_def]
          · simp [Polynomial.derivative_map]
        have hDb : (fderiv ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2)
            (x₀, w₀)) (0, b) = b * (P.map (evalIntPolyComplex (x₀ : ℂ))).derivative.eval (w₀ : ℂ) := by
          convert congr_arg (fun x ↦ b * x)
            ‹(fderiv ℂ (fun p : ℂ × ℂ ↦ eval p.2 (Polynomial.map (evalIntPolyComplex p.1) P)) (x₀, w₀)) (0, 1) =
              eval (w₀ : ℂ) (Polynomial.map (evalIntPolyComplex x₀) (derivative P))› using 1
          · rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul]
            norm_num [Prod.smul_def]
          · simp [Polynomial.derivative_map]
        simp_all [Polynomial.derivative_map]
      · intro y
        use y / (fderiv ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2) (x₀, w₀)) (0, 1)
        simp_all
        have hkey : (fderiv ℂ (fun p : ℂ × ℂ ↦ eval p.2 (Polynomial.map (evalIntPolyComplex p.1) P))
            (x₀, w₀)) (0, y / eval (w₀ : ℂ) (Polynomial.map (evalIntPolyComplex x₀) (derivative P))) =
            (y / eval (w₀ : ℂ) (Polynomial.map (evalIntPolyComplex x₀) (derivative P))) *
              (fderiv ℂ (fun p : ℂ × ℂ ↦ eval p.2 (Polynomial.map (evalIntPolyComplex p.1) P))
                (x₀, w₀)) (0, 1) := by
          rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul]
          norm_num [hDfd]
        rw [hkey]
        simp_all
    · decide +revert
  refine ⟨h_implicit.implicitFunction, ?_, ?_, ?_, ?_⟩
  · exact h_implicit.contDiffAt_implicitFunction
  · convert h_implicit.eventually_implicitFunction_apply_eq.self_of_nhds using 1
    grind
  · have hEqImpl : ∀ᶠ (xy : ℂ × ℂ) in nhds (x₀, w₀),
        (P.map (evalIntPolyComplex xy.1)).eval xy.2 = 0 → h_implicit.implicitFunction xy.1 = xy.2 := by
      convert h_implicit.eventually_implicitFunction_apply_eq using 1
      simp [evalIntPolyComplex_ofReal]
      rw [hw0root]
      norm_num
    have hEqRoot : ∀ᶠ (x : ℝ) in nhds x₀, (P.map (evalIntPolyComplex (x : ℂ))).eval (g x : ℂ) = 0 := by
      filter_upwards [hgroot] with x hx
      simpa [evalIntPolyComplex_ofReal] using congr_arg ((↑) : ℝ → ℂ) hx
    have hTend : Filter.Tendsto (fun x : ℝ ↦ ((x : ℂ), (g x : ℂ))) (nhds x₀) (nhds (x₀, w₀)) :=
      Filter.Tendsto.prodMk_nhds (Complex.continuous_ofReal.continuousAt)
        (Complex.continuous_ofReal.continuousAt.comp hg.continuousAt) |> fun h ↦ h.trans (by simp_all)
    filter_upwards [hTend.eventually hEqImpl, hEqRoot] with x hx₁ hx₂ using hx₁ hx₂
  · convert h_implicit.apply_implicitFunction using 1
    ext
    simp [evalIntPolyComplex_ofReal]
    rw [hw0root]
    norm_num

end PuiseuxDataComputation

end
