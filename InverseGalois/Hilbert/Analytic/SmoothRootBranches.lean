/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Real root branches of a smooth separable family of monic polynomials

* The **implicit function theorem** (Dini, 1877) turns each *simple* real root of a smooth
  family into a local smooth branch, and gives *local uniqueness* of that root.
* **Cauchy's root bound** (1829) confines all real roots to a compact set that varies
  continuously with the parameter, so on a compact parameter interval the roots stay in a
  fixed compact box.
* A **compactness** argument (Bolzano–Weierstrass / Heine–Borel) then shows that near any
  parameter value the real roots are *exactly* the finitely many local branches, so the
  number of distinct real roots is **locally constant**.
* **Connectedness** of a half-line upgrades "locally constant" to "constant".
* Finally the real roots are organised into the finitely many **order statistics** (the
  `j`-th smallest real root), each of which is smooth because it locally coincides with one
  of the implicit-function branches.

The main result is `smooth_separable_family_root_branches`.

## Main definitions and results

* `SmoothRootBranches.realRootFinset` : the finite set of real roots of `Q x`.
* `SmoothRootBranches.nRealRoots` : the number of distinct real roots of `Q x`.
* `SmoothRootBranches.local_branch_of_simple` : implicit-function branch at a simple root.
* `SmoothRootBranches.local_root_cover` : the local finite smooth cover of the real roots.
* `SmoothRootBranches.nRealRoots_eventuallyConst` : the count is locally constant.
* `SmoothRootBranches.smooth_separable_family_root_branches` : the packaged classical result. -/

open Polynomial Filter Topology Set

namespace SmoothRootBranches

variable (Q : ℝ → Polynomial ℝ)

/-- The finite set of distinct real roots of `Q x`. -/
noncomputable def realRootFinset (x : ℝ) : Finset ℝ := (Q x).roots.toFinset

/-- The number of distinct real roots of `Q x`. -/
noncomputable def nRealRoots (x : ℝ) : ℕ := (realRootFinset Q x).card

variable {Q}

lemma mem_realRootFinset {x y : ℝ} (hQ : Q x ≠ 0) :
    y ∈ realRootFinset Q x ↔ (Q x).eval y = 0 := by
  simp only [realRootFinset, Multiset.mem_toFinset, mem_roots hQ, IsRoot.def]

/-- A separable real polynomial has only *simple* roots: the derivative is nonzero at
every root.  (Classical fact; the analytic core below only ever uses simplicity.) -/
lemma eval_derivative_ne_zero_of_separable {p : Polynomial ℝ} (hsep : p.Separable) {y : ℝ}
    (hy : p.eval y = 0) : p.derivative.eval y ≠ 0 := by
  have h := hsep.aeval_derivative_ne_zero (x := y)
    (by simpa [aeval_def, eval_map] using hy)
  simpa [aeval_def, eval_map] using h

/-
**Local implicit-function branch at a simple real root.**  If `y₀` is a *simple* real
root of `Q x₀` (root with nonzero `Y`-derivative) and the two-variable evaluation map is
smooth, then `y₀` extends to a local `C^∞` genuine-root branch `φ` of the family near `x₀`.

This is the local, reusable Dini step.
-/
lemma local_branch_of_simple
    (hsmooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (Q p.1).eval p.2))
    (x₀ y₀ : ℝ) (hroot : (Q x₀).eval y₀ = 0)
    (hsimple : (Q x₀).derivative.eval y₀ ≠ 0) :
    ∃ φ : ℝ → ℝ, φ x₀ = y₀ ∧ ContDiffAt ℝ ⊤ φ x₀ ∧
      ∀ᶠ x : ℝ in nhds x₀, (Q x).eval (φ x) = 0 := by
  let F : ℝ × ℝ → ℝ := fun p ↦ (Q p.1).eval p.2
  have hF : HasFDerivAt F (fderiv ℝ F (x₀, y₀)) (x₀, y₀) :=
    DifferentiableAt.hasFDerivAt (hsmooth.contDiffAt.differentiableAt (by norm_num))
  have hF_contDiff : ContDiffAt ℝ ⊤ F (x₀, y₀) := hsmooth.contDiffAt
  have hL : ∀ x, (fderiv ℝ F (x₀, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) x =
      (Polynomial.derivative (Q x₀)).eval y₀ * x := by
    intro x
    have hderiv : deriv (fun y ↦ (Q x₀).eval y) y₀ = (fderiv ℝ F (x₀, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1 := by
      convert HasDerivAt.deriv _ using 1
      convert HasFDerivAt.hasDerivAt (hF.comp y₀
        (HasFDerivAt.prodMk (hasFDerivAt_const _ _) (hasFDerivAt_id _))) using 1
    convert congr_arg (fun z ↦ z * x) hderiv.symm using 1
    · norm_num [Polynomial.derivative_eval]
      ring_nf!
      rw [mul_comm]
      erw [← smul_eq_mul]
      erw [← ContinuousLinearMap.map_smul]
      norm_num
    · norm_num [Polynomial.derivative_eval]
  obtain ⟨L_inv, hL_inv⟩ :
      ∃ L_inv : ℝ →L[ℝ] ℝ, ∀ x, L_inv ((Polynomial.derivative (Q x₀)).eval y₀ * x) = x :=
    ⟨ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        ((Polynomial.eval y₀ (Polynomial.derivative (Q x₀))) ⁻¹),
      fun x ↦ by simp [hsimple, mul_comm]⟩
  have h_implicit : IsContDiffImplicitAt ⊤ F (fderiv ℝ F (x₀, y₀)) (x₀, y₀) := by
    constructor
    · exact hF
    · exact hF_contDiff
    · constructor
      · intro x y hxy
        have := hL_inv x
        have := hL_inv y
        aesop
      · intro x
        use x / (Polynomial.eval y₀ (Polynomial.derivative (Q x₀)))
        simp [hL, mul_div_cancel₀ _ hsimple]
    · decide
  refine ⟨h_implicit.implicitFunction, ?_, ?_, ?_⟩ <;> norm_num [h_implicit]
  · convert h_implicit.eventually_implicitFunction_apply_eq.self_of_nhds using 1
    aesop
  · exact h_implicit.contDiffAt_implicitFunction
  · have := h_implicit.apply_implicitFunction
    aesop

/-
**Local uniqueness of a simple real root.**  Near a simple real root `y₀` of `Q x₀`,
for parameters `x` near `x₀` the root of `Q x` lying near `y₀` is unique.  This is the
uniqueness clause of the implicit function theorem, and is what lets the (a priori several)
local branches be counted without collision.
-/
lemma local_unique_of_simple
    (hsmooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (Q p.1).eval p.2))
    (x₀ y₀ : ℝ) (hsimple : (Q x₀).derivative.eval y₀ ≠ 0) :
    ∃ (u v : Set ℝ), u ∈ nhds x₀ ∧ v ∈ nhds y₀ ∧
      ∀ x ∈ u, ∀ y₁ ∈ v, ∀ y₂ ∈ v, (Q x).eval y₁ = 0 → (Q x).eval y₂ = 0 → y₁ = y₂ := by
  -- By continuity of the partial derivative away from zero, there exists a δ > 0 such that for (x, y) with |x - x₀| < δ, |y - y₀| < δ, we have (Q x).derivative.eval y ≠ 0.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x y, abs (x - x₀) < δ → abs (y - y₀) < δ → (Q x).derivative.eval y ≠ 0 := by
    have h_deriv_cont : ContDiff ℝ ⊤ (fun p : ℝ × ℝ ↦ deriv (fun y ↦ (Q p.1).eval y) p.2) := by
      apply_rules [ContDiff.fderiv_apply]
      any_goals exact le_top
      · exact hsmooth.comp (contDiff_fst.fst.prodMk contDiff_snd)
      · exact contDiff_snd
      · exact contDiff_const
    have h_cont_diff : ContDiff ℝ ⊤ (fun p : ℝ × ℝ ↦ (Q p.1).derivative.eval p.2) := by
      convert h_deriv_cont using 1
      ext
      simp [Polynomial.derivative_eval]
    have h_cont : ContinuousAt (fun p : ℝ × ℝ ↦ (Q p.1).derivative.eval p.2) (x₀, y₀) :=
      h_cont_diff.continuous.continuousAt
    have := Metric.continuousAt_iff.mp h_cont
    obtain ⟨δ, hδ⟩ := this (|eval y₀ (derivative (Q x₀))|) (abs_pos.mpr hsimple)
    refine ⟨δ, hδ.1, fun x y hx hy ↦ ?_⟩
    cases abs_cases (eval y₀ (derivative (Q x₀))) <;>
      linarith [abs_lt.mp (hδ.2 (show dist (x, y) (x₀, y₀) < δ from max_lt hx hy))]
  refine ⟨Metric.ball x₀ δ, Metric.ball y₀ δ, Metric.ball_mem_nhds _ hδ_pos, Metric.ball_mem_nhds _ hδ_pos, ?_⟩
  intro x hx y₁ hy₁ y₂ hy₂ h₁ h₂
  contrapose! hδ
  -- By Rolle's theorem, since `Q(x, y₁) = 0` and `Q(x, y₂) = 0`, there exists some `c` between `y₁` and `y₂` such that `Q'(x, c) = 0`.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo (min y₁ y₂) (max y₁ y₂), deriv (fun y ↦ (Q x).eval y) c = 0 := by
    apply_mod_cast exists_deriv_eq_zero
    · grind
    · exact Continuous.continuousOn (Polynomial.continuous _)
    · cases le_total y₁ y₂ <;> aesop
  simp_all [Polynomial.derivative_eval]
  refine ⟨x, hx, c, abs_lt.mpr ⟨?_, ?_⟩, hc.2⟩ <;>
    cases hc.1.1 <;> cases hc.1.2 <;> linarith [abs_lt.mp hy₁, abs_lt.mp hy₂]

/-
Coefficients of a smooth family of polynomials are continuous functions of the
parameter.  (The `k`-th coefficient is `1/k!` times the `k`-th `Y`-derivative of the
evaluation at `Y = 0`, which is continuous since the evaluation is `C^∞`.)
-/
lemma coeff_continuous
    (hsmooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (Q p.1).eval p.2)) (k : ℕ) :
    Continuous (fun x ↦ (Q x).coeff k) := by
  have h_two_var : ∀ p : ℕ,
      ContDiff ℝ ⊤ (fun p' : ℝ × ℝ ↦ Polynomial.eval p'.2 (Polynomial.derivative^[p] (Q p'.1))) := by
    intro p
    induction' p with p ih <;> simp_all [Function.iterate_succ_apply']
    have h_eval_cont : ContDiff ℝ ⊤
        (fun p' : ℝ × ℝ ↦ deriv (fun y ↦ Polynomial.eval y (Polynomial.derivative^[p] (Q p'.1))) p'.2) := by
      apply_rules [ContDiff.fderiv_apply, ih]
      · convert ih.comp (contDiff_fst.fst.prodMk contDiff_snd) using 1
      · exact contDiff_snd
      · fun_prop
      · norm_num at *
    convert h_eval_cont using 1
    ext
    simp [Polynomial.derivative_eval]
  have h_coeff_cont : ∀ p : ℕ,
      ContDiff ℝ ⊤ (fun x ↦ Polynomial.eval 0 (Polynomial.derivative^[p] (Q x))) :=
    fun p ↦ (h_two_var p).comp (contDiff_id.prodMk contDiff_const)
  convert (h_coeff_cont k).continuous.div_const k.factorial using 1
  ext x
  rw [eq_div_iff (by positivity)]
  simp [Polynomial.eval, Polynomial.coeff_iterate_derivative]
  rw [mul_comm, Nat.descFactorial_self]

/-
**Uniform local bound on the real roots (Cauchy's bound).**  Near any parameter `x₀`,
all real roots of `Q x` stay in a fixed bounded interval.  This uses that `Q x` is monic of
fixed degree with coefficients depending continuously on `x` (`coeff_continuous`), so
Cauchy's root bound is locally uniform.
-/
lemma exists_uniform_root_bound (d : ℕ) (hd : 1 ≤ d)
    (hmonic : ∀ x, (Q x).Monic) (hdeg : ∀ x, (Q x).natDegree = d)
    (hsmooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (Q p.1).eval p.2))
    (x₀ : ℝ) :
    ∃ (M : ℝ) (u : Set ℝ), u ∈ nhds x₀ ∧
      ∀ x ∈ u, ∀ y : ℝ, (Q x).eval y = 0 → |y| ≤ M := by
  -- Let B(x) := 1 + ∑_{i=0}^{d-1} |(Q x).coeff i|. Each x ↦ |(Q x).coeff i| is continuous (coeff_continuous composed with abs), so B is continuous.
  set B : ℝ → ℝ := fun x ↦ 1 + ∑ i ∈ Finset.range d, abs ((Q x).coeff i)
  -- By continuity of `B` at `x₀`, pick `M := B x₀ + 1` and a neighborhood `u` of `x₀` on which `B x < M` (i.e. `B x ≤ M`).
  obtain ⟨M, u, hu⟩ : ∃ M u, u ∈ nhds x₀ ∧ ∀ x ∈ u, B x ≤ M := by
    have hB_cont : Continuous B := by
      refine continuous_const.add (continuous_finset_sum _ fun i hi ↦ ?_)
      exact Continuous.abs (coeff_continuous hsmooth i)
    exact ⟨B x₀ + 1, { x | B x < B x₀ + 1 },
      hB_cont.continuousAt.eventually (gt_mem_nhds <| lt_add_one _), fun x hx ↦ le_of_lt hx⟩
  refine ⟨M, u, hu.1, fun x hx y hy ↦ ?_⟩
  by_cases hy_abs : |y| > 1
  · -- The bound `|y|^d ≤ ∑ i ∈ Finset.range d, |(Q x).coeff i| * |y|^i` holds.
    have h_bound : |y|^d ≤ ∑ i ∈ Finset.range d, |(Q x).coeff i| * |y|^i := by
      have h_abs_bound : |y|^d ≤ |∑ i ∈ Finset.range d, (Q x).coeff i * y^i| := by
        rw [Polynomial.eval_eq_sum_range] at hy
        simp_all [Finset.sum_range_succ]
        simp_all [add_eq_zero_iff_eq_neg, Polynomial.Monic.def, Polynomial.leadingCoeff]
      exact h_abs_bound.trans (le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum fun i hi ↦ by rw [abs_mul, abs_pow]))
    -- Since `|y| > 1`, we can factor out `|y|^(d-1)` from the right-hand side of the inequality.
    have h_factor : |y|^d ≤ (∑ i ∈ Finset.range d, |(Q x).coeff i|) * |y|^(d-1) := by
      refine h_bound.trans ?_
      rw [Finset.sum_mul _ _ _]
      exact Finset.sum_le_sum fun i hi ↦
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hy_abs.le (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))) (abs_nonneg _)
    rcases d <;> simp_all [pow_succ']
    nlinarith [hu.2 x hx, pow_pos (zero_lt_one.trans hy_abs) ‹_›,
      show ∑ i ∈ Finset.range (‹_› + 1), |(Q x).coeff i| ≤ M - 1 by linarith [hu.2 x hx]]
  · linarith [hu.2 x hx,
      show 0 ≤ ∑ i ∈ Finset.range d, |(Q x).coeff i| from Finset.sum_nonneg fun _ _ ↦ abs_nonneg _]

/-
**Upper semicontinuity of the real root set.**  Every real root of `Q x`, for `x` near
`x₀`, lies within `ε` of some real root of `Q x₀`.  This is the compactness core of the
local theory: the roots of `Q x` cannot escape to infinity (`exists_uniform_root_bound`)
nor appear away from the roots of `Q x₀` (on the compact complement of the `ε`-balls,
`Q x₀` is nonzero, hence so is `Q x` for `x` near `x₀`, by the tube lemma).
-/
lemma roots_near_roots (d : ℕ) (hd : 1 ≤ d)
    (hmonic : ∀ x, (Q x).Monic) (hdeg : ∀ x, (Q x).natDegree = d)
    (hsmooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (Q p.1).eval p.2))
    (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ nhds x₀, ∀ x ∈ u, ∀ y : ℝ, (Q x).eval y = 0 →
      ∃ y₀ : ℝ, (Q x₀).eval y₀ = 0 ∧ |y - y₀| < ε := by
  -- Let M and u₁ be from `exists_uniform_root_bound d hd hmonic hdeg hsmooth x₀`.
  obtain ⟨M, u₁, hu₁⟩ : ∃ M u₁, u₁ ∈ nhds x₀ ∧ ∀ x ∈ u₁, ∀ y : ℝ, eval y (Q x) = 0 → abs y ≤ M :=
    exists_uniform_root_bound d hd hmonic hdeg hsmooth x₀
  -- Define the compact set K := {t : ℝ | t ∈ Set.Icc (-M) M ∧ ∀ y₀ ∈ realRootFinset Q x₀, ε ≤ |t - y₀|}.
  set K := {t : ℝ | t ∈ Set.Icc (-M) M ∧ ∀ y₀ ∈ realRootFinset Q x₀, ε ≤ |t - y₀|}
  have hK_compact : IsCompact K := by
    apply (CompactIccSpace.isCompact_Icc (a := -M) (b := M)).of_isClosed_subset
    · refine isClosed_Icc.inter (isClosed_of_closure_subset fun x hx ↦ ?_)
      rw [mem_closure_iff_seq_limit] at hx
      exact fun y₀ hy₀ ↦
        le_of_tendsto_of_tendsto' tendsto_const_nhds (Filter.Tendsto.abs (hx.choose_spec.2.sub_const y₀))
          fun n ↦ hx.choose_spec.1 n y₀ hy₀
    · exact fun x hx ↦ hx.1
  -- Apply the generalized tube lemma to get open `u₀, v` with `x₀ ∈ u₀`, `K ⊆ v`, and `u₀ ×ˢ v ⊆ O`.
  obtain ⟨u₀, v, hu₀, hv, huv⟩ :
      ∃ u₀ v : Set ℝ, IsOpen u₀ ∧ IsOpen v ∧ x₀ ∈ u₀ ∧ K ⊆ v ∧ u₀ ×ˢ v ⊆ {p : ℝ × ℝ | eval p.2 (Q p.1) ≠ 0} := by
    have h_generalized_tube : {x₀} ×ˢ K ⊆ {p : ℝ × ℝ | eval p.2 (Q p.1) ≠ 0} := by
      simp +zetaDelta at *
      simp +contextual [Set.subset_def, mem_realRootFinset (hmonic x₀).ne_zero]
      intro a b ha hb₁ hb₂ hb₃ hb₄
      exact not_lt_of_ge (hb₃ b hb₄) (by simpa [hb₄] using hε)
    have := @generalized_tube_lemma
    specialize this (isCompact_singleton : IsCompact { x₀ }) hK_compact
      (show IsOpen { p : ℝ × ℝ | eval p.2 (Q p.1) ≠ 0 } from
        isOpen_compl_iff.mpr <| isClosed_eq (hsmooth.continuous) continuous_const) h_generalized_tube
    simp_all [Set.subset_def]
  refine ⟨u₀ ∩ u₁, Filter.inter_mem (hu₀.mem_nhds huv.1) hu₁.1, fun x hx y hy ↦ ?_⟩
  contrapose! huv
  simp_all [Set.not_subset]
  exact fun _ _ ↦ ⟨x, y, ⟨hx.1, ‹K ⊆ v›
    ⟨⟨by linarith [abs_le.mp (hu₁.2 x hx.2 y hy)], by linarith [abs_le.mp (hu₁.2 x hx.2 y hy)]⟩,
      fun y₀ hy₀ ↦ huv y₀ <| by simpa using mem_realRootFinset (hmonic x₀).ne_zero |>.1 hy₀⟩⟩, hy⟩

/-
**Local finite smooth cover of the real roots.**  On a separable tail, near any
parameter `x₀ ≥ T₀` there is a neighborhood (within `Ici T₀`) on which the real roots of
`Q x` are *exactly* the values of finitely many injective smooth branches.  This is the
heart of the local theory: it packages the implicit-function branches (existence +
uniqueness) with the Cauchy/compactness argument that no extra roots appear.  From it the
count is immediately locally constant.
-/
set_option maxHeartbeats 1000000 in
lemma local_root_cover
    (T₀ : ℝ) (d : ℕ)
    (hmonic : ∀ x, (Q x).Monic) (hdeg : ∀ x, (Q x).natDegree = d)
    (hsmooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (Q p.1).eval p.2))
    (hsep : ∀ x, T₀ ≤ x → (Q x).Separable)
    {x₀ : ℝ} (hx₀ : T₀ ≤ x₀) :
    ∃ (m : ℕ) (φ : Fin m → ℝ → ℝ) (s : Set ℝ),
      s ∈ nhdsWithin x₀ (Set.Ici T₀) ∧ x₀ ∈ s ∧ Convex ℝ s ∧
      (∀ i, ContDiffOn ℝ ⊤ (φ i) s) ∧
      (∀ i, ∀ x ∈ s, (Q x).eval (φ i x) = 0) ∧
      (∀ x ∈ s, Function.Injective (fun i => φ i x)) ∧
      (∀ x ∈ s, ∀ y : ℝ, (Q x).eval y = 0 → ∃ i, φ i x = y) := by
  -- Set `S := realRootFinset Q x₀`, the finite set of real roots of `Q x₀`.
  set S := realRootFinset Q x₀ with hS_def
  obtain ⟨y, hy⟩ : ∃ y : Fin (S.card) → ℝ, StrictMono y ∧ S = Finset.image y Finset.univ := by
    use fun i ↦ S.orderEmbOfFin rfl i
    simp [StrictMono]
  have hroots : ∀ i, (Q x₀).eval (y i) = 0 := by
    intro i
    have hmem : y i ∈ S := hy.2.symm ▸ Finset.mem_image_of_mem y (Finset.mem_univ i)
    rw [hS_def] at hmem
    exact (mem_realRootFinset (hmonic x₀).ne_zero).1 hmem
  -- For each `i`, apply `local_branch_of_simple` to get `φ i : ℝ → ℝ` with `φ i x₀ = y i`, `ContDiffAt ℝ ⊤ (φ i) x₀`, and `(Q x).eval (φ i x) = 0` for `x` near `x₀`.
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin (S.card) → ℝ → ℝ,
      (∀ i, φ i x₀ = y i) ∧ (∀ i, ContDiffAt ℝ ⊤ (φ i) x₀) ∧ (∀ i, ∀ᶠ x in nhds x₀, (Q x).eval (φ i x) = 0) := by
    have h_local_branch : ∀ i, ∃ φ : ℝ → ℝ,
        φ x₀ = y i ∧ ContDiffAt ℝ ⊤ φ x₀ ∧ ∀ᶠ x in nhds x₀, (Q x).eval (φ x) = 0 := by
      intro i
      apply local_branch_of_simple hsmooth x₀ (y i) (hroots i)
        (eval_derivative_ne_zero_of_separable (hsep x₀ hx₀) (hroots i))
    choose φ h1 h2 h3 using h_local_branch
    exact ⟨φ, h1, h2, h3⟩
  -- Apply `local_unique_of_simple` to get `u i ∈ 𝓝 x₀`, `v i ∈ 𝓝 (y i)`.
  obtain ⟨u, v, hu, hv, huv⟩ : ∃ u : Fin (S.card) → Set ℝ, ∃ v : Fin (S.card) → Set ℝ,
      (∀ i, u i ∈ nhds x₀) ∧ (∀ i, v i ∈ nhds (y i)) ∧
        (∀ i, ∀ x ∈ u i, ∀ y₁ ∈ v i, ∀ y₂ ∈ v i, (Q x).eval y₁ = 0 → (Q x).eval y₂ = 0 → y₁ = y₂) := by
    have h_unique : ∀ i, ∃ u v : Set ℝ, u ∈ nhds x₀ ∧ v ∈ nhds (y i) ∧
        ∀ x ∈ u, ∀ y₁ ∈ v, ∀ y₂ ∈ v, (Q x).eval y₁ = 0 → (Q x).eval y₂ = 0 → y₁ = y₂ := by
      intro i
      apply local_unique_of_simple hsmooth x₀ (y i)
        (eval_derivative_ne_zero_of_separable (hsep x₀ hx₀) (hroots i))
    choose u v hu hv huv using h_unique
    exact ⟨u, v, hu, hv, huv⟩
  -- Choose `ε > 0` small enough that: (i) for `i ≠ i'`, `2 * ε ≤ |y i - y i'|` (possible since `y` is injective and there are finitely many pairs, so the pairwise distances have a positive minimum; if `m ≤ 1` this is vacuous); and (ii) for every `i`, `Metric.ball (y i) ε ⊆ v i` (possible since each `v i ∈ 𝓝 (y i)`).
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, (∀ i j, i ≠ j → 2 * ε ≤ |y i - y j|) ∧ (∀ i, Metric.ball (y i) ε ⊆ v i) := by
    -- Choose `ε > 0` small enough that for `i ≠ i'`, `2 * ε ≤ |y i - y i'|`.
    obtain ⟨ε₁, hε₁_pos, hε₁⟩ : ∃ ε₁ > 0, ∀ i j, i ≠ j → 2 * ε₁ ≤ |y i - y j| := by
      by_cases h_empty : Finset.card (Finset.image
          (fun p : Fin S.card × Fin S.card ↦ |y p.1 - y p.2|)
          (Finset.filter (fun p ↦ p.1 ≠ p.2) (Finset.univ : Finset (Fin S.card × Fin S.card)))) = 0
      · simp at *
        exact ⟨1, zero_lt_one, fun i j hij ↦ False.elim <| hij <| h_empty i j⟩
      · obtain ⟨ε₁, hε₁⟩ :
            ∃ ε₁ ∈ Finset.image (fun p : Fin S.card × Fin S.card ↦ |y p.1 - y p.2|)
                (Finset.filter (fun p ↦ p.1 ≠ p.2) (Finset.univ : Finset (Fin S.card × Fin S.card))),
              ∀ ε ∈ Finset.image (fun p : Fin S.card × Fin S.card ↦ |y p.1 - y p.2|)
                (Finset.filter (fun p ↦ p.1 ≠ p.2) (Finset.univ : Finset (Fin S.card × Fin S.card))), ε₁ ≤ ε := by
          exact ⟨Finset.min' _ <| Finset.card_pos.mp <| Nat.pos_of_ne_zero h_empty,
            Finset.min'_mem _ _, fun ε hε ↦ Finset.min'_le _ _ hε⟩
        simp at *
        refine ⟨ε₁ / 2, half_pos ?_, fun i j hij ↦ by linarith [hε₁.2 _ i j hij rfl]⟩
        obtain ⟨a, b, hab, rfl⟩ := hε₁.1
        exact abs_pos.mpr (sub_ne_zero.mpr <| hy.1.injective.ne hab)
    -- Choose `ε > 0` small enough that for every `i`, `Metric.ball (y i) ε ⊆ v i`.
    obtain ⟨ε₂, hε₂_pos, hε₂⟩ : ∃ ε₂ > 0, ∀ i, Metric.ball (y i) ε₂ ⊆ v i := by
      choose ε₂ hε₂ using fun i ↦ Metric.mem_nhds_iff.mp (hv i)
      by_cases h : Finset.Nonempty (Finset.univ : Finset (Fin S.card)) <;> simp_all [Finset.Nonempty]
      · refine ⟨Finset.min' (Finset.univ.image ε₂) ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ h.some)⟩,
          ?_, ?_⟩
        · have := Finset.min'_mem (Finset.univ.image ε₂) ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ h.some)⟩
          aesop
        · exact fun i ↦
            Set.Subset.trans
              (Metric.ball_subset_ball (Finset.min'_le _ _ <| Finset.mem_image_of_mem _ <| Finset.mem_univ i))
              (hε₂ i |>.2)
      · exact ⟨1, zero_lt_one⟩
    exact ⟨Min.min ε₁ ε₂, lt_min hε₁_pos hε₂_pos,
      fun i j hij ↦ le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le_two) (hε₁ i j hij),
      fun i ↦ Set.Subset.trans (Metric.ball_subset_ball (min_le_right _ _)) (hε₂ i)⟩
  -- Apply `roots_near_roots` to get `uε ∈ 𝓝 x₀`.
  obtain ⟨uε, huε⟩ :
      ∃ uε ∈ nhds x₀, ∀ x ∈ uε, ∀ y : ℝ, (Q x).eval y = 0 → ∃ y₀ : ℝ, (Q x₀).eval y₀ = 0 ∧ |y - y₀| < ε := by
    by_cases hd : 1 ≤ d <;> simp_all [realRootFinset]
    · obtain ⟨u, hu₁, hu₂⟩ := roots_near_roots (Q := Q) d hd hmonic hdeg hsmooth x₀ hε_pos
      exact ⟨u, hu₁, fun x hx y hy ↦ by simpa using hu₂ x hx y hy⟩
    · exact ⟨Set.univ, Filter.univ_mem⟩
  -- Now pick `δ > 0` (a ball `Metric.ball x₀ δ`) inside the intersection of the following neighborhoods of `x₀`: each `u i`; `uε`; a ball on which each `φ i` is `ContDiffOn ℝ ⊤` (from `ContDiffAt`); a ball on which each `(Q x).eval (φ i x) = 0` (from the eventual root property); and a ball on which each `φ i x ∈ Metric.ball (y i) ε` (from continuity of `φ i` at `x₀`, since `φ i x₀ = y i` and the ball is a neighborhood of `y i`).
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, Metric.ball x₀ δ ⊆ uε ∧ (∀ i, Metric.ball x₀ δ ⊆ u i) ∧
      (∀ i, ∀ x ∈ Metric.ball x₀ δ, (Q x).eval (φ i x) = 0) ∧
      (∀ i, ∀ x ∈ Metric.ball x₀ δ, φ i x ∈ Metric.ball (y i) ε) ∧
      (∀ i, ContDiffOn ℝ ⊤ (φ i) (Metric.ball x₀ δ)) := by
    have hδ_all : ∀ i, ∃ δi > 0, Metric.ball x₀ δi ⊆ u i ∧ (∀ x ∈ Metric.ball x₀ δi, (Q x).eval (φ i x) = 0) ∧
        (∀ x ∈ Metric.ball x₀ δi, φ i x ∈ Metric.ball (y i) ε) ∧ ContDiffOn ℝ ⊤ (φ i) (Metric.ball x₀ δi) := by
      intro i
      obtain ⟨δi, hδi_pos, hδi⟩ : ∃ δi > 0, Metric.ball x₀ δi ⊆ u i ∧
          (∀ x ∈ Metric.ball x₀ δi, (Q x).eval (φ i x) = 0) ∧
          (∀ x ∈ Metric.ball x₀ δi, φ i x ∈ Metric.ball (y i) ε) := by
        have hev : ∀ᶠ x in nhds x₀, (Q x).eval (φ i x) = 0 ∧ φ i x ∈ Metric.ball (y i) ε :=
          Filter.Eventually.and (hφ.2.2 i)
            (by simpa [hφ.1 i] using
                (hφ.2.1 i).continuousAt.eventually (Metric.ball_mem_nhds _ hε_pos))
        rcases Metric.mem_nhds_iff.mp (hu i) with ⟨δ₁, hδ₁_pos, hδ₁⟩
        rcases Metric.mem_nhds_iff.mp hev with ⟨δ₂, hδ₂_pos, hδ₂⟩
        exact ⟨Min.min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos,
          fun x hx ↦ hδ₁ <| Metric.mem_ball.mpr <| lt_of_lt_of_le hx <| min_le_left _ _,
          fun x hx ↦ hδ₂ (Metric.mem_ball.mpr <| lt_of_lt_of_le hx <| min_le_right _ _) |>.1,
          fun x hx ↦ hδ₂ (Metric.mem_ball.mpr <| lt_of_lt_of_le hx <| min_le_right _ _) |>.2⟩
      obtain ⟨δi', hδi'_pos, hδi'⟩ : ∃ δi' > 0, ContDiffOn ℝ ⊤ (φ i) (Metric.ball x₀ δi') := by
        have := hφ.2.1 i
        have := this.eventually (by norm_num)
        simp_all [Metric.eventually_nhds_iff]
        exact ⟨this.choose, this.choose_spec.1, fun x hx ↦ (this.choose_spec.2 hx).contDiffWithinAt⟩
      exact ⟨Min.min δi δi', lt_min hδi_pos hδi'_pos,
        Set.Subset.trans (Metric.ball_subset_ball (min_le_left _ _)) hδi.1,
        fun x hx ↦ hδi.2.1 x (Metric.ball_subset_ball (min_le_left _ _) hx),
        fun x hx ↦ hδi.2.2 x (Metric.ball_subset_ball (min_le_left _ _) hx),
        hδi'.mono (Metric.ball_subset_ball (min_le_right _ _))⟩
    choose δ hδ_pos hδ using hδ_all
    obtain ⟨δ', hδ'_pos, hδ'⟩ : ∃ δ' > 0, Metric.ball x₀ δ' ⊆ uε ∧ ∀ i, δ' ≤ δ i := by
      rcases Metric.mem_nhds_iff.mp huε.1 with ⟨δ', hδ'_pos, hδ'⟩
      by_cases hS_card : S.card = 0
      · exact ⟨δ', hδ'_pos, hδ', fun i ↦ False.elim <| Fin.elim0 <| Fin.castLE (by linarith) i⟩
      · have hmem : (Finset.univ.image δ).Nonempty :=
          ⟨_, Finset.mem_image_of_mem δ (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hS_card⟩)⟩
        refine ⟨Min.min δ' (Finset.min' (Finset.univ.image δ) hmem), ?_,
          Set.Subset.trans (Metric.ball_subset_ball (min_le_left _ _)) hδ',
          fun i ↦
            min_le_right _ _ |> le_trans <| Finset.min'_le _ _ <| Finset.mem_image_of_mem δ <| Finset.mem_univ i⟩
        refine lt_min hδ'_pos ?_
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem (Finset.univ.image δ) hmem)
        linarith [hδ_pos i]
    exact ⟨δ', hδ'_pos, hδ'.1,
      fun i ↦ Set.Subset.trans (Metric.ball_subset_ball (hδ'.2 i)) (hδ i |>.1),
      fun i x hx ↦ hδ i |>.2.1 x (Metric.ball_subset_ball (hδ'.2 i) hx),
      fun i x hx ↦ hδ i |>.2.2.1 x (Metric.ball_subset_ball (hδ'.2 i) hx),
      fun i ↦ ContDiffOn.mono (hδ i |>.2.2.2) (Metric.ball_subset_ball (hδ'.2 i))⟩
  refine ⟨S.card, φ, Set.Ici T₀ ∩ Metric.ball x₀ δ, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [hδ_pos]
  · exact ⟨self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hδ_pos)⟩
  · linarith
  · exact (convex_Ici _).inter (convex_ball _ _)
  · exact fun i ↦ (hδ.2.2.2.2 i).mono Set.inter_subset_right
  · refine ⟨?_, ?_, ?_⟩
    · exact fun i x hx₁ hx₂ ↦ hδ.2.2.1 i x hx₂
    · intro x hx₁ hx₂ i j hij
      have := hε.1 i j
      contrapose! this
      simp_all [dist_eq_norm]
      refine abs_lt.mpr ⟨?_, ?_⟩ <;>
        linarith [abs_lt.mp (hδ.2.2.2.1 i x hx₂), abs_lt.mp (hδ.2.2.2.1 j x hx₂)]
    · intro x hx₁ hx₂ y hy
      have := huε.2 x (hδ.1 hx₂) y hy
      obtain ⟨y₀, hy₀₁, hy₀₂⟩ := this
      simp_all [Finset.ext_iff]
      -- Since `y₀` is a root of `Q x₀`, there exists some `i` such that `y₀ = y i`.
      obtain ⟨i, hi⟩ : ∃ i : Fin S.card, y₀ = ‹Fin S.card → ℝ› i := by
        exact hS_def y₀ |>.2
          (Multiset.mem_toFinset.mpr <| Polynomial.mem_roots (hmonic x₀).ne_zero |>.2 hy₀₁) |>
          fun ⟨i, hi⟩ ↦ ⟨i, hi.symm⟩
      specialize huv i x (hδ.2.1 i hx₂) y (hε.2 i <| by simpa [hi] using hy₀₂)
        (φ i x) (hε.2 i (hδ.2.2.2.1 i x hx₂)) hy (hδ.2.2.1 i x hx₂)
      aesop

/-
**The number of distinct real roots is locally constant on the separable tail.**
Immediate from `local_root_cover`: on the local neighborhood the roots are the `m` distinct
values of the injective branches, so `nRealRoots x = m` there.
-/
lemma nRealRoots_eventuallyConst
    (T₀ : ℝ) (d : ℕ)
    (hmonic : ∀ x, (Q x).Monic) (hdeg : ∀ x, (Q x).natDegree = d)
    (hsmooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (Q p.1).eval p.2))
    (hsep : ∀ x, T₀ ≤ x → (Q x).Separable)
    {x₀ : ℝ} (hx₀ : T₀ ≤ x₀) :
    ∀ᶠ x in nhdsWithin x₀ (Set.Ici T₀), nRealRoots Q x = nRealRoots Q x₀ := by
  obtain ⟨m, φ, s, hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, hs₇⟩ := local_root_cover T₀ d hmonic hdeg hsmooth hsep hx₀
  -- For every `x ∈ s`, `realRootFinset Q x = Finset.image (fun i ↦ φ i x) Finset.univ`.
  have h_realRootFinset_eq : ∀ x ∈ s, realRootFinset Q x = Finset.image (fun i ↦ φ i x) Finset.univ := by
    intro x hx
    ext y
    simp [realRootFinset]
    exact ⟨fun h ↦ hs₇ x hx y h.2, fun ⟨i, hi⟩ ↦ ⟨(hmonic x).ne_zero, by simpa [hi] using hs₅ i x hx⟩⟩
  filter_upwards [hs₁] with x hx
  simp_all [nRealRoots]
  rw [Finset.card_image_of_injective _ (hs₆ x hx), Finset.card_image_of_injective _ (hs₆ x₀ hs₂)]

/-
**The number of distinct real roots is constant on the separable tail.**  Upgrades the
local constancy of `nRealRoots_eventuallyConst` to global constancy, using connectedness of
the half-line `Ici T₀`.
-/
lemma nRealRoots_const
    (T₀ : ℝ) (d : ℕ)
    (hmonic : ∀ x, (Q x).Monic) (hdeg : ∀ x, (Q x).natDegree = d)
    (hsmooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (Q p.1).eval p.2))
    (hsep : ∀ x, T₀ ≤ x → (Q x).Separable) :
    ∀ x, T₀ ≤ x → nRealRoots Q x = nRealRoots Q T₀ := by
  -- To show `ContinuousOn (nRealRoots Q) (Set.Ici T₀)` (into the discrete space ℕ), we can use the fact that if a function is eventually constant on a neighborhood of every point in a set, then it is continuous on that set.
  have h_cont : ContinuousOn (fun x ↦ nRealRoots Q x) (Set.Ici T₀) := by
    intro x hx
    exact tendsto_nhds_of_eventually_eq (nRealRoots_eventuallyConst T₀ d hmonic hdeg hsmooth hsep hx)
  intro x hx
  have h_const : IsPreconnected (Set.Ici T₀) := isPreconnected_Ici
  exact (h_const.image _ h_cont).subsingleton (Set.mem_image_of_mem _ hx)
    (Set.mem_image_of_mem _ Set.self_mem_Ici)

set_option maxHeartbeats 1000000 in
/-- **Classical construction of the smooth real root branches.**

For a `C^∞` family `Q x` of monic real polynomials of fixed degree `d ≥ 1` that is
*separable* on a half-line `[T₀, ∞)`, the real roots of `Q x` are given by finitely many
`C^∞` functions `g j` on `[T₀, ∞)`, each a genuine real root, whose values at every
`x ≥ T₀` exhaust all real roots of `Q x`.

This is the honest, elementary (pre-1900) Weierstrass-style statement: on the separable
tail each real root is simple, hence continues smoothly by the implicit function theorem
(`local_branch_of_simple`), the local branches never collide (`local_unique_of_simple`),
the number of real roots is constant (`nRealRoots_const`), and the ordered real roots (the
order statistics) are the finitely many global smooth branches. -/
theorem smooth_separable_family_root_branches
    (Q : ℝ → Polynomial ℝ) (T₀ : ℝ) (d : ℕ) (_hd : 1 ≤ d)
    (hmonic : ∀ x, (Q x).Monic) (hdeg : ∀ x, (Q x).natDegree = d)
    (hsmooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (Q p.1).eval p.2))
    (hsep : ∀ x, T₀ ≤ x → (Q x).Separable) :
    ∃ (n : ℕ) (g : Fin n → ℝ → ℝ),
      (∀ j, ContDiffOn ℝ ⊤ (g j) (Set.Ici T₀)) ∧
      (∀ j, ∀ x, T₀ ≤ x → (Q x).eval (g j x) = 0) ∧
      (∀ x, T₀ ≤ x → ∀ y : ℝ, (Q x).eval y = 0 → ∃ j, g j x = y) ∧
      (∀ x, T₀ ≤ x → Function.Injective (fun j ↦ g j x)) := by
  -- Let `n := nRealRoots Q T₀`. For every `x ≥ T₀`, `(realRootFinset Q x).card = n` by `nRealRoots_const`.
  set n := nRealRoots Q T₀ with hn
  have h_card : ∀ x, T₀ ≤ x → (realRootFinset Q x).card = n :=
    nRealRoots_const T₀ d hmonic hdeg hsmooth hsep
  -- Define, for `j : Fin n`, `g j x := if h : (realRootFinset Q x).card = n then (realRootFinset Q x).orderEmbOfFin h j else 0`.
  let g := fun j : Fin n ↦ fun x ↦
    if h : (realRootFinset Q x).card = n then (realRootFinset Q x).orderEmbOfFin h j else 0
  refine ⟨n, g, ?_, ?_, ?_, ?_⟩
  · intro j x₀ hx₀
    obtain ⟨m, φ, s, hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, hs₇⟩ := local_root_cover T₀ d hmonic hdeg hsmooth hsep hx₀
    -- Since `m = n`, we can rewrite the goal in terms of `n`.
    have hm_eq_n : m = n := by
      have hcard_s : ∀ x ∈ s, (realRootFinset Q x).card = m := by
        intro x hx
        have h_card_eq : (realRootFinset Q x).card = Finset.card (Finset.image (fun i ↦ φ i x) Finset.univ) := by
          congr with y
          simp [mem_realRootFinset (hmonic x).ne_zero]
          exact ⟨fun hy ↦ hs₇ x hx y hy, fun ⟨i, hi⟩ ↦ hi ▸ hs₅ i x hx⟩
        rw [h_card_eq, Finset.card_image_of_injective _ (hs₆ x hx), Finset.card_fin]
      rw [← hcard_s x₀ hs₂, h_card x₀ hx₀]
    -- Choose a permutation `σ : Equiv.Perm (Fin n)` sorting the values at `x₀`.
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), StrictMono (fun j ↦ φ (Fin.cast hm_eq_n.symm (σ j)) x₀) := by
      have h_order : ∃ σ : Fin n → Fin n, StrictMono (fun j ↦ φ (Fin.cast hm_eq_n.symm (σ j)) x₀) := by
        have h_distinct : ∀ i j : Fin n, i ≠ j → φ (Fin.cast hm_eq_n.symm i) x₀ ≠ φ (Fin.cast hm_eq_n.symm j) x₀ :=
          fun i j hij ↦ fun h ↦ hij <| Fin.ext <| by
            have := hs₆ x₀ hs₂
            have := @this (Fin.cast hm_eq_n.symm i) (Fin.cast hm_eq_n.symm j)
            aesop
        have h_sorted : ∃ σ : Fin n → ℝ, StrictMono σ ∧
            ∀ i, σ i ∈ Finset.image (fun i : Fin n ↦ φ (Fin.cast hm_eq_n.symm i) x₀) Finset.univ := by
          have h_card_n :
              Finset.card (Finset.image (fun i : Fin n ↦ φ (Fin.cast hm_eq_n.symm i) x₀) Finset.univ) = n := by
            rw [Finset.card_image_of_injective _ fun i j hij ↦ not_imp_not.mp (h_distinct i j) hij,
              Finset.card_fin]
          exact ⟨fun i ↦ Finset.orderEmbOfFin _ (by aesop) i, by aesop_cat,
            fun i ↦ Finset.orderEmbOfFin_mem _ (by aesop) _⟩
        obtain ⟨σ, hσ₁, hσ₂⟩ := h_sorted
        choose f hf using fun i ↦ Finset.mem_image.mp (hσ₂ i)
        use f
        exact fun i j hij ↦ by simpa [hf i, hf j] using hσ₁ hij
      obtain ⟨σ, hσ⟩ := h_order
      have h_inj : Function.Injective σ :=
        fun i j hij ↦ hσ.injective <| by simp [hij]
      exact ⟨Equiv.ofBijective σ ⟨h_inj, Finite.injective_iff_surjective.mp h_inj⟩, hσ⟩
    -- For all `x ∈ s`, `fun j ↦ φ (σ j) x` is `StrictMono`.
    have h_strict_mono : ∀ x ∈ s, StrictMono (fun j ↦ φ (Fin.cast hm_eq_n.symm (σ j)) x) := by
      intro x hx
      intros j k hjk
      by_contra h_contra
      have hsub : Set.uIcc x₀ x ⊆ s := by
        intro y hy
        cases Set.mem_uIcc.mp hy <;> [exact hs₃.ordConnected.out hs₂ hx ‹_› ; exact hs₃.ordConnected.out hx hs₂ ‹_›]
      have h_ivt : ∃ c ∈ Set.uIcc x₀ x, φ (Fin.cast hm_eq_n.symm (σ j)) c - φ (Fin.cast hm_eq_n.symm (σ k)) c = 0 := by
        have h_cont_ivt : ContinuousOn
            (fun x ↦ φ (Fin.cast hm_eq_n.symm (σ j)) x - φ (Fin.cast hm_eq_n.symm (σ k)) x) (Set.uIcc x₀ x) :=
          ContinuousOn.sub ((hs₄ _).continuousOn.mono hsub) ((hs₄ _).continuousOn.mono hsub)
        have := h_cont_ivt.image_uIcc
        refine this.symm.subset (Set.mem_Icc.mpr ⟨?_, ?_⟩) <;>
          nlinarith [hσ hjk,
            Set.mem_Icc.mp (this ▸ Set.mem_image_of_mem _ (Set.left_mem_uIcc)),
            Set.mem_Icc.mp (this ▸ Set.mem_image_of_mem _ (Set.right_mem_uIcc))]
      obtain ⟨c, hc₁, hc₂⟩ := h_ivt
      have := hs₆ c (hsub hc₁)
      simp_all [sub_eq_iff_eq_add, Function.Injective.eq_iff this]
    -- Therefore, `g j x = φ (σ j) x` for all `x ∈ s`.
    have h_eq : ∀ x ∈ s, T₀ ≤ x → g j x = φ (Fin.cast hm_eq_n.symm (σ j)) x := by
      intros x hx hxT₀
      simp [g, h_card x hxT₀]
      have h_mem : ∀ j : Fin n, φ (Fin.cast hm_eq_n.symm (σ j)) x ∈ realRootFinset Q x :=
        fun j ↦ mem_realRootFinset (hmonic x).ne_zero |>.2 (hs₅ _ _ hx)
      have h_eq_emb : ∀ j : Fin n,
          φ (Fin.cast hm_eq_n.symm (σ j)) x = (realRootFinset Q x).orderEmbOfFin (h_card x hxT₀) j := by
        apply_rules [Finset.orderEmbOfFin_unique]
      rw [h_eq_emb]
    apply ContDiffWithinAt.congr_of_eventuallyEq (f := fun x ↦ φ (Fin.cast hm_eq_n.symm (σ j)) x)
    · exact ContDiffWithinAt.mono_of_mem_nhdsWithin ((hs₄ _).contDiffWithinAt (by aesop)) hs₁
    · filter_upwards [hs₁, self_mem_nhdsWithin] with x hx₁ hx₂ using h_eq x hx₁ hx₂
    · exact h_eq x₀ hs₂ hx₀
  · intro j x hx
    specialize h_card x hx
    simp [g, h_card]
    exact mem_realRootFinset (hmonic x).ne_zero |>.1 (Finset.orderEmbOfFin_mem _ _ _)
  · intro x hx y hy
    specialize h_card x hx
    have := Finset.mem_image.mp
      (show y ∈ Finset.image
          (fun j : Fin n ↦ (realRootFinset Q x).orderEmbOfFin h_card j) Finset.univ from ?_)
    · aesop
    · simp_all
      exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots ((hmonic x).ne_zero) |>.2 hy)
  · intro x hx i i' hii
    have hc := h_card x hx
    simp only [g, hc, dif_pos] at hii
    exact (Finset.orderEmbOfFin (realRootFinset Q x) hc).injective hii

end SmoothRootBranches