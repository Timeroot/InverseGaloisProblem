/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.BranchAnalytic

/-!
# The ramified single-valued root section (monodromy core)

This file develops the covering-space / monodromy content behind
`DorgeBauer.separable_ramified_root_section` in `InverseGalois/Hilbert/Analytic/PuiseuxTail.lean`.

The strategy is the classical Newton–Puiseux construction, made effective through the
universal cover of the annulus at infinity `U = {z | B < ‖z‖}` by the right half-plane
`P = {ζ | Real.log B < ζ.re}` via `ζ ↦ Complex.exp ζ`:

* `branch_unique_on_connected` — two continuous roots of a separable family agreeing at one
  point of a preconnected open set agree everywhere (clopen argument via simple roots).
* `root_comp_holomorphic` — a continuous root of a separable family pulled back through a
  holomorphic substitution is holomorphic (local implicit-function branches).
* `exists_exp_lift` — the covering-space lift of `exp` yields a continuous single-valued root
  branch `g` on the half-plane `P`.
* `exists_periodic_exp_lift` — pigeonhole on the finite fibre plus lift uniqueness gives a
  ramification index `e ≥ 1` with `g` periodic of period `2πi·e`.
* `periodic_log_comp_continuous` — `w ↦ g (-(e)·log w)` is continuous on the punctured disk
  (the two log branches with complementary cuts glue by periodicity).
* `cpow_neg_e_log` — the substitution identity `-(e)·log (z⁻¹ ^ (1/e)) = log z` on the right
  half-plane.
* `branch_match_tail` — `H = g ∘ log` on the tail spheres (uniqueness of continuation).

These are assembled in `PuiseuxTail.lean`.
-/

open Filter Topology

namespace DorgeBauer

/-
**Uniqueness of a continuous root branch on a preconnected separable domain.**
Two continuous root selections of the monic family that agree at one point of a preconnected
open set on which the family is separable agree throughout.
-/
lemma branch_unique_on_connected
    (P : Polynomial (Polynomial ℤ)) (U : Set ℂ) (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hsep : ∀ z ∈ U, (P.map (evalIntPolyComplex z)).Separable)
    (g₁ g₂ : ℂ → ℂ) (hg₁ : ContinuousOn g₁ U) (hg₂ : ContinuousOn g₂ U)
    (hr₁ : ∀ z ∈ U, (P.map (evalIntPolyComplex z)).eval (g₁ z) = 0)
    (hr₂ : ∀ z ∈ U, (P.map (evalIntPolyComplex z)).eval (g₂ z) = 0)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (hbase : g₁ z₀ = g₂ z₀) :
    ∀ z ∈ U, g₁ z = g₂ z := by
  -- Let $A$ be the set of points in $U$ where $g₁$ and $g₂$ agree.
  set A : Set ℂ := {z ∈ U | g₁ z = g₂ z} with hA_def
  -- We show that $A$ is open in $U$.
  have hA_open : IsOpen A := by
    have hA_open : ∀ z ∈ A, ∃ ε > 0, Metric.ball z ε ∩ U ⊆ A := by
      intro z hz
      have := DorgeBauer.complex_branch_at_simple_root_unique P z (g₁ z) ?_ ?_ <;> simp_all [Set.subset_def]
      · obtain ⟨φ, hφ₁, hφ₂, hφ₃, hφ₄⟩ := this
        have := hφ₂.continuousAt
        simp_all [Metric.eventually_nhds_iff]
        obtain ⟨ε, hε₁, hε₂⟩ := hφ₄
        obtain ⟨δ, hδ₁, hδ₂⟩ := Metric.continuousAt_iff.mp
          (show ContinuousAt (fun x : ℂ ↦ (x, g₁ x)) z from
            ContinuousAt.prodMk continuousAt_id (hg₁.continuousAt (hUopen.mem_nhds hz.1))) ε hε₁
        obtain ⟨δ', hδ'₁, hδ'₂⟩ := Metric.continuousAt_iff.mp
          (show ContinuousAt (fun x : ℂ ↦ (x, g₂ x)) z from
            ContinuousAt.prodMk continuousAt_id (hg₂.continuousAt (hUopen.mem_nhds hz.1))) ε hε₁
        use Min.min δ δ'
        simp_all [Prod.dist_eq]
        grind
      · have := hsep z hz.1
        have := Polynomial.Separable.aeval_derivative_ne_zero this (hr₂ z hz.1)
        aesop
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    rcases hA_open x hx with ⟨ε, εpos, hε⟩
    exact Filter.mem_of_superset (Filter.inter_mem (Metric.ball_mem_nhds _ εpos)
      (hUopen.mem_nhds hx.1)) hε
  -- We show that the complement of $A$ in $U$ is also open in $U$.
  have hA_compl_open : IsOpen (U \ A) := by
    have hA_compl_open : IsOpen (U ∩ {z ∈ U | g₁ z - g₂ z ≠ 0}) := by
      have hA_compl_open : IsOpen {z ∈ U | g₁ z - g₂ z ≠ 0} := by
        have h_cont : ContinuousOn (fun z ↦ g₁ z - g₂ z) U := ContinuousOn.sub hg₁ hg₂
        exact isOpen_iff_mem_nhds.mpr fun x hx ↦
          Filter.inter_mem (hUopen.mem_nhds hx.1)
            (h_cont.continuousAt (hUopen.mem_nhds hx.1) |> fun h ↦ h.eventually_ne hx.2)
      exact hUopen.inter hA_compl_open
    convert hA_compl_open using 1
    ext
    simp [sub_eq_zero]
    grind +splitImp
  contrapose! hUconn
  simp_all [IsPreconnected]
  refine ⟨A, hA_open, {a | a ∈ U ∧ ¬g₁ a = g₂ a}, hA_compl_open, ?_,
    ⟨z₀, hz₀, hz₀, hbase⟩,
    ⟨hUconn.choose, hUconn.choose_spec.1, hUconn.choose_spec.1, hUconn.choose_spec.2⟩, ?_⟩
  · intro x hx
    by_cases h : g₁ x = g₂ x <;> aesop
  · rintro ⟨x, hx₁, hx₂⟩
    aesop

/-
**Uniqueness of a continuous root branch pulled back through a continuous substitution.**
Two continuous root selections of `P.map (evalIntPolyComplex (φ ζ))` that agree at one point
of a preconnected open set (on which the pulled-back family is separable) agree throughout.
-/
lemma branch_unique_on_connected_comp
    (P : Polynomial (Polynomial ℤ)) (U : Set ℂ) (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (φ : ℂ → ℂ) (hφ : ContinuousOn φ U)
    (hsep : ∀ ζ ∈ U, (P.map (evalIntPolyComplex (φ ζ))).Separable)
    (g₁ g₂ : ℂ → ℂ) (hg₁ : ContinuousOn g₁ U) (hg₂ : ContinuousOn g₂ U)
    (hr₁ : ∀ ζ ∈ U, (P.map (evalIntPolyComplex (φ ζ))).eval (g₁ ζ) = 0)
    (hr₂ : ∀ ζ ∈ U, (P.map (evalIntPolyComplex (φ ζ))).eval (g₂ ζ) = 0)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (hbase : g₁ z₀ = g₂ z₀) :
    ∀ ζ ∈ U, g₁ ζ = g₂ ζ := by
  contrapose! hUconn
  simp_all [IsPreconnected]
  refine ⟨{ ζ ∈ U | g₁ ζ = g₂ ζ }, ?_, { ζ ∈ U | g₁ ζ ≠ g₂ ζ }, ?_, ?_, ?_, ?_⟩ <;> norm_num [Set.Nonempty]
  · refine isOpen_iff_mem_nhds.mpr fun ζ hζ ↦ ?_
    obtain ⟨b, hb⟩ := DorgeBauer.complex_branch_at_simple_root_unique P (φ ζ) (g₁ ζ) (by
    exact hr₁ ζ hζ.1) (by
    intro h
    specialize hsep ζ hζ.1
    simp_all [Polynomial.Separable]
    obtain ⟨a, b, H⟩ := hsep
    replace H := congr_arg (Polynomial.eval (g₂ ζ)) H
    simp_all [Polynomial.eval_map])
    have h_cont : Filter.Tendsto (fun ζ ↦ (φ ζ, g₁ ζ)) (nhds ζ) (nhds (φ ζ, g₁ ζ)) ∧
        Filter.Tendsto (fun ζ ↦ (φ ζ, g₂ ζ)) (nhds ζ) (nhds (φ ζ, g₁ ζ)) := by
      refine ⟨Filter.Tendsto.prodMk_nhds (hφ.continuousAt (hUopen.mem_nhds hζ.1))
          (hg₁.continuousAt (hUopen.mem_nhds hζ.1)), ?_⟩
      exact Filter.Tendsto.prodMk_nhds (hφ.continuousAt (hUopen.mem_nhds hζ.1))
        (hg₂.continuousAt (hUopen.mem_nhds hζ.1) |> fun h ↦ h.trans (by aesop))
    filter_upwards [h_cont.1.eventually hb.2.2.2, h_cont.2.eventually hb.2.2.2,
      hUopen.mem_nhds hζ.1] with ζ hζ₁ hζ₂ hζ₃
    refine ⟨hζ₃, ?_⟩
    have := hζ₁ (hr₁ ζ hζ₃)
    have := hζ₂ (hr₂ ζ hζ₃)
    aesop
  · have h_open : ∀ ζ ∈ U, g₁ ζ ≠ g₂ ζ → ∃ ε > 0, ∀ z ∈ Metric.ball ζ ε, z ∈ U → g₁ z ≠ g₂ z := by
      intro ζ hζ hneq
      have h_cont : ContinuousAt (fun z ↦ g₁ z - g₂ z) ζ :=
        ContinuousAt.sub (hg₁.continuousAt (hUopen.mem_nhds hζ)) (hg₂.continuousAt (hUopen.mem_nhds hζ))
      have h_neq : g₁ ζ - g₂ ζ ≠ 0 := sub_ne_zero_of_ne hneq
      have h_ball : ∃ ε > 0, ∀ z ∈ Metric.ball ζ ε, z ∈ U → g₁ z - g₂ z ≠ 0 :=
        Metric.mem_nhds_iff.mp (h_cont.eventually_ne h_neq) |> fun ⟨ε, ε_pos, hε⟩ ↦ ⟨ε, ε_pos, fun z hz hzU ↦ hε hz⟩
      obtain ⟨ε, hε_pos, hε⟩ := h_ball
      use ε, hε_pos
      intro z hz hzU
      exact sub_ne_zero.mp (hε z hz hzU)
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    rcases h_open x hx.1 hx.2 with ⟨ε, ε_pos, hε⟩
    filter_upwards [Metric.ball_mem_nhds x ε_pos, hUopen.mem_nhds hx.1] with y hy₁ hy₂
      using ⟨hy₂, hε y hy₁ hy₂⟩
  · exact fun x hx ↦ if h : g₁ x = g₂ x then Or.inl ⟨hx, h⟩ else Or.inr ⟨hx, h⟩
  · exact ⟨z₀, hz₀, hbase⟩
  · grind +qlia

/-
**A continuous root of a separable family pulled back through a holomorphic substitution
is holomorphic.** If `φ` is holomorphic on an open set `V`, `F` is a continuous root of the
family `P.map (evalIntPolyComplex (φ w))` for `w ∈ V`, and the family is separable at `φ w`,
then `F` is holomorphic on `V`.
-/
lemma root_comp_holomorphic
    (P : Polynomial (Polynomial ℤ)) (V : Set ℂ) (hVopen : IsOpen V)
    (φ F : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ V) (hF : ContinuousOn F V)
    (hroot : ∀ w ∈ V, (P.map (evalIntPolyComplex (φ w))).eval (F w) = 0)
    (hsep : ∀ w ∈ V, (P.map (evalIntPolyComplex (φ w))).Separable) :
    DifferentiableOn ℂ F V := by
  intro w hw
  obtain ⟨b, hb⟩ := DorgeBauer.complex_branch_at_simple_root_unique P (φ w) (F w) (hroot w hw) (by
  exact Polynomial.Separable.aeval_derivative_ne_zero (hsep w hw) (hroot w hw))
  have h_eq : ∀ᶠ w' in nhdsWithin w V, F w' = b (φ w') := by
    have h_eq : ∀ᶠ w' in nhdsWithin w V,
        (φ w', F w') ∈ {p : ℂ × ℂ | Polynomial.eval p.2 (Polynomial.map (evalIntPolyComplex p.1) P) = 0} ∧
        (φ w', F w') ∈ {p : ℂ × ℂ | b p.1 = p.2} := by
      have h_eq : Filter.Tendsto (fun w' ↦ (φ w', F w')) (nhdsWithin w V) (nhds (φ w, F w)) :=
        Filter.Tendsto.prodMk_nhds (hφ.continuousOn.continuousWithinAt hw) (hF.continuousWithinAt hw)
      filter_upwards [h_eq.eventually hb.2.2.2, self_mem_nhdsWithin] with w' hw' hw''
        using ⟨hroot w' hw'', hw' (hroot w' hw'')⟩
    filter_upwards [h_eq] with w' hw' using hw'.2.symm
  refine DifferentiableWithinAt.congr_of_eventuallyEq ?_ h_eq ?_
  · exact DifferentiableAt.comp_differentiableWithinAt w (hb.2.1.differentiableAt (by norm_num))
      (hφ.differentiableAt (hVopen.mem_nhds hw) |> DifferentiableAt.differentiableWithinAt)
  · rw [hb.1]

/-
**Covering-space lift on the universal cover of the annulus at infinity.**
For a monic separable family over `U = {z | B < ‖z‖}`, the map `ζ ↦ exp ζ` on the half-plane
`P = {ζ | Real.log B < ζ.re}` lifts through `rootProj`, giving a continuous single-valued root
branch `g` with prescribed value `w₀` at `ζ₀`.
-/
lemma exists_exp_lift
    (Q : Polynomial (Polynomial ℤ)) (hQ_monic : Q.Monic) (B : ℝ) (hB : 1 ≤ B)
    (hQsep : ∀ z : ℂ, B < ‖z‖ → (Q.map (evalIntPolyComplex z)).Separable)
    (ζ₀ : ℂ) (hζ₀ : Real.log B < ζ₀.re) (w₀ : ℂ)
    (hw₀ : (Q.map (evalIntPolyComplex (Complex.exp ζ₀))).eval w₀ = 0) :
    ∃ g : ℂ → ℂ, ContinuousOn g {ζ : ℂ | Real.log B < ζ.re} ∧ g ζ₀ = w₀ ∧
      (∀ ζ : ℂ, Real.log B < ζ.re →
        (Q.map (evalIntPolyComplex (Complex.exp ζ))).eval (g ζ) = 0) := by
  -- By the properties of the exponential function and the definition of `rootVariety`, we can lift the map `ζ ↦ exp ζ` through `rootProj`.
  obtain ⟨F, hF⟩ : ∃ F : {ζ : ℂ | Real.log B < ζ.re} → rootVariety Q,
    Continuous F ∧
    F ⟨ζ₀, hζ₀⟩ = ⟨(Complex.exp ζ₀, w₀), hw₀⟩ ∧
    ∀ ζ, (rootProj Q (F ζ)) = Complex.exp ζ := by
      have h_covering : IsCoveringMapOn (rootProj Q) {z : ℂ | B < ‖z‖} := by
        apply DorgeBauer.rootProj_isCoveringMapOn Q hQ_monic {z : ℂ | B < ‖z‖} (by
        exact isOpen_lt continuous_const continuous_norm) (by
        exact hQsep)
      have h_contractible : ContractibleSpace {ζ : ℂ | Real.log B < ζ.re} := by
        convert Convex.contractibleSpace (convex_halfSpace_re_gt (Real.log B)) using 1
        exact ⟨fun h ↦ fun _ ↦ h, fun h ↦ h ⟨ζ₀, hζ₀⟩⟩
      have h_simply_connected : SimplyConnectedSpace {ζ : ℂ | Real.log B < ζ.re} := by
        infer_instance
      have h_locally_path_connected : LocPathConnectedSpace {ζ : ℂ | Real.log B < ζ.re} :=
        IsOpen.locPathConnectedSpace (isOpen_lt continuous_const Complex.continuous_re)
      have := h_covering.existsUnique_continuousMap_lifts
        (f := ⟨fun ζ : {ζ : ℂ | Real.log B < ζ.re} ↦ Complex.exp ζ, by continuity⟩)
        (a₀ := ⟨ζ₀, hζ₀⟩) (e₀ := ⟨(Complex.exp ζ₀, w₀), hw₀⟩) (hs := ?_) ?_ <;> norm_num at *
      · exact ⟨this.exists.choose, this.exists.choose.continuous, this.exists.choose_spec.1,
          fun a ha ↦ congr_fun this.exists.choose_spec.2 ⟨a, ha⟩⟩
      · rfl
      · intro a ha
        rw [Complex.norm_exp]
        exact Real.log_lt_iff_lt_exp (by positivity) |>.1 ha
  refine ⟨fun ζ ↦ if h : Real.log B < ζ.re then (F ⟨ζ, h⟩ : ℂ × ℂ).2 else w₀, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    convert continuous_snd.comp (continuous_subtype_val.comp hF.1) using 1
    grind
  · aesop
  · intro ζ hζ
    specialize hF
    have := hF.2.2 ⟨ζ, hζ⟩
    simp_all [rootProj]
    convert (F ⟨ζ, hζ⟩) |>.2 using 1
    rw [← hF.2.2 ζ hζ]
    rfl

/-
**Finite ramification index via monodromy.**
Continuing `g` around the annulus (i.e. shifting `ζ` by `2πi`) permutes the finitely many
sheets; pigeonhole plus lift uniqueness gives a period `e ≥ 1` with `g (ζ + 2πi·e) = g ζ`.
-/
lemma exists_periodic_exp_lift
    (Q : Polynomial (Polynomial ℤ)) (hQ_monic : Q.Monic) (B : ℝ) (hB : 1 ≤ B)
    (hQsep : ∀ z : ℂ, B < ‖z‖ → (Q.map (evalIntPolyComplex z)).Separable)
    (ζ₀ : ℂ) (hζ₀ : Real.log B < ζ₀.re) (w₀ : ℂ)
    (hw₀ : (Q.map (evalIntPolyComplex (Complex.exp ζ₀))).eval w₀ = 0) :
    ∃ (e : ℕ) (g : ℂ → ℂ), 1 ≤ e ∧
      ContinuousOn g {ζ : ℂ | Real.log B < ζ.re} ∧ g ζ₀ = w₀ ∧
      (∀ ζ : ℂ, Real.log B < ζ.re →
        (Q.map (evalIntPolyComplex (Complex.exp ζ))).eval (g ζ) = 0) ∧
      (∀ ζ : ℂ, Real.log B < ζ.re →
        g (ζ + 2 * Real.pi * Complex.I * (e : ℂ)) = g ζ) := by
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := DorgeBauer.exists_exp_lift Q hQ_monic B hB hQsep ζ₀ hζ₀ w₀ hw₀
  -- By the pigeonhole principle, since the polynomial $Q.map (evalIntPolyComplex (exp ζ₀))$ has finitely many roots, there exist $m \neq n$ such that $g(ζ₀ + 2πi·m) = g(ζ₀ + 2πi·n)$.
  obtain ⟨m, n, hmn, h_eq⟩ :
      ∃ m n : ℕ, m < n ∧ g (ζ₀ + 2 * Real.pi * Complex.I * m) = g (ζ₀ + 2 * Real.pi * Complex.I * n) := by
    have h_finite : Set.Finite (Set.range (fun n : ℕ ↦ g (ζ₀ + 2 * Real.pi * Complex.I * n))) := by
      refine Set.Finite.subset (Polynomial.map (evalIntPolyComplex (Complex.exp ζ₀)) Q
        |> Polynomial.roots |> Multiset.toFinset |> Finset.finite_toSet) ?_
      rintro _ ⟨n, rfl⟩
      specialize hg₃ (ζ₀ + 2 * Real.pi * Complex.I * n)
      simp_all [Complex.exp_add, mul_assoc, mul_left_comm]
      have hexp1 : Complex.exp (Complex.I * (Real.pi * (2 * n))) = 1 := by
        rw [Complex.exp_eq_one_iff]
        use n
        push_cast
        ring
      simp_all
      exact Polynomial.Monic.ne_zero (hQ_monic.map _)
    contrapose! h_finite
    exact Set.infinite_range_of_injective fun m n hmn ↦ le_antisymm
      (le_of_not_gt fun hmn' ↦ h_finite _ _ hmn' hmn.symm)
      (le_of_not_gt fun hmn' ↦ h_finite _ _ hmn' hmn)
  refine ⟨n - m, g, Nat.sub_pos_of_lt hmn, hg₁, hg₂, hg₃, ?_⟩
  · intro ζ hζ
    have := @branch_unique_on_connected_comp Q {ζ : ℂ | Real.log B < ζ.re} (by
    exact isOpen_lt continuous_const Complex.continuous_re) (by
    exact convex_halfSpace_re_gt _ |> Convex.isPreconnected) (fun ζ ↦ Complex.exp ζ) (by
    exact Complex.continuous_exp.continuousOn) (by
    intro ζ hζ
    apply hQsep
    simp_all [Complex.norm_exp]
    rwa [Real.log_lt_iff_lt_exp (by positivity)] at hζ)
              (fun ζ ↦ g (ζ + 2 * Real.pi * Complex.I * m))
              (fun ζ ↦ g (ζ + 2 * Real.pi * Complex.I * n)) (by
    exact hg₁.comp (continuousOn_id.add continuousOn_const) fun x hx ↦ by simpa using hx) (by
    exact hg₁.comp (continuousOn_id.add continuousOn_const) fun x hx ↦ by simpa using hx) (by
    simp_all [mul_comm (2 * Real.pi * Complex.I)]
    intro ζ hζ
    convert hg₃ (ζ + m * (2 * Real.pi * Complex.I)) (by simpa using hζ) using 1
    norm_num [Complex.exp_add, Complex.exp_nat_mul]) (by
    intro ζ hζ
    specialize hg₃ (ζ + 2 * Real.pi * Complex.I * n)
    simp_all [Complex.exp_add, mul_assoc, mul_left_comm]
    convert hg₃ using 3
    have hexp1 : Complex.exp (Complex.I * (Real.pi * (2 * n))) = 1 := by
      rw [Complex.exp_eq_one_iff]
      use n
      push_cast
      ring
    norm_num [hexp1]) ζ₀ (by
    exact hζ₀) (by
    exact h_eq)
    convert this (ζ - 2 * Real.pi * Complex.I * m)
      (by simpa [mul_assoc, mul_comm, mul_left_comm] using hζ) |> Eq.symm using 1 <;>
      push_cast [Nat.cast_sub hmn.le] <;> ring_nf

/-
**Continuity of the ramified section on the punctured disk.**
If `g` is continuous on the half-plane `P` and `2πi·e`-periodic there, then
`w ↦ g (-(e)·log w)` is continuous on the punctured disk `{0 < ‖w‖ < exp (-(log B)/e)}`.
The principal `Complex.log` (cut on the negative reals) and the branch `log (-w) + iπ` (cut on
the positive reals) together cover the disk, and they agree after applying periodicity.
-/
lemma periodic_log_comp_continuous
    (g : ℂ → ℂ) (B : ℝ) (_hB : 1 ≤ B) (e : ℕ) (he : 1 ≤ e)
    (hgc : ContinuousOn g {ζ : ℂ | Real.log B < ζ.re})
    (hper : ∀ ζ : ℂ, Real.log B < ζ.re →
        g (ζ + 2 * Real.pi * Complex.I * (e : ℂ)) = g ζ) :
    ContinuousOn (fun w : ℂ ↦ g (-(e : ℂ) * Complex.log w))
      {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < Real.exp (-(Real.log B) / e)} := by
  -- By the integer periodicity, $g(-(e:ℂ) * ℓ w) = g(-(e:ℂ) * Complex.log w)$ for all $w$ in the punctured disk.
  have h_eq : ∀ w : ℂ, 0 < ‖w‖ ∧ ‖w‖ < Real.exp (-Real.log B / e) →
      g (-(e : ℂ) * (Complex.log (-w) + Real.pi * Complex.I)) = g (-(e : ℂ) * Complex.log w) := by
    intros w hw
    obtain ⟨k, hk⟩ :
        ∃ k : ℤ, Complex.log (-w) + Real.pi * Complex.I - Complex.log w = k * (2 * Real.pi * Complex.I) := by
      have h_eq : Complex.exp (Complex.log (-w) + Real.pi * Complex.I - Complex.log w) = 1 := by
        rw [Complex.exp_sub, Complex.exp_add, Complex.exp_log, Complex.exp_log] <;> norm_num [show w ≠ 0 by aesop]
      rw [Complex.exp_eq_one_iff] at h_eq
      obtain ⟨k, hk⟩ := h_eq
      exact ⟨k, by linear_combination hk⟩
    have h_int_periodic : ∀ j : ℤ, ∀ ζ : ℂ, Real.log B < ζ.re →
        g (ζ + (j : ℂ) * (2 * Real.pi * Complex.I * e)) = g ζ := by
      intro j ζ hζ
      induction j using Int.induction_on <;> simp_all [← add_assoc, add_mul]
      have := hper (ζ + (-↑‹ℕ› - 1) * (2 * Real.pi * Complex.I * e)) ?_ <;> ring_nf at * <;> aesop
    convert h_int_periodic (-k) (-e * Complex.log w) _ using 1 <;> norm_num [mul_assoc, mul_comm, mul_left_comm]
    · grind
    · rw [Complex.log_re]
      have := Real.log_lt_log hw.1 hw.2
      norm_num at *
      nlinarith [show (e : ℝ) ≥ 1 by norm_cast,
        mul_div_cancel₀ (-Real.log B) (by positivity : (e : ℝ) ≠ 0)]
  intro w hw
  by_cases hw' : w.im = 0 ∧ w.re ≤ 0
  · have h_cont : ContinuousWithinAt (fun w ↦ g (-(e : ℂ) * (Complex.log (-w) + Real.pi * Complex.I)))
        {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < Real.exp (-Real.log B / e)} w := by
      apply ContinuousAt.continuousWithinAt
      refine hgc.continuousAt ?_ |> ContinuousAt.comp <| ContinuousAt.mul continuousAt_const <|
        ContinuousAt.add (Complex.differentiableAt_log ?_ |> DifferentiableAt.continuousAt |>
          ContinuousAt.comp <| ContinuousAt.neg continuousAt_id) continuousAt_const
      · refine IsOpen.mem_nhds ?_ ?_ <;> norm_num [Complex.log_re, Complex.log_im] at *
        · exact isOpen_lt continuous_const Complex.continuous_re
        · have := Real.log_lt_log (norm_pos_iff.mpr hw.1) hw.2
          simp_all [div_eq_mul_inv]
          nlinarith [show (e : ℝ) ≥ 1 by norm_cast, mul_inv_cancel_left₀ (by positivity : (e : ℝ) ≠ 0) (Real.log B)]
      · simp_all [Complex.slitPlane]
        refine lt_of_le_of_ne hw'.2 ?_
        rintro h
        exact hw.1 <| by simp [Complex.ext_iff, h, hw'.1]
    exact h_cont.congr (fun x hx ↦ h_eq x hx ▸ rfl) (h_eq w hw ▸ rfl)
  · apply ContinuousAt.continuousWithinAt
    refine hgc.continuousAt ?_ |> ContinuousAt.comp <| ContinuousAt.mul continuousAt_const <|
      Complex.differentiableAt_log ?_ |> DifferentiableAt.continuousAt
    · apply IsOpen.mem_nhds
      · exact isOpen_lt continuous_const Complex.continuous_re
      · simp_all [Complex.log_re]
        have := Real.log_lt_log (norm_pos_iff.mpr hw.1) hw.2
        rw [Real.log_exp] at this
        nlinarith [show (e : ℝ) ≥ 1 by norm_cast,
          mul_div_cancel₀ (-Real.log B) (by positivity : (e : ℝ) ≠ 0)]
    · refine Classical.or_iff_not_imp_left.2 fun h ↦ ?_
      contrapose! hw'
      aesop

/-
**The substitution identity** `-(e)·log (z⁻¹ ^ (1/e)) = log z` for `z` in the right
half-plane and `e ≥ 1`.
-/
lemma cpow_neg_e_log (e : ℕ) (he : 1 ≤ e) (z : ℂ) (hz : 0 < z.re) :
    -(e : ℂ) * Complex.log (z⁻¹ ^ ((e : ℂ)⁻¹)) = Complex.log z := by
  have h_arg : Complex.arg (z⁻¹) = -Complex.arg z := by
    convert Complex.arg_inv z using 1
    ring_nf
    have harg2 : z.arg < Real.pi / 2 := by
      rw [Complex.arg_lt_pi_div_two_iff]
      aesop
    rw [if_neg (by linarith [Real.pi_pos, Complex.neg_pi_lt_arg z, Complex.arg_le_pi z, harg2])]
  rw [Complex.cpow_def_of_ne_zero] <;> norm_num [h_arg, Complex.exp_ne_zero]
  · rw [Complex.log_exp] <;> norm_num [Complex.log, h_arg]
    · ring_nf
      simp [mul_assoc, mul_comm, ne_of_gt (zero_lt_one.trans_le he)]
    · rw [mul_inv_lt_iff₀ (by positivity)]
      rw [Complex.arg]
      split_ifs <;> nlinarith [Real.pi_pos, show (e : ℝ) ≥ 1 by norm_cast,
        Real.arcsin_le_pi_div_two (z.im / ‖z‖), Real.neg_pi_div_two_le_arcsin (z.im / ‖z‖)]
    · nlinarith [Real.pi_pos, show (e : ℝ) ⁻¹ ≥ 0 by positivity,
        show (e : ℝ) ⁻¹ ≤ 1 by exact inv_le_one_of_one_le₀ <| mod_cast he,
        Complex.neg_pi_lt_arg z, Complex.arg_le_pi z]
  · aesop

/-
**Matching the branch on the positive real ray (at the ball centres).**
The continuation `g ∘ log` agrees with `H` at every real centre `x ≥ T₁`. A clopen argument
on `[T₁, ∞)`: both are continuous root selections of the family with simple roots, agreeing
at the base `T₁`.
-/
lemma branch_match_real_ray
    (Q : Polynomial (Polynomial ℤ)) (B : ℝ) (hB : 1 ≤ B)
    (hQsep : ∀ z : ℂ, B < ‖z‖ → (Q.map (evalIntPolyComplex z)).Separable)
    (T₁ : ℝ) (hT1B : 2 * B < T₁) (H : ℂ → ℂ)
    (hcont : ∀ x : ℝ, T₁ ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2)))
    (hHroot : ∀ x : ℝ, T₁ ≤ x → ∀ z ∈ Metric.ball (x : ℂ) (x / 2),
        (Q.map (evalIntPolyComplex z)).eval (H z) = 0)
    (g : ℂ → ℂ) (hgc : ContinuousOn g {ζ : ℂ | Real.log B < ζ.re})
    (hgroot : ∀ ζ : ℂ, Real.log B < ζ.re →
        (Q.map (evalIntPolyComplex (Complex.exp ζ))).eval (g ζ) = 0)
    (hbase : g (Complex.log (T₁ : ℂ)) = H (T₁ : ℂ)) :
    ∀ x : ℝ, T₁ ≤ x → H (x : ℂ) = g (Complex.log (x : ℂ)) := by
  -- Consider the set $A := \{x : ℝ | T₁ ≤ x ∧ H (x:ℂ) = g (Complex.log (x:ℂ))\}$.
  set A := {x : ℝ | T₁ ≤ x ∧ H (x : ℂ) = g (Complex.log (x : ℂ))}
  -- We show that $A$ is relatively open in $[T₁, \infty)$.
  have hA_open : ∀ x ∈ A, ∃ ε > 0, ∀ y : ℝ, T₁ ≤ y → |y - x| < ε → y ∈ A := by
    intro x hx
    obtain ⟨hxT₁, hxH⟩ := hx
    have h_simple_root : (Q.map (evalIntPolyComplex (x : ℂ))).derivative.eval (H (x : ℂ)) ≠ 0 := by
      have := hQsep (x : ℂ) ?_ <;> simp_all [Polynomial.Separable]
      · obtain ⟨a, b, h⟩ := this
        replace h := congr_arg (Polynomial.eval (g (Complex.log x))) h
        simp_all [Polynomial.eval_map]
        intro H
        simp_all [Polynomial.eval₂_eq_sum_range]
        specialize hgroot (Complex.log x)
        have hxne : (x : ℂ) ≠ 0 := by
          norm_cast
          linarith
        simp_all [Complex.exp_log hxne]
        simp_all [Complex.log_re, Real.log_lt_log (by linarith : 0 < B) (by linarith : B < x)]
      · cases abs_cases x <;> linarith
    obtain ⟨φ, hφ₁, hφ₂, hφ₃, hφ₄⟩ :=
      DorgeBauer.complex_branch_at_simple_root_unique Q (x : ℂ) (H (x : ℂ)) (hHroot x hxT₁ x (by
      norm_num [show x > 0 by linarith])) h_simple_root
    -- By the uniqueness of the branch $\phi$, we have $H(y) = \phi(y)$ and $g(\log(y)) = \phi(y)$ for $y$ sufficiently close to $x$.
    obtain ⟨ε, hε_pos, hε⟩ :
        ∃ ε > 0, ∀ y : ℂ, ‖y - (x : ℂ)‖ < ε → H y = φ y ∧ g (Complex.log y) = φ y := by
      have hH_eq_phi : ∀ᶠ y in nhds (x : ℂ), H y = φ y := by
        have hH_eq_phi : ∀ᶠ y in nhds (x : ℂ),
            (y, H y) ∈ {p : ℂ × ℂ | Polynomial.eval p.2 (Polynomial.map (evalIntPolyComplex p.1) Q) = 0} := by
          filter_upwards [Metric.ball_mem_nhds _ (show 0 < x / 2 by linarith)] with y hy using hHroot x hxT₁ y hy
        have htend : Filter.Tendsto (fun y : ℂ ↦ (y, H y)) (nhds (x : ℂ)) (nhds (x, H x)) := by
          refine Filter.Tendsto.prodMk_nhds Filter.tendsto_id ?_
          have := hcont x hxT₁
          convert this.continuousOn.continuousAt _ using 1
          exact Filter.mem_of_superset (Metric.ball_mem_nhds _ <| half_pos <| by linarith)
            fun y hy ↦ subset_closure hy
        filter_upwards [hH_eq_phi, hφ₄.filter_mono htend] with y hy₁ hy₂ using by aesop
      have hg_log_eq_phi : ∀ᶠ y in nhds (x : ℂ), g (Complex.log y) = φ y := by
        have hg_log_eq_phi : ∀ᶠ y in nhds (x : ℂ), (Q.map (evalIntPolyComplex y)).eval (g (Complex.log y)) = 0 := by
          have hg_log_eq_phi : ∀ᶠ y in nhds (x : ℂ), Real.log B < (Complex.log y).re := by
            have h_log_cont : Filter.Tendsto (fun y : ℂ ↦ (Complex.log y).re) (nhds (x : ℂ)) (nhds (Real.log x)) := by
              have h_log_cont :
                  Filter.Tendsto (fun y : ℂ ↦ Complex.log y) (nhds (x : ℂ)) (nhds (Complex.log (x : ℂ))) := by
                convert Complex.differentiableAt_log _ |> DifferentiableAt.continuousAt using 1
                refine Or.inl ?_
                norm_num
                linarith
              convert Complex.continuous_re.continuousAt.tendsto.comp h_log_cont using 2
              norm_num [Complex.log_re]
            exact h_log_cont.eventually (lt_mem_nhds <| Real.log_lt_log (by linarith) <| by linarith)
          have hxne : (x : ℂ) ≠ 0 := by
            norm_cast
            linarith
          filter_upwards [hg_log_eq_phi, isOpen_ne.mem_nhds hxne] with y hy₁ hy₂
          convert hgroot (Complex.log y) hy₁ using 1
          rw [Complex.exp_log hy₂]
        have htend : Filter.Tendsto (fun y : ℂ ↦ (y, g (Complex.log y))) (nhds (x : ℂ)) (nhds (x, H x)) := by
          apply Filter.Tendsto.prodMk_nhds
          · exact Filter.tendsto_id
          · have hg_log_eq_phi : ContinuousAt (fun y ↦ g (Complex.log y)) (x : ℂ) := by
              refine hgc.continuousAt ?_ |> ContinuousAt.comp <|
                Complex.differentiableAt_log ?_ |> DifferentiableAt.continuousAt
              · apply IsOpen.mem_nhds
                · exact isOpen_lt continuous_const Complex.continuous_re
                · norm_num [Complex.log_re]
                  exact Real.log_lt_log (by linarith) (by linarith)
              · refine Or.inl ?_
                norm_num
                linarith
            exact hg_log_eq_phi.tendsto.trans (by aesop)
        filter_upwards [hg_log_eq_phi, hφ₄.filter_mono htend] with y hy₁ hy₂ using by aesop
      exact Metric.mem_nhds_iff.mp (hH_eq_phi.and hg_log_eq_phi) |> fun ⟨ε, hε₁, hε₂⟩ ↦ ⟨ε, hε₁, fun y hy ↦ hε₂ hy⟩
    use ε, hε_pos
    intro y hy₁ hy₂
    specialize hε y
    simp_all [Complex.norm_def, Complex.normSq]
    exact ⟨hy₁, by simp [hε (by rwa [Real.sqrt_mul_self_eq_abs])]⟩
  -- We show that $A$ is relatively closed in $[T₁, \infty)$.
  have hA_closed : ∀ x : ℝ, T₁ ≤ x → (∀ ε > 0, ∃ y : ℝ, T₁ ≤ y ∧ |y - x| < ε ∧ y ∈ A) → x ∈ A := by
    intros x hx hseq
    have h_cont : ContinuousOn (fun y : ℝ ↦ H (y : ℂ) - g (Complex.log (y : ℂ))) (Set.Ici T₁) := by
      apply ContinuousOn.sub
      · intro y hy
        specialize hcont y hy
        have := hcont.continuousOn
        apply ContinuousAt.continuousWithinAt
        refine this.continuousAt ?_ |> ContinuousAt.comp <| Complex.continuous_ofReal.continuousAt
        rw [closure_ball] <;> norm_num [show y ≠ 0 by linarith [Set.mem_Ici.mp hy]]
        exact Metric.closedBall_mem_nhds _ (half_pos (by linarith [Set.mem_Ici.mp hy]))
      · apply hgc.comp
        · apply ContinuousOn.clog
          · exact Complex.continuous_ofReal.continuousOn
          · intro x hx
            refine Or.inl ?_
            norm_num
            linarith [Set.mem_Ici.mp hx]
        · intro y hy
          simp [Complex.log_re]
          exact Real.log_lt_log (by linarith) (by linarith [Set.mem_Ici.mp hy])
    have h_seq : ∃ seq : ℕ → ℝ, (∀ n, T₁ ≤ seq n ∧ seq n ∈ A) ∧ Filter.Tendsto seq Filter.atTop (nhds x) := by
      exact ⟨fun n ↦ Classical.choose (hseq (1 / (n + 1)) (by positivity)),
        fun n ↦ ⟨Classical.choose_spec (hseq (1 / (n + 1)) (by positivity)) |>.1,
          Classical.choose_spec (hseq (1 / (n + 1)) (by positivity)) |>.2.2⟩,
        tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero (fun _ ↦ by positivity)
          (fun n ↦ Classical.choose_spec (hseq (1 / (n + 1)) (by positivity)) |>.2.1.le) <|
          tendsto_one_div_add_atTop_nhds_zero_nat⟩
    obtain ⟨seq, hseq₁, hseq₂⟩ := h_seq
    have h_seq_zero : Filter.Tendsto (fun n ↦ H (seq n : ℂ) - g (Complex.log (seq n : ℂ))) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.congr fun n ↦ by rw [hseq₁ n |>.2.2, sub_self]
    have := h_cont.continuousWithinAt (show x ∈ Set.Ici T₁ from hx)
    refine ⟨hx, ?_⟩
    simpa [sub_eq_zero] using
      tendsto_nhds_unique (this.tendsto.comp (show Filter.Tendsto seq Filter.atTop
        (nhdsWithin x (Set.Ici T₁)) from tendsto_nhdsWithin_iff.mpr
          ⟨hseq₂, Filter.Eventually.of_forall fun n ↦ hseq₁ n |>.1⟩)) h_seq_zero
  -- Since $A$ is both open and closed in $[T₁, \infty)$, and $T₁ \in A$, it follows that $A = [T₁, \infty)$.
  have hA_eq : A = Set.Ici T₁ := by
    apply Set.eq_of_subset_of_subset
    · exact fun x hx ↦ hx.1
    · intro x hx
      contrapose! hA_closed
      use sInf { y : ℝ | T₁ ≤ y ∧ y ∉ A }
      refine ⟨le_csInf ⟨x, hx, hA_closed⟩ fun y hy ↦ hy.1, ?_, ?_⟩
      · intro ε ε_pos
        by_cases h_inf : sInf { y : ℝ | T₁ ≤ y ∧ y ∉ A } = T₁
        · exact ⟨T₁, le_rfl, by simpa [h_inf] using ε_pos, ⟨le_rfl, by simp [hbase]⟩⟩
        · obtain ⟨y, hy₁, hy₂⟩ :
              ∃ y ∈ Set.Ioo T₁ (sInf {y : ℝ | T₁ ≤ y ∧ y ∉ A}), |y - sInf {y : ℝ | T₁ ≤ y ∧ y ∉ A}| < ε := by
            have h_inf_gt_T1 : T₁ < sInf { y : ℝ | T₁ ≤ y ∧ y ∉ A } :=
              lt_of_le_of_ne (le_csInf ⟨x, hx, hA_closed⟩ fun y hy ↦ hy.1) (Ne.symm h_inf)
            by_cases h_inf_gt_T1 : sInf { y : ℝ | T₁ ≤ y ∧ y ∉ A } - T₁ < ε
            · exact ⟨(T₁ + sInf {y : ℝ | T₁ ≤ y ∧ y ∉ A}) / 2, ⟨by linarith, by linarith⟩,
                abs_lt.mpr ⟨by linarith, by linarith⟩⟩
            · exact ⟨sInf {y : ℝ | T₁ ≤ y ∧ y ∉ A} - ε / 2, ⟨by linarith, by linarith⟩,
                abs_lt.mpr ⟨by linarith, by linarith⟩⟩
          exact ⟨y, hy₁.1.le, hy₂,
            Classical.not_not.1 fun hy₃ ↦ hy₁.2.not_ge <| csInf_le ⟨T₁, fun x hx ↦ hx.1⟩ ⟨hy₁.1.le, hy₃⟩⟩
      · intro h
        obtain ⟨ε, ε_pos, hε⟩ := hA_open _ h
        obtain ⟨y, hy₁, hy₂⟩ := exists_lt_of_csInf_lt
          (show {y : ℝ | T₁ ≤ y ∧ y ∉ A}.Nonempty from ⟨x, hx, hA_closed⟩) (lt_add_of_pos_right _ ε_pos)
        have hle : sInf {y : ℝ | T₁ ≤ y ∧ y ∉ A} ≤ y := csInf_le ⟨T₁, fun z hz ↦ hz.1⟩ hy₁
        exact hy₁.2 <| hε y hy₁.1 <| abs_lt.mpr ⟨by linarith [hle], by linarith [hle]⟩
  exact fun x hx ↦ hA_eq.symm.subset hx |>.2

/-
**Matching the branch on the tail spheres.**
The continuation `g ∘ log` agrees with `H` on the tail spheres, by uniqueness of the
continuous root branch on the (connected) horn of tail balls and continuity up to the
boundary.
-/
lemma branch_match_tail
    (Q : Polynomial (Polynomial ℤ)) (B : ℝ) (hB : 1 ≤ B)
    (hQsep : ∀ z : ℂ, B < ‖z‖ → (Q.map (evalIntPolyComplex z)).Separable)
    (T₁ : ℝ) (hT1B : 2 * B < T₁) (H : ℂ → ℂ)
    (hcont : ∀ x : ℝ, T₁ ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2)))
    (hHroot : ∀ x : ℝ, T₁ ≤ x → ∀ z ∈ Metric.ball (x : ℂ) (x / 2),
        (Q.map (evalIntPolyComplex z)).eval (H z) = 0)
    (g : ℂ → ℂ) (hgc : ContinuousOn g {ζ : ℂ | Real.log B < ζ.re})
    (hgroot : ∀ ζ : ℂ, Real.log B < ζ.re →
        (Q.map (evalIntPolyComplex (Complex.exp ζ))).eval (g ζ) = 0)
    (hbase : g (Complex.log (T₁ : ℂ)) = H (T₁ : ℂ)) :
    ∀ x : ℝ, T₁ ≤ x → ∀ z ∈ Metric.sphere (x : ℂ) (x / 2),
      H z = g (Complex.log z) := by
  intro x hx z hz
  have h_cont : ContinuousOn (fun z ↦ g (Complex.log z)) (Metric.closedBall (x : ℂ) (x / 2)) := by
    refine hgc.comp (ContinuousOn.clog ?_ ?_) ?_
    · exact continuousOn_id
    · norm_num [Complex.slitPlane]
      intro w hw
      contrapose! hw
      simp_all [Complex.dist_eq, Complex.normSq, Complex.norm_def]
      rw [Real.sqrt_mul_self_eq_abs, abs_of_nonpos] <;> linarith
    · intro z hz
      simp_all [Complex.log_re]
      gcongr
      have := norm_sub_le (z : ℂ) (z - x)
      norm_num at *
      linarith [abs_of_nonneg (by linarith : 0 ≤ x), dist_eq_norm z x]
  have h_eq : ∀ z' ∈ Metric.ball (x : ℂ) (x / 2), H z' = g (Complex.log z') := by
    apply DorgeBauer.branch_unique_on_connected
    · exact Metric.isOpen_ball
    · exact Metric.isPreconnected_ball
    any_goals exact Q
    any_goals exact hcont x hx |>.differentiableOn.continuousOn
    any_goals exact Metric.mem_ball_self (by linarith)
    · intro z hz
      apply hQsep
      have := norm_sub_le (z : ℂ) (z - x)
      norm_num at *
      linarith [abs_of_nonneg (by linarith : 0 ≤ x), dist_eq_norm z x]
    · exact h_cont.mono (Metric.ball_subset_closedBall)
    · exact hHroot x hx
    · intro z hz
      have hz_log : Complex.exp (Complex.log z) = z := by
        rw [Complex.exp_log]
        intro h
        norm_num [h] at hz
        linarith [abs_lt.mp (show |x| < x / 2 by simpa [abs_of_nonneg (by linarith : 0 ≤ x)] using hz)]
      have hz_log_re : Real.log B < (Complex.log z).re := by
        rw [Complex.log_re]
        gcongr
        have := norm_sub_le (z : ℂ) (z - x)
        norm_num at *
        rw [abs_of_nonneg] at this <;> linarith [dist_eq_norm z x]
      exact (by
      simpa only [hz_log] using hgroot (Complex.log z) hz_log_re)
    · have := branch_match_real_ray Q B hB hQsep T₁ hT1B H hcont hHroot g hgc hgroot hbase x hx
      aesop
  have h_eq_closure : ∀ z' ∈ Metric.closedBall (x : ℂ) (x / 2), H z' = g (Complex.log z') := by
    intro z' hz'
    have hz'cl : z' ∈ closure (Metric.ball (x : ℂ) (x / 2)) := by
      rw [closure_ball (x : ℂ) (by linarith)]
      exact hz'
    obtain ⟨seq, hseq⟩ := mem_closure_iff_seq_limit.mp hz'cl
    have h_eq_seq : Filter.Tendsto (fun n ↦ H (seq n)) Filter.atTop (nhds (H z')) := by
      have := hcont x hx
      have := this.continuousOn
      exact this.continuousWithinAt hz'cl |> fun h ↦ h.tendsto.comp <|
        Filter.tendsto_inf.mpr ⟨hseq.2, Filter.tendsto_principal.mpr <|
          Filter.Eventually.of_forall fun n ↦ subset_closure <| hseq.1 n⟩
    refine tendsto_nhds_unique h_eq_seq ?_
    simpa only [h_eq _ (hseq.1 _)] using
      h_cont.continuousWithinAt (show z' ∈ Metric.closedBall (x : ℂ) (x / 2) from hz') |>
        fun h ↦ h.tendsto.comp <| Filter.tendsto_inf.mpr ⟨hseq.2,
          Filter.tendsto_principal.mpr <| Filter.Eventually.of_forall fun n ↦
            by simpa using hseq.1 n |> Metric.mem_ball.mp |> fun h ↦ by simpa using h.le⟩
  exact h_eq_closure z <| Metric.sphere_subset_closedBall hz

end DorgeBauer