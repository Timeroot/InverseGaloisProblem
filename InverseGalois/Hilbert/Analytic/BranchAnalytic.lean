/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.DorgeBauerAnalytic

/-!
# Analytic continuation of algebraic branches off the real axis

This file develops the analytic theory needed to build the holomorphic continuation of a
real algebraic branch `g` of a monic family `P(x, ·)` onto complex tail balls, which is the
"continuation half" of `DorgeBauer.real_branch_full_holomorphic_continuation`.

The main results:

* `continuous_root_holomorphic` — a *continuous* root of a separable holomorphic family is
  automatically *holomorphic* (each value is a simple root, so it locally coincides with the
  implicit-function branch).
* `complex_branch_holomorphic_on_convex` — on a convex open set `U` on which the complex
  family is everywhere separable, any root `w₀` of the family at a base point `z₀ ∈ U`
  extends to a holomorphic root branch `H : ℂ → ℂ` on all of `U`.  This is the monodromy /
  covering-space core: `U` is contractible hence simply connected, the root projection is a
  covering map, and the section lifts.
-/

open Filter Topology

namespace DorgeBauer

/-
**Local holomorphic branch at a simple complex root, with local uniqueness.**

Strengthening of `complex_branch_at_simple_root`: the branch `φ` obtained from the implicit
function theorem is not only a root near `z₀` but is the *unique* nearby root: for `(z, w)`
near `(z₀, w₀)`, any root `w` of `P.map (evalIntPolyComplex z)` equals `φ z`.  This is the
local-uniqueness clause `eventually_implicitFunction_apply_eq` of the analytic implicit
function theorem.
-/
lemma complex_branch_at_simple_root_unique
    (P : Polynomial (Polynomial ℤ)) (z₀ w₀ : ℂ)
    (hroot : (P.map (evalIntPolyComplex z₀)).eval w₀ = 0)
    (hsimple : (P.map (evalIntPolyComplex z₀)).derivative.eval w₀ ≠ 0) :
    ∃ φ : ℂ → ℂ, φ z₀ = w₀ ∧ ContDiffAt ℂ ⊤ φ z₀ ∧
      (∀ᶠ z : ℂ in nhds z₀, (P.map (evalIntPolyComplex z)).eval (φ z) = 0) ∧
      (∀ᶠ p : ℂ × ℂ in nhds (z₀, w₀),
        (P.map (evalIntPolyComplex p.1)).eval p.2 = 0 → φ p.1 = p.2) := by
  obtain ⟨φ, hφ⟩ :
      ∃ φ : ℂ → ℂ, φ z₀ = w₀ ∧ ContDiffAt ℂ ⊤ φ z₀ ∧
        (∀ᶠ z in nhds z₀, (P.map (evalIntPolyComplex z)).eval (φ z) = 0) :=
    complex_branch_at_simple_root P z₀ w₀ hroot hsimple
  refine ⟨φ, hφ.1, hφ.2.1, hφ.2.2, ?_⟩
  have h_implicit :
      IsContDiffImplicitAt ⊤ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2)
        (fderiv ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2) (z₀, w₀)) (z₀, w₀) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply_rules [DifferentiableAt.hasFDerivAt]
      refine (evalIntPolyComplex_eval_contDiff P).differentiable ?_ (z₀, w₀)
      norm_num
    · exact evalIntPolyComplex_eval_contDiff P |> ContDiff.contDiffAt
    · have h_deriv :
        (fderiv ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2) (z₀, w₀)) (0, 1) =
          (P.map (evalIntPolyComplex z₀)).derivative.eval w₀ := by
        have h_deriv_eq :
          deriv (fun y ↦ (P.map (evalIntPolyComplex z₀)).eval y) w₀ =
            (fderiv ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2) (z₀, w₀)) (0, 1) := by
          convert HasDerivAt.deriv (HasFDerivAt.hasDerivAt (HasFDerivAt.comp w₀
            (show HasFDerivAt
                (fun p : ℂ × ℂ ↦ Polynomial.eval p.2 (Polynomial.map (evalIntPolyComplex p.1) P)) _ _ from ?_)
            (hasFDerivAt_const _ _ |> HasFDerivAt.prodMk <| hasFDerivAt_id _))) using 1
          apply_rules [DifferentiableAt.hasFDerivAt]
          refine (evalIntPolyComplex_eval_contDiff P).differentiable ?_ (z₀, w₀)
          norm_num
        rw [← h_deriv_eq, Polynomial.deriv]
      refine ⟨?_, ?_⟩
      · intro x y hxy
        simp_all
        have h_deriv :
          (fderiv ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2) (z₀, w₀)) (0, x) =
              x * (P.map (evalIntPolyComplex z₀)).derivative.eval w₀ ∧
            (fderiv ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2) (z₀, w₀)) (0, y) =
              y * (P.map (evalIntPolyComplex z₀)).derivative.eval w₀ := by
          have h_deriv_all : ∀ x : ℂ,
              (fderiv ℂ (fun p : ℂ × ℂ ↦ (P.map (evalIntPolyComplex p.1)).eval p.2) (z₀, w₀)) (0, x) =
                x * (P.map (evalIntPolyComplex z₀)).derivative.eval w₀ := by
            intro x
            convert congr_arg (fun y ↦ x * y) h_deriv using 1
            · ring_nf!
              rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul]
              norm_num
            · simp [Polynomial.derivative_map]
          exact ⟨h_deriv_all x, h_deriv_all y⟩
        simp_all [Polynomial.derivative_map]
      · intro x
        use x / (Polynomial.eval w₀ (Polynomial.derivative (Polynomial.map (evalIntPolyComplex z₀) P)))
        simp
        convert congr_arg
          (fun y ↦ y * (x / Polynomial.eval w₀ (Polynomial.derivative (Polynomial.map (evalIntPolyComplex z₀) P))))
          h_deriv using 1 <;> ring_nf!
        · convert
            (fderiv ℂ (fun p : ℂ × ℂ ↦ Polynomial.eval p.2 (Polynomial.map (evalIntPolyComplex p.1) P))
                (z₀, w₀)).map_smul
            (x * (Polynomial.eval w₀ (Polynomial.map (evalIntPolyComplex z₀) (Polynomial.derivative P))) ⁻¹)
              (0, 1) using 1
          · ring_nf!
            norm_num [Prod.smul_def]
          · simp [mul_assoc, mul_comm, mul_left_comm, Polynomial.derivative_map]
        · rw [mul_right_comm, mul_inv_cancel₀ hsimple, one_mul]
    · norm_num
  have := h_implicit.eventually_implicitFunction_apply_eq
  have h_eq : ∀ᶠ z in nhds z₀, h_implicit.implicitFunction z = φ z := by
    have h_eq : Filter.Tendsto (fun z ↦ (z, φ z)) (nhds z₀) (nhds (z₀, w₀)) := by
      refine Filter.Tendsto.prodMk_nhds Filter.tendsto_id (hφ.2.1.continuousAt.tendsto.trans ?_)
      simp_all
    filter_upwards [h_eq.eventually this, hφ.2.2] with z hz₁ hz₂
    simp_all
  filter_upwards [this, h_eq.prod_nhds (Filter.eventually_of_mem (Metric.ball_mem_nhds _ zero_lt_one) fun x hx ↦ hx)]
    with p hp hp'
  simp_all

/-- **A continuous root of a separable holomorphic family is holomorphic.**

If `H` is continuous on an open set `U`, is a genuine root of the complex family
`P.map (evalIntPolyComplex z)` for every `z ∈ U`, and the family is separable on `U`, then
`H` is holomorphic (differentiable) on `U`.

Reason: at each `z₀ ∈ U`, `w₀ := H z₀` is a *simple* root (separability gives nonzero
`Y`-derivative), so `complex_branch_at_simple_root` provides a holomorphic implicit-function
branch `φ` through `(z₀, w₀)` that is the *unique* nearby root; by continuity `H` coincides
with `φ` near `z₀`, hence is holomorphic there. -/
lemma continuous_root_holomorphic
    (P : Polynomial (Polynomial ℤ)) (U : Set ℂ) (hUopen : IsOpen U)
    (H : ℂ → ℂ) (hHc : ContinuousOn H U)
    (hroot : ∀ z ∈ U, (P.map (evalIntPolyComplex z)).eval (H z) = 0)
    (hsep : ∀ z ∈ U, (P.map (evalIntPolyComplex z)).Separable) :
    DifferentiableOn ℂ H U := by
  intro z₀ hz₀
  -- `w₀ := H z₀` is a simple root; get the locally unique holomorphic branch `φ`.
  have hsimple : (P.map (evalIntPolyComplex z₀)).derivative.eval (H z₀) ≠ 0 :=
    Polynomial.Separable.aeval_derivative_ne_zero (hsep z₀ hz₀) (hroot z₀ hz₀)
  obtain ⟨φ, hφ0, hφcd, hφroot, hφuniq⟩ :=
    complex_branch_at_simple_root_unique P z₀ (H z₀) (hroot z₀ hz₀) hsimple
  -- `H = φ` near `z₀`: `H` is continuous with `H z₀ = w₀ = φ z₀`, so `(z, H z) → (z₀, w₀)`,
  -- and `H z` is a root, so local uniqueness forces `φ z = H z`.
  have hHtendsto : Filter.Tendsto (fun z ↦ (z, H z)) (nhds z₀) (nhds (z₀, H z₀)) :=
    (Filter.Tendsto.prodMk_nhds tendsto_id (hHc.continuousAt (hUopen.mem_nhds hz₀)))
  have hEq : H =ᶠ[nhds z₀] φ := by
    filter_upwards [hHtendsto.eventually hφuniq, hUopen.mem_nhds hz₀] with z hz hzU
    exact (hz (hroot z hzU)).symm
  have hd : DifferentiableAt ℂ φ z₀ := hφcd.differentiableAt (by norm_num)
  exact (hd.congr_of_eventuallyEq hEq).differentiableWithinAt

/-!
### The root projection as a covering map

We realise the algebraic function as a covering space: the complex root variety of the monic
family projects to the base `ℂ`, and over any separable open set this projection is a
covering map (a closed map with finite fibres that is a local homeomorphism).
-/

/-- The complex root variety of the monic family `P.map (evalIntPolyComplex ·)`. -/
def rootVariety (P : Polynomial (Polynomial ℤ)) : Set (ℂ × ℂ) :=
  {q | (P.map (evalIntPolyComplex q.1)).eval q.2 = 0}

/-- Projection from the complex root variety to the base plane. -/
def rootProj (P : Polynomial (Polynomial ℤ)) : rootVariety P → ℂ := fun q ↦ (q : ℂ × ℂ).1

lemma continuous_rootProj (P : Polynomial (Polynomial ℤ)) : Continuous (rootProj P) :=
  (continuous_fst.comp continuous_subtype_val)

/-
**Finite fibres.**  Over any base point the root projection has a finite fibre (the
roots of the monic specialization, of which there are at most `P.natDegree`).
-/
lemma rootProj_finite_fiber
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic) (x : ℂ) :
    ((rootProj P) ⁻¹' {x}).Finite := by
  -- Consider the polynomial `Q(y) = (P.map (evalIntPolyComplex x)).eval y`.
  set Q : Polynomial ℂ := P.map (evalIntPolyComplex x)
  -- Since `Q` is a non-zero polynomial, its roots form a finite set.
  have hQ_nonzero : Q ≠ 0 := Polynomial.Monic.ne_zero (hP.map _)
  refine Set.Finite.of_finite_image (f := fun q ↦ q.val.2) ?_ ?_
  · apply Set.Finite.subset (Q.roots.toFinset.finite_toSet)
    intro y hy
    simp_all only [ne_eq, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff, Subtype.exists, exists_and_right,
      Prod.exists, exists_eq_right, SetLike.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots', not_false_eq_true,
      Polynomial.IsRoot.def, true_and, Q]
    obtain ⟨w, h⟩ := hy
    obtain ⟨w_1, h⟩ := h
    subst h
    exact w_1
  · intro q hq q' hq' h
    simp only [Set.mem_preimage, Set.mem_singleton_iff, rootProj] at hq hq'
    exact Subtype.ext <| Prod.ext (hq.trans hq'.symm) h

/-
**The root projection is a closed map.**  This is the properness of the algebraic
function: over a compact set the roots of the monic family stay bounded (Cauchy's bound), so
preimages of compacts are compact.
-/
lemma rootProj_isClosedMap
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic) :
    IsClosedMap (rootProj P) := by
  -- Properness: preimages of compact sets are compact, hence the map is closed.
  have h_closed_map : ∀ K : Set ℂ, IsCompact K → IsCompact (rootProj P ⁻¹' K) := by
    intro K hK
    set T := {q : ℂ × ℂ | q.1 ∈ K ∧ (P.map (evalIntPolyComplex q.1)).eval q.2 = 0} with hT_def
    have hT_closed : IsClosed T := by
      apply IsClosed.inter (hK.isClosed.preimage continuous_fst)
      have h_cont : Continuous (fun q : ℂ × ℂ ↦ (P.map (evalIntPolyComplex q.1)).eval q.2) :=
        evalIntPolyComplex_eval_contDiff P |> ContDiff.continuous
      exact isClosed_eq h_cont continuous_const
    have hT_bounded : ∃ M : ℝ, ∀ q ∈ T, ‖q.2‖ ≤ M := by
      -- By the Cauchy root bound, any root `w` of `P.map (evalIntPolyComplex z)` satisfies
      -- `‖w‖ ≤ 1 + ∑ i, ‖cᵢ‖`, where the `cᵢ` are the coefficients.
      have h_cauchy_bound : ∀ z ∈ K, ∀ w : ℂ, (P.map (evalIntPolyComplex z)).eval w = 0 →
          ‖w‖ ≤ 1 + ∑ i ∈ Finset.range P.natDegree, ‖(P.map (evalIntPolyComplex z)).coeff i‖ := by
        intros z hz w hw_root
        have h_cb :
          ‖w‖ ≤ 1 + ∑ i ∈ Finset.range (P.map (evalIntPolyComplex z)).natDegree,
            ‖(P.map (evalIntPolyComplex z)).coeff i‖ := by
          convert cauchy_root_bound _ hw_root using 1
          exact hP.map _
        rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] at h_cb <;> simp_all
      -- Since `K` is compact, the coefficients of `P.map (evalIntPolyComplex z)` are bounded on `K`.
      have h_coeff_bounded : ∃ M : ℝ, ∀ z ∈ K, ∀ i ∈ Finset.range P.natDegree,
          ‖(P.map (evalIntPolyComplex z)).coeff i‖ ≤ M := by
        have h_coeff_all : ∀ i ∈ Finset.range P.natDegree, ∃ M : ℝ, ∀ z ∈ K,
            ‖(P.map (evalIntPolyComplex z)).coeff i‖ ≤ M := by
          intro i hi
          have h_coeff_cont : Continuous (fun z : ℂ ↦ (P.map (evalIntPolyComplex z)).coeff i) := by
            simpa [Polynomial.coeff_map] using Polynomial.continuous _
          exact IsCompact.exists_bound_of_continuousOn hK h_coeff_cont.continuousOn
        choose! M hM using h_coeff_all
        exact ⟨∑ i ∈ Finset.range P.natDegree, M i,
          fun z hz i hi ↦ le_trans (hM i hi z hz)
            (Finset.single_le_sum (fun i _ ↦ le_trans (by positivity) (hM i ‹_› z hz)) hi)⟩
      obtain ⟨M, hM⟩ := h_coeff_bounded
      use 1 + P.natDegree * M
      intro q hq
      specialize h_cauchy_bound q.1 hq.1 q.2 hq.2
      refine le_trans h_cauchy_bound ?_
      simp_all
      exact le_trans (Finset.sum_le_sum fun _ _ ↦ hM _ hq.1 _ (Finset.mem_range.mp ‹_›)) (by norm_num)
    have hT_compact : IsCompact T := by
      apply IsCompact.of_isClosed_subset (hK.prod (ProperSpace.isCompact_closedBall 0 hT_bounded.choose)) hT_closed
      exact fun q hq ↦ ⟨hq.1, mem_closedBall_zero_iff.mpr (hT_bounded.choose_spec q hq)⟩
    have h_preimage_compact : IsCompact ((rootProj P) ⁻¹' K) := by
      convert hT_compact using 1
      constructor <;> intro h <;> rw [isCompact_iff_compactSpace] at * <;> simp_all
      apply isCompact_iff_compactSpace.mp
      convert h.isCompact_univ.image
        (show Continuous (fun q : T ↦ ⟨q.val, by simp_all only [Set.coe_setOf, Set.mem_setOf_eq, T]; obtain ⟨w, h_1⟩ := hT_bounded; obtain ⟨val, property⟩ := q; obtain ⟨fst, snd⟩ := val; simp_all only; simp_all only [Set.mem_setOf_eq, T]; obtain ⟨left, right⟩ := property; exact right⟩ : T → rootVariety P) from ?_) using 1
      · ext
        rename_i x
        simp_all only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_preimage, Set.image_univ, Set.mem_range, Subtype.exists,
          Prod.exists, T]
        obtain ⟨w, h_1⟩ := hT_bounded
        obtain ⟨val, property⟩ := x
        obtain ⟨fst, snd⟩ := val
        simp_all only [Subtype.mk.injEq, Prod.mk.injEq, exists_and_left, exists_prop, ↓existsAndEq, and_true, exists_eq_left]
        apply Iff.intro
        · intro a
          apply And.intro
          · exact a
          · exact property
        · intro a
          obtain ⟨left, right⟩ := a
          exact left
      · fun_prop (disch := solve_by_elim)
    exact h_preimage_compact
  apply IsProperMap.isClosedMap
  exact isProperMap_iff_isCompact_preimage.mpr ⟨continuous_rootProj P, h_closed_map⟩

/-
**Local open-embedding from a section.**  Given a holomorphic section `ψ` of the root
family over an open box `Vz ×ˢ Vw`, which by local uniqueness is the *only* root branch in
the box, the root projection restricted to the corresponding open subset of the root variety
is an open embedding onto `Vz`.  This is the topological heart of the local-homeomorphism
property, with the section given explicitly (no implicit-function bookkeeping).
-/
lemma rootProj_restrict_isOpenEmbedding
    (P : Polynomial (Polynomial ℤ))
    (Vz Vw : Set ℂ) (hVz : IsOpen Vz)
    (ψ : ℂ → ℂ) (hψcont : ContinuousOn ψ Vz)
    (hψroot : ∀ z ∈ Vz, (P.map (evalIntPolyComplex z)).eval (ψ z) = 0)
    (hψVw : ∀ z ∈ Vz, ψ z ∈ Vw)
    (huniq : ∀ z ∈ Vz, ∀ w ∈ Vw, (P.map (evalIntPolyComplex z)).eval w = 0 → w = ψ z) :
    IsOpenEmbedding
      (Set.restrict {q : rootVariety P | (q : ℂ × ℂ) ∈ Vz ×ˢ Vw} (rootProj P)) := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · ext
    simp [isOpen_induced_iff]
    constructor <;> rintro ⟨t, ht, rfl⟩
    · refine ⟨{ z : ℂ | (z, ψ z) ∈ t } ∩ Vz, ?_, ?_⟩
      · have h_cont : ContinuousOn (fun z ↦ (z, ψ z)) Vz := by
          exact ContinuousOn.prodMk continuousOn_id hψcont
        exact isOpen_iff_mem_nhds.mpr fun x hx ↦
          Filter.inter_mem (h_cont.continuousAt (hVz.mem_nhds hx.2) |> fun h ↦ h.eventually (ht.mem_nhds hx.1))
            (hVz.mem_nhds hx.2)
      · grind only [rootVariety, = Set.mem_preimage, usr Set.mem_setOf_eq, = Set.mem_prod,
          = Set.restrict_apply, = Set.mem_inter_iff, rootProj]
    · refine ⟨t ×ˢ Set.univ, ht.prod isOpen_univ, ?_⟩
      ext
      rename_i x
      simp_all only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Set.restrict_apply, Set.mem_setOf_eq]
      obtain ⟨val, property⟩ := x
      obtain ⟨val, property⟩ := val
      obtain ⟨fst, snd⟩ := val
      simp_all only
      simp_all only [Set.mem_prod]
      obtain ⟨left, right⟩ := property
      rfl
  · intro q1 q2 h_eq
    grind only [usr Set.mem_setOf_eq, = Set.restrict_apply, rootVariety, rootProj, = Set.mem_prod]
  · convert hVz using 1
    ext
    simp [rootProj]
    exact ⟨fun ⟨b, hb₁, hb₂⟩ ↦ hb₁.1, fun hx ↦ ⟨ψ _, ⟨hx, hψVw _ hx⟩, hψroot _ hx⟩⟩

/-
**Local homeomorphism over a separable set.**  Over a set on which the family is
separable, every root is simple, so the implicit-function branch is a local section and the
root projection is a local homeomorphism.
-/
lemma rootProj_isLocalHomeomorphOn
    (P : Polynomial (Polynomial ℤ)) (U : Set ℂ) (hUopen : IsOpen U)
    (hsep : ∀ z ∈ U, (P.map (evalIntPolyComplex z)).Separable) :
    IsLocalHomeomorphOn (rootProj P) ((rootProj P) ⁻¹' U) := by
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro e he
  have heU : (e : ℂ × ℂ).1 ∈ U := he
  have hroot0 : (P.map (evalIntPolyComplex (e : ℂ × ℂ).1)).eval (e : ℂ × ℂ).2 = 0 := e.2
  have hsimple : (P.map (evalIntPolyComplex (e : ℂ × ℂ).1)).derivative.eval (e : ℂ × ℂ).2 ≠ 0 :=
    Polynomial.Separable.aeval_derivative_ne_zero (hsep _ heU) hroot0
  obtain ⟨ψ, hψ0, hψcd, hψroot, hψuniq⟩ :=
    complex_branch_at_simple_root_unique P (e : ℂ × ℂ).1 (e : ℂ × ℂ).2 hroot0 hsimple
  -- `ψ` is continuous near `z₀` and `ψ z₀ = w₀ ∈ Vw`; choose an open box `Vz ×ˢ Vw` in `U`
  -- on which `ψ` is a root branch, stays in `Vw`, and is the unique root (from `hψuniq`).
  set z₀ : ℂ := (e : ℂ × ℂ).1 with hz₀def
  set w₀ : ℂ := (e : ℂ × ℂ).2 with hw₀def
  have hψcont0 : ContinuousAt ψ z₀ := hψcd.continuousAt
  -- Build the properties as an eventual statement in `nhds z₀ ×ˢ nhds w₀`, then extract a box.
  obtain ⟨Vz, Vw, hVz, hVw, hz₀Vz, hw₀Vw, hbox⟩ :
      ∃ Vz Vw : Set ℂ, IsOpen Vz ∧ IsOpen Vw ∧ z₀ ∈ Vz ∧ w₀ ∈ Vw ∧
        (Vz ⊆ U) ∧ (ContinuousOn ψ Vz) ∧
        (∀ z ∈ Vz, (P.map (evalIntPolyComplex z)).eval (ψ z) = 0) ∧
        (∀ z ∈ Vz, ψ z ∈ Vw) ∧
        (∀ z ∈ Vz, ∀ w ∈ Vw, (P.map (evalIntPolyComplex z)).eval w = 0 → w = ψ z) := by
    obtain ⟨A, B, hA, hB, hAB⟩ :
        ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ z₀ ∈ A ∧ w₀ ∈ B ∧ ∀ z ∈ A, ∀ w ∈ B,
          (P.map (evalIntPolyComplex z)).eval w = 0 → ψ z = w := by
      rcases mem_nhds_prod_iff.mp hψuniq with ⟨A, B, hA, hB, hAB⟩
      exact ⟨interior A, interior hA, isOpen_interior, isOpen_interior, mem_interior_iff_mem_nhds.mpr B,
        mem_interior_iff_mem_nhds.mpr hB,
        fun z hz w hw h ↦ hAB (Set.mk_mem_prod (interior_subset hz) (interior_subset hw)) h⟩
    obtain ⟨C, hC⟩ : ∃ C : Set ℂ, IsOpen C ∧ z₀ ∈ C ∧ ∀ z ∈ C, (P.map (evalIntPolyComplex z)).eval (ψ z) = 0 :=
      Exists.imp (by tauto) (mem_nhds_iff.mp hψroot)
    obtain ⟨E, hE⟩ : ∃ E : Set ℂ, IsOpen E ∧ z₀ ∈ E ∧ ContinuousOn ψ E := by
      obtain ⟨u, hu, h⟩ := hψcd
      obtain ⟨p, hp₁, hp₂⟩ := h
      obtain ⟨E, hE₁, hE₂⟩ := mem_nhdsWithin.mp hu
      refine ⟨E, hE₁, hE₂.1, hp₁.continuousOn.mono ?_⟩
      simp_all
    obtain ⟨D, hD⟩ : ∃ D : Set ℂ, IsOpen D ∧ z₀ ∈ D ∧ ∀ z ∈ D, ψ z ∈ B :=
      Exists.imp (by tauto) (mem_nhds_iff.mp (hψcont0 (hB.mem_nhds (by simp_all))))
    use A ∩ C ∩ D ∩ E ∩ U, B
    simp_all [Set.subset_def]
    exact ⟨IsOpen.inter (IsOpen.inter (IsOpen.inter (IsOpen.inter hA hC.1) hD.1) hE.1) hUopen,
      hE.2.2.mono (by intro a a_1; simp_all only [Set.mem_inter_iff, z₀, w₀]),
      fun z hz₁ hz₂ hz₃ hz₄ hz₅ w hw₁ hw₂ ↦ hAB.2.2 z hz₁ w hw₁ hw₂ ▸ rfl⟩
  obtain ⟨hVzU, hψcontVz, hψrootVz, hψVwVz, huniqVz⟩ := hbox
  refine ⟨{q : rootVariety P | (q : ℂ × ℂ) ∈ Vz ×ˢ Vw}, ?_,
    rootProj_restrict_isOpenEmbedding P Vz Vw hVz ψ hψcontVz hψrootVz hψVwVz huniqVz⟩
  -- `e` lies in the box, which is open, hence a neighbourhood of `e`.
  have hopen : IsOpen {q : rootVariety P | (q : ℂ × ℂ) ∈ Vz ×ˢ Vw} :=
    (hVz.prod hVw).preimage continuous_subtype_val
  refine hopen.mem_nhds ?_
  exact ⟨hz₀Vz, hw₀Vw⟩

/-- **The root projection is a covering map over a separable open set.** -/
lemma rootProj_isCoveringMapOn
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic)
    (U : Set ℂ) (hUopen : IsOpen U)
    (hsep : ∀ z ∈ U, (P.map (evalIntPolyComplex z)).Separable) :
    IsCoveringMapOn (rootProj P) U := by
  refine (rootProj_isClosedMap P hP).isCoveringMapOn_of_openPartialHomeomorph
    (fun x _ ↦ rootProj_finite_fiber P hP x) ?_
  intro e he
  obtain ⟨φ, hφsrc, hφeq⟩ := rootProj_isLocalHomeomorphOn P U hUopen hsep e he
  exact ⟨φ, hφsrc, hφeq.symm⟩

/-
**Holomorphic root branch on a convex separable domain.**

Let `U ⊆ ℂ` be open and convex, and suppose the complex family
`P.map (evalIntPolyComplex z)` is separable for every `z ∈ U`.  Then any root `w₀` of the
family at a base point `z₀ ∈ U` extends to a single holomorphic function `H : ℂ → ℂ` that is
a root of the family throughout `U`, with `H z₀ = w₀`.

This is the covering-space / monodromy core of the holomorphic continuation of an algebraic
branch: on a simply connected domain with no branch points the algebraic function is
single-valued and holomorphic.
-/
lemma complex_branch_holomorphic_on_convex
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic)
    (U : Set ℂ) (hUconv : Convex ℝ U) (hUopen : IsOpen U)
    (z₀ w₀ : ℂ) (hz₀ : z₀ ∈ U)
    (hw₀ : (P.map (evalIntPolyComplex z₀)).eval w₀ = 0)
    (hsep : ∀ z ∈ U, (P.map (evalIntPolyComplex z)).Separable) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧ H z₀ = w₀ ∧
      (∀ z ∈ U, (P.map (evalIntPolyComplex z)).eval (H z) = 0) := by
  obtain ⟨F, hF⟩ : ∃ F : U → ↥((rootProj P) ⁻¹' U), Continuous F ∧ F ⟨z₀, hz₀⟩ = ⟨⟨(z₀, w₀), hw₀⟩, hz₀⟩ ∧
      ∀ a : U, (U.restrictPreimage (rootProj P)) (F a) = a := by
    have cov : IsCoveringMap (U.restrictPreimage (rootProj P)) :=
      (rootProj_isCoveringMapOn P hP U hUopen hsep).isCoveringMap_restrictPreimage
    have h_unique_lift : ∃! F : C(U, ↥((rootProj P) ⁻¹' U)), F ⟨z₀, hz₀⟩ = ⟨⟨(z₀, w₀), hw₀⟩, hz₀⟩ ∧
        (U.restrictPreimage (rootProj P)) ∘ F = ContinuousMap.id U := by
      apply_rules [cov.existsUnique_continuousMap_lifts]
      · have h_contractible : ContractibleSpace U := by
          convert hUconv.contractibleSpace ⟨z₀, hz₀⟩
        infer_instance
      · exact hUopen.locPathConnectedSpace
    exact ⟨h_unique_lift.exists.choose, h_unique_lift.exists.choose.2,
      h_unique_lift.exists.choose_spec.1, fun a ↦ congr_fun h_unique_lift.exists.choose_spec.2 a⟩
  obtain ⟨H, hH⟩ : ∃ H : U → ℂ, Continuous H ∧ H ⟨z₀, hz₀⟩ = w₀ ∧ ∀ z : U,
      (P.map (evalIntPolyComplex z)).eval (H z) = 0 := by
    refine ⟨fun z ↦ (F z |>.1 |>.1 |>.2), ?_, ?_, ?_⟩ <;> simp_all
    · exact continuous_subtype_val.comp (continuous_subtype_val.comp hF.1) |> Continuous.snd
    · intro a ha
      specialize hF
      have := hF.2.2 a ha
      simp_all [Subtype.ext_iff, rootProj]
      grind only [rootVariety, usr Set.mem_setOf_eq]
  convert DorgeBauer.continuous_root_holomorphic P U hUopen
    (fun z ↦ if hz : z ∈ U then H ⟨z, hz⟩ else 0) ?_ ?_ ?_ using 1
  any_goals tauto
  any_goals
    intro z
    exact Classical.propDecidable (z ∈ U)
  · constructor <;> intro h
    · convert DorgeBauer.continuous_root_holomorphic P U hUopen
        (fun z ↦ if hz : z ∈ U then H ⟨z, hz⟩ else 0) ?_ ?_ ?_ using 1
      · rw [continuousOn_iff_continuous_restrict]
        convert hH.1 using 1
        ext ⟨z, hz⟩
        simp [hz]
      · grind
      · exact hsep
    · exact ⟨_, h, by simpa [hz₀] using hH.2.1, fun z hz ↦ by simpa [hz] using hH.2.2 ⟨z, hz⟩⟩
  · rw [continuousOn_iff_continuous_restrict]
    convert hH.1 using 1
    ext ⟨z, hz⟩
    simp_all
  · simp_all

/-!
### Packaging the continuation in tail-ball form

We combine `complex_branch_holomorphic_on_convex` with a "no branch switching" argument on
the real axis to obtain the holomorphic continuation of a real algebraic branch in exactly
the form used by `DorgeBauer.real_branch_full_holomorphic_continuation`: a single `H`,
holomorphic on all the right-half tail balls, that agrees with `g` on the real ray.
-/

/-
**No branch switching on the real ray.**  If `H` is a complex root branch that is
continuous at each real `y ≥ a`, `g` is a continuous real root branch on `[a, ∞)`, the
complex family is separable at each real `y ≥ a`, and `H` and `g` agree at the base point
`a`, then they agree along the whole real ray.  (Both are continuous root selections of a
family with simple, hence isolated and non-colliding, roots; the agreement set is clopen in
the connected ray.)
-/
lemma branch_agrees_on_real_ray
    (P : Polynomial (Polynomial ℤ)) (a : ℝ) (g : ℝ → ℝ) (H : ℂ → ℂ)
    (hgc : ContinuousOn g (Set.Ici a))
    (hHc : ∀ y : ℝ, a ≤ y → ContinuousAt H (y : ℂ))
    (hgroot : ∀ y : ℝ, a ≤ y → (P.map (evalIntPolyReal y)).eval (g y) = 0)
    (hHroot : ∀ y : ℝ, a ≤ y → (P.map (evalIntPolyComplex (y : ℂ))).eval (H (y : ℂ)) = 0)
    (hsep : ∀ y : ℝ, a ≤ y → (P.map (evalIntPolyComplex (y : ℂ))).Separable)
    (hbase : H (a : ℂ) = (g a : ℂ)) :
    ∀ y : ℝ, a ≤ y → H (y : ℂ) = (g y : ℂ) := by
  -- Let `A := {y : ℝ | H y = g y}`.
  set A : Set ℝ := {y : ℝ | H y = g y}
  -- We show `A ∩ [a, ∞)` is both relatively open and relatively closed in `[a, ∞)`.
  have h_rel_open : ∀ y ∈ A ∩ Set.Ici a, ∃ ε > 0, ∀ z ∈ Set.Ici a, |z - y| < ε → z ∈ A := by
    intro y hy
    obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ℂ, w₀ = H y ∧ (P.map (evalIntPolyComplex y)).eval w₀ = 0 ∧
        (P.map (evalIntPolyComplex y)).derivative.eval w₀ ≠ 0 := by
      have := hsep y hy.2
      refine ⟨_, rfl, hHroot y hy.2, ?_⟩
      simpa using Polynomial.Separable.aeval_derivative_ne_zero this (hHroot y hy.2)
    obtain ⟨φ, hφ⟩ := complex_branch_at_simple_root_unique P y w₀ hw₀.right.left hw₀.right.right
    have h_cont : Filter.Tendsto (fun z : ℝ ↦ (z : ℂ)) (nhdsWithin y (Set.Ici a)) (nhds y) ∧
        Filter.Tendsto (fun z : ℝ ↦ H z) (nhdsWithin y (Set.Ici a)) (nhds w₀) ∧
        Filter.Tendsto (fun z : ℝ ↦ (g z : ℂ)) (nhdsWithin y (Set.Ici a)) (nhds w₀) := by
      refine ⟨?_, ?_, ?_⟩
      · exact Complex.continuous_ofReal.continuousWithinAt
      · apply tendsto_nhdsWithin_of_tendsto_nhds
        simpa [hw₀.1] using
          hHc y hy.2 |> ContinuousAt.tendsto |> Filter.Tendsto.comp <| Complex.continuous_ofReal.tendsto y
      · convert Complex.continuous_ofReal.continuousAt.tendsto.comp (hgc.continuousWithinAt hy.2) using 1
        simp_all only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ici, Polynomial.derivative_map, ne_eq, A]
    have h_cont : ∀ᶠ z : ℝ in nhdsWithin y (Set.Ici a), φ (z : ℂ) = H z ∧ φ (z : ℂ) = (g z : ℂ) := by
      have h_cont : ∀ᶠ z : ℝ in nhdsWithin y (Set.Ici a),
          (P.map (evalIntPolyComplex (z : ℂ))).eval (H z) = 0 ∧
            (P.map (evalIntPolyComplex (z : ℂ))).eval ((g z : ℂ)) = 0 := by
        filter_upwards [self_mem_nhdsWithin] with z hz using
          ⟨hHroot z hz, by simpa [evalIntPolyComplex_ofReal] using hgroot z hz⟩
      have := hφ.2.2.2
      simp_all [Metric.eventually_nhds_iff]
      have := hφ.2.2.2
      rcases this with ⟨ε, ε_pos, hε⟩
      simp_all [Prod.dist_eq]
      have h_cont : ∀ᶠ z : ℝ in nhdsWithin y (Set.Ici a),
          dist (z : ℂ) y < ε ∧ dist (H z) (H y) < ε ∧ dist ((g z : ℂ)) (H y) < ε := by
        have hT :
            Tendsto (fun z : ℝ ↦ (z : ℂ)) (𝓝[Set.Ici a] y) (𝓝 (y : ℂ)) ∧
              Tendsto (fun z : ℝ ↦ H (z : ℂ)) (𝓝[Set.Ici a] y) (𝓝 (H (y : ℂ))) ∧
              Tendsto (fun z : ℝ ↦ (g z : ℂ)) (𝓝[Set.Ici a] y) (𝓝 (H (y : ℂ))) := ‹_›
        exact Filter.eventually_and.mpr ⟨hT.1.eventually (Metric.ball_mem_nhds _ ε_pos),
          Filter.eventually_and.mpr ⟨hT.2.1.eventually (Metric.ball_mem_nhds _ ε_pos),
            hT.2.2.eventually (Metric.ball_mem_nhds _ ε_pos)⟩⟩
      have hev :
          (∀ᶠ x : ℝ in 𝓝[Set.Ici a] y, Polynomial.eval (H x) (Polynomial.map (evalIntPolyComplex x) P) = 0) ∧
            ∀ᶠ x : ℝ in 𝓝[Set.Ici a] y, Polynomial.eval (g x : ℂ) (Polynomial.map (evalIntPolyComplex x) P) = 0 := ‹_›
      refine ⟨?_, ?_⟩
      · filter_upwards [h_cont, hev.1] with x hx₁ hx₂ using hε _ _ hx₁.1 hx₁.2.1 hx₂
      · filter_upwards [h_cont, hev.2] with x hx₁ hx₂ using hε _ _ hx₁.1 hx₁.2.2 hx₂
    rw [eventually_nhdsWithin_iff] at h_cont
    rw [Metric.eventually_nhds_iff] at h_cont
    obtain ⟨ε, ε_pos, hε⟩ := h_cont
    refine ⟨ε, ε_pos, fun z hz hz' ↦ ?_⟩
    have := hε hz' hz
    simp_all only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ici, Polynomial.derivative_map, ne_eq, dist_self,
      true_and, gt_iff_lt, A]
    obtain ⟨left, right⟩ := hy
    obtain ⟨left_1, right_1⟩ := hw₀
    obtain ⟨left_2, right_2⟩ := hφ
    obtain ⟨left_3, right_3⟩ := h_cont
    obtain ⟨left_4, right_4⟩ := this
    obtain ⟨left_5, right_1⟩ := right_1
    obtain ⟨left_6, right_2⟩ := right_2
    obtain ⟨left_7, right_3⟩ := right_3
    subst left_1
    simp_all only
  -- We show `A ∩ [a, ∞)` is relatively closed in `[a, ∞)`.
  have h_rel_closed : IsClosed {y : ℝ | y ∈ Set.Ici a ∧ H y = g y} := by
    have h_cont : ContinuousOn (fun y : ℝ ↦ H y - g y) (Set.Ici a) := by
      apply ContinuousOn.sub
      · exact continuousOn_of_forall_continuousAt fun y hy ↦
          ContinuousAt.comp (hHc y hy) (Complex.continuous_ofReal.continuousAt)
      · exact Complex.continuous_ofReal.comp_continuousOn hgc
    have h_rel_closed : IsClosed {y : ℝ | y ∈ Set.Ici a ∧ (H y - g y) = 0} :=
      h_cont.preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
    simpa only [sub_eq_zero] using h_rel_closed
  -- Since `A ∩ [a, ∞)` is clopen in `[a, ∞)` and `a ∈ A`, it equals `[a, ∞)`.
  have h_eq : {y : ℝ | y ∈ Set.Ici a ∧ H y = g y} = Set.Ici a := by
    apply_rules [IsClopen.eq_univ]
    ext y
    refine ⟨fun hy ↦ hy.left, fun hy ↦ ⟨hy, ?_⟩⟩
    contrapose! h_rel_open
    obtain ⟨z, hz⟩ : ∃ z ∈ Set.Icc a y, z ∈ A ∧ ∀ w ∈ Set.Icc a y, w ∈ A → w ≤ z := by
      have h_compact : IsCompact {z ∈ Set.Icc a y | z ∈ A} := by
        have h_compact : IsCompact {z ∈ Set.Icc a y | z ∈ Set.Ici a ∧ H z = g z} :=
          CompactIccSpace.isCompact_Icc.inter_right h_rel_closed
        grind +splitIndPred
      obtain ⟨x, hx⟩ := h_compact.exists_isGreatest ⟨a, ⟨by linarith, by linarith⟩, by trivial⟩
      exact ⟨x, hx.1.1, hx.1.2, fun w hw hw' ↦ hx.2 ⟨hw, hw'⟩⟩
    use z
    simp at *
    refine ⟨⟨hz.2.1, hz.1.1⟩, fun ε ε_pos ↦ ?_⟩
    by_cases hz_eq_y : z = y
    · grind
    · -- Since `z ≠ y`, choose `z₁ ∈ (z, y)` with `|z₁ - z| < ε`.
      obtain ⟨z_1, hz_1⟩ : ∃ z_1 ∈ Set.Ioo z y, |z_1 - z| < ε := by
        by_cases hz_lt_y : z < y
        · by_cases hε : ε < y - z
          · exact ⟨z + ε / 2, ⟨by linarith, by linarith⟩, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
          · exact ⟨(z + y) / 2, ⟨by linarith, by linarith⟩, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
        · exact False.elim <| hz_eq_y <| le_antisymm hz.1.2 <| not_lt.mp hz_lt_y
      grind +splitImp
  exact fun y hy ↦ h_eq.symm.subset hy |>.2

/-
**Holomorphic continuation of a real branch onto the right-half tail balls.** -/
lemma real_branch_holo_continuation_tail
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic)
    (T₀ : ℤ) (g : ℝ → ℝ) (B : ℝ)
    (hgc : ContinuousOn g (Set.Ici (T₀ : ℝ)))
    (hroot : ∀ x : ℝ, (T₀ : ℝ) ≤ x → (P.map (evalIntPolyReal x)).eval (g x) = 0)
    (hsep : ∀ z : ℂ, B < ‖z‖ → (P.map (evalIntPolyComplex z)).Separable) :
    ∃ (T : ℝ) (H : ℂ → ℂ),
      (2 * (T₀ : ℝ)) ≤ T ∧ (2 : ℝ) ≤ T ∧
      (∀ x : ℝ, T ≤ x → DiffContOnCl ℂ H (Metric.ball (x : ℂ) (x / 2))) ∧
      (∀ y : ℝ, T / 2 ≤ y → H (y : ℂ) = (g y : ℂ)) := by
  -- Let `U := {z : ℂ | B < z.re}`, which is open (`isOpen_lt continuous_const Complex.continuous_re`) and convex (`convex_halfSpace_re_gt B`). For any `z ∈ U`, `B < z.re ≤ ‖z‖`, so `hsep` gives separability of the complex family on `U`.
  set U : Set ℂ := {z : ℂ | B < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconvex : Convex ℝ U := convex_halfSpace_re_gt B
  have hUsep : ∀ z ∈ U, (P.map (evalIntPolyComplex z)).Separable :=
    fun z hz ↦ hsep z <| lt_of_lt_of_le hz <| Complex.re_le_norm z
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧
      H ((max (max (2*(T₀:ℝ)) 2) (2*B+1)) / 2 : ℂ) = (g ((max (max (2*(T₀:ℝ)) 2) (2*B+1)) / 2 : ℝ) : ℂ) ∧
      (∀ z ∈ U, (P.map (evalIntPolyComplex z)).eval (H z) = 0) := by
    apply_rules [complex_branch_holomorphic_on_convex]
    · simp +zetaDelta at *
      linarith [le_max_left (max (2 * (T₀ : ℝ)) 2) (2 * B + 1),
        le_max_right (max (2 * (T₀ : ℝ)) 2) (2 * B + 1), le_max_left (2 * (T₀ : ℝ)) 2,
        le_max_right (2 * (T₀ : ℝ)) 2]
    · convert hroot (max (max (2 * T₀ : ℝ) 2) (2 * B + 1) / 2) _ using 1
      · convert evalIntPolyComplex_ofReal P (max (max (2 * T₀ : ℝ) 2) (2 * B + 1) / 2)
          (g (max (max (2 * T₀ : ℝ) 2) (2 * B + 1) / 2)) using 1
        norm_num [Complex.ext_iff]
        grind +qlia
      · linarith [le_max_left (max (2 * T₀ : ℝ) 2) (2 * B + 1),
          le_max_right (max (2 * T₀ : ℝ) 2) (2 * B + 1), le_max_left (2 * T₀ : ℝ) 2,
          le_max_right (2 * T₀ : ℝ) 2]
  refine ⟨max (max (2 * T₀) 2) (2 * B + 1), H, ?_, ?_, ?_, ?_⟩ <;> norm_num at *
  · intro x hx₁ hx₂ hx₃
    refine ⟨?_, ?_⟩
    · apply hH.1.mono
      intro z hz
      rw [Metric.mem_ball] at hz
      rw [dist_eq_norm] at hz
      norm_num [Complex.normSq, Complex.norm_def] at *
      show B < z.re
      rw [Real.sqrt_lt' (by linarith)] at hz
      nlinarith [sq_nonneg (z.re - x), sq_nonneg z.im]
    · apply hH.1.continuousOn.mono
      rw [closure_ball _ (by positivity)]
      intro z hz
      rw [Metric.mem_closedBall] at hz
      rw [dist_eq_norm] at hz
      norm_num [Complex.normSq, Complex.norm_def] at hz ⊢
      show B < z.re
      nlinarith [Real.sqrt_le_iff.mp hz]
  · apply branch_agrees_on_real_ray P ((max (max (2*(T₀:ℝ)) 2) (2*B+1)) / 2) g H
    · exact hgc.mono (Set.Ici_subset_Ici.mpr <| by
        cases max_cases (max (2 * (T₀ : ℝ)) 2) (2 * B + 1) <;> cases max_cases (2 * (T₀ : ℝ)) 2 <;> linarith)
    · intro y hy
      have hre : B < (y : ℂ).re := by
        norm_num
        cases max_cases (max (2 * (T₀ : ℝ)) 2) (2 * B + 1) <;> cases max_cases (2 * (T₀ : ℝ)) 2 <;>
          linarith
      exact (hH.1.differentiableAt (hUopen.mem_nhds hre)).continuousAt
    · intro y hy
      refine hroot y ?_
      cases max_cases (max (2 * (T₀ : ℝ)) 2) (2 * B + 1) <;> cases max_cases (2 * (T₀ : ℝ)) 2 <;> linarith
    · intro y hy
      refine hH.2.2 _ ?_
      show B < (y : ℂ).re
      norm_num
      linarith [le_max_left (max (2 * (T₀ : ℝ)) 2) (2 * B + 1),
        le_max_right (max (2 * (T₀ : ℝ)) 2) (2 * B + 1), le_max_left (2 * (T₀ : ℝ)) 2,
        le_max_right (2 * (T₀ : ℝ)) 2]
    · intro y hy
      specialize hsep y
      simp_all
      have := le_max_left (max (2 * (T₀ : ℝ)) 2) (2 * B + 1)
      have := le_max_right (max (2 * (T₀ : ℝ)) 2) (2 * B + 1)
      have := le_max_left (2 * (T₀ : ℝ)) 2
      have := le_max_right (2 * (T₀ : ℝ)) 2
      refine hsep ?_
      cases abs_cases y <;> linarith
    · simp_all

end DorgeBauer
