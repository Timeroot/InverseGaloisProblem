/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.DorgeBauer

/-!
# The root variety of a complex family of monic polynomials is a covering space

An algebraic function is a covering space of its base away from the branch points.  This file
proves that in the form the analytification of a cover of the line needs it: for a monic
two-variable complex polynomial `P ∈ ℂ[X][Y]`, the set of pairs `(z, w)` with `P(z, w) = 0`
projects to the `z`-plane, and over any open set on which the specialization `P(z, ·)` is
separable that projection is a covering map.

Three facts combine.  The projection is *closed*: the roots of a monic polynomial are bounded by
its coefficients, so nothing escapes to infinity over a compact set and the projection is proper.
Its *fibres are finite*, being root sets of a nonzero polynomial.  And it is a *local
homeomorphism* over the separable locus: at a simple root the derivative in the `Y`-direction is
invertible, so the inverse function theorem applied to `(z, w) ↦ (z, P(z, w))` straightens the
variety.  A closed map with finite fibres that is a local homeomorphism is a covering map.

## Main results

* `Rigidity.RET.Analytic.isClosedMap_rootProj` — the root projection is a closed map.
* `Rigidity.RET.Analytic.isLocalHomeomorphOn_rootProj` — it is a local homeomorphism over the
  separable locus.
* `Rigidity.RET.Analytic.isCoveringMapOn_rootProj` — it is a covering map over any set on which
  the family is separable.
-/

open Polynomial Topology Filter

noncomputable section

namespace Rigidity.RET.Analytic

/-! ### The complex root variety -/

/-- The specialization of a two-variable complex polynomial at a value of the first variable. -/
def spec (P : Polynomial (Polynomial ℂ)) (z : ℂ) : Polynomial ℂ :=
  P.map (Polynomial.evalRingHom z)

/-- The two-variable evaluation of a polynomial in `ℂ[X][Y]`. -/
def biEval (P : Polynomial (Polynomial ℂ)) (p : ℂ × ℂ) : ℂ := (spec P p.1).eval p.2

/-- The complex root variety of a two-variable polynomial. -/
def rootVariety (P : Polynomial (Polynomial ℂ)) : Set (ℂ × ℂ) := {p | biEval P p = 0}

/-- The projection of the root variety onto the plane of the first variable. -/
def rootProj (P : Polynomial (Polynomial ℂ)) : rootVariety P → ℂ := fun q ↦ (q : ℂ × ℂ).1

theorem mem_rootVariety {P : Polynomial (Polynomial ℂ)} {p : ℂ × ℂ} :
    p ∈ rootVariety P ↔ (spec P p.1).eval p.2 = 0 := Iff.rfl

theorem spec_monic {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) (z : ℂ) : (spec P z).Monic :=
  hP.map _

theorem natDegree_spec {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) (z : ℂ) :
    (spec P z).natDegree = P.natDegree :=
  hP.natDegree_map _

/-! ### Smoothness of the two-variable evaluation -/

/-- **The two-variable evaluation is holomorphic**, being a polynomial expression in the two
coordinates. -/
theorem contDiff_biEval (P : Polynomial (Polynomial ℂ)) : ContDiff ℂ ⊤ (biEval P) := by
  have hrw : biEval P = fun p : ℂ × ℂ ↦
      ∑ i ∈ Finset.range (P.natDegree + 1),
        (∑ j ∈ Finset.range ((P.coeff i).natDegree + 1), (P.coeff i).coeff j * p.1 ^ j) *
          p.2 ^ i := by
    funext p
    simp only [biEval, spec, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range,
      Polynomial.coe_evalRingHom]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Polynomial.eval_eq_sum_range]
  rw [hrw]
  exact ContDiff.sum fun i _ ↦ ContDiff.mul
    (ContDiff.sum fun j _ ↦ contDiff_const.mul (contDiff_fst.pow j)) (contDiff_snd.pow i)

theorem continuous_biEval (P : Polynomial (Polynomial ℂ)) : Continuous (biEval P) :=
  (contDiff_biEval P).continuous

theorem continuous_rootProj (P : Polynomial (Polynomial ℂ)) : Continuous (rootProj P) :=
  continuous_fst.comp continuous_subtype_val

/-! ### Finite fibres -/

/-- **The root projection has finite fibres**: a fibre injects into the root set of a nonzero
polynomial. -/
theorem finite_fiber {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) (x : ℂ) :
    ((rootProj P) ⁻¹' {x}).Finite := by
  have hne : spec P x ≠ 0 := (spec_monic hP x).ne_zero
  refine Set.Finite.of_finite_image (f := fun q : rootVariety P ↦ (q : ℂ × ℂ).2) ?_ ?_
  · refine Set.Finite.subset (spec P x).roots.toFinset.finite_toSet ?_
    rintro y ⟨q, hq, rfl⟩
    have hx : (q : ℂ × ℂ).1 = x := hq
    have hroot : (spec P x).eval (q : ℂ × ℂ).2 = 0 := by
      have := q.2
      rwa [mem_rootVariety, hx] at this
    simp only [Multiset.mem_toFinset, Finset.mem_coe, Polynomial.mem_roots hne]
    exact hroot
  · rintro q hq q' hq' h
    exact Subtype.ext (Prod.ext (hq.trans hq'.symm) h)

/-! ### Properness -/

/-- **The root projection is a closed map.**  Over a compact set of the base the roots stay
bounded, by Cauchy's root bound applied to the monic specializations, so the projection is
proper. -/
theorem isClosedMap_rootProj {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) :
    IsClosedMap (rootProj P) := by
  refine IsProperMap.isClosedMap (isProperMap_iff_isCompact_preimage.mpr
    ⟨continuous_rootProj P, fun K hK ↦ ?_⟩)
  rw [Topology.IsEmbedding.isCompact_iff (f := (Subtype.val : rootVariety P → ℂ × ℂ))
    Topology.IsEmbedding.subtypeVal]
  have himg : (Subtype.val : rootVariety P → ℂ × ℂ) '' (rootProj P ⁻¹' K)
      = {p : ℂ × ℂ | p.1 ∈ K ∧ biEval P p = 0} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq, q.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨p, h2⟩, h1, rfl⟩
  rw [himg]
  -- the coefficient bound
  set g : ℂ → ℝ := fun z ↦ 1 + ∑ i ∈ Finset.range P.natDegree, ‖(P.coeff i).eval z‖ with hg
  have hgc : Continuous g :=
    continuous_const.add (continuous_finset_sum _ fun i _ ↦ (Polynomial.continuous _).norm)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hgc.continuousOn
  have hbound : ∀ p : ℂ × ℂ, p.1 ∈ K → biEval P p = 0 → ‖p.2‖ ≤ M := by
    rintro ⟨z, w⟩ hz hw
    have hroot : (spec P z).IsRoot w := hw
    have hcb := cauchy_root_bound (spec_monic hP z) hroot
    rw [natDegree_spec hP z] at hcb
    have hcoeff : ∀ i, (spec P z).coeff i = (P.coeff i).eval z := by
      intro i; simp [spec, Polynomial.coeff_map]
    simp only [hcoeff] at hcb
    exact hcb.trans ((le_abs_self _).trans (hM z hz))
  refine IsCompact.of_isClosed_subset (hK.prod (isCompact_closedBall (0 : ℂ) M)) ?_ ?_
  · exact (hK.isClosed.preimage continuous_fst).inter
      (isClosed_eq (continuous_biEval P) continuous_const)
  · rintro p ⟨h1, h2⟩
    exact ⟨h1, mem_closedBall_zero_iff.mpr (hbound p h1 h2)⟩

/-! ### The straightening chart -/

/-- **The graph map of a family straightens the root variety near a simple root.**  The map
`(z, w) ↦ (z, P(z, w))` has derivative `(a, b) ↦ (a, D(a, b))` at a point, and the `Y`-derivative
of `P` is the coefficient of `b`; at a simple root it is nonzero, so that linear map is invertible
and the inverse function theorem applies.  The chart inverse is again differentiable at the image
point, which is what makes the local branches of the roots holomorphic. -/
theorem exists_graphChart (P : Polynomial (Polynomial ℂ)) {z₀ w₀ : ℂ}
    (hsimple : (spec P z₀).derivative.eval w₀ ≠ 0) :
    ∃ φ : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ), ((z₀, w₀) : ℂ × ℂ) ∈ φ.source ∧
      ⇑φ = (fun p : ℂ × ℂ ↦ (p.1, biEval P p)) ∧
      DifferentiableAt ℂ (⇑φ.symm) (z₀, biEval P (z₀, w₀)) := by
  -- the derivative of the family, kept abstract
  obtain ⟨D, hF⟩ : ∃ D : (ℂ × ℂ) →L[ℂ] ℂ, HasStrictFDerivAt (biEval P) D (z₀, w₀) :=
    ⟨_, (contDiff_biEval P).hasStrictFDerivAt (by simp)⟩
  have hDsplit : ∀ a b : ℂ, D (a, b) = D (a, 0) + b * D (0, 1) := by
    intro a b
    have hab : ((a, b) : ℂ × ℂ) = (a, 0) + b • ((0, 1) : ℂ × ℂ) := by
      simp
    rw [hab, map_add, map_smul, smul_eq_mul]
  have hβ : D (0, 1) = (spec P z₀).derivative.eval w₀ := by
    have hcomp : HasFDerivAt (fun w : ℂ ↦ ((z₀, w) : ℂ × ℂ))
        ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)) w₀ :=
      (hasFDerivAt_const z₀ w₀).prodMk (hasFDerivAt_id w₀)
    have h1 : HasDerivAt (fun w : ℂ ↦ biEval P (z₀, w)) (D (0, 1)) w₀ := by
      simpa using (hF.hasFDerivAt.comp w₀ hcomp).hasDerivAt
    exact h1.unique ((spec P z₀).hasDerivAt w₀)
  have hβne : D (0, 1) ≠ 0 := hβ ▸ hsimple
  -- the derivative of `(z, w) ↦ (z, P (z, w))` as a linear equivalence
  set Lf : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := (ContinuousLinearMap.fst ℂ ℂ ℂ).prod D with hLfdef
  set Lg : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
      ((D (0, 1))⁻¹ • ((ContinuousLinearMap.snd ℂ ℂ ℂ) -
        (D.comp (ContinuousLinearMap.inl ℂ ℂ ℂ)).comp (ContinuousLinearMap.fst ℂ ℂ ℂ))) with hLgdef
  have hLfapp : ∀ p : ℂ × ℂ, Lf p = (p.1, D p) := fun _ ↦ rfl
  have hLgapp : ∀ p : ℂ × ℂ, Lg p = (p.1, (D (0, 1))⁻¹ * (p.2 - D (p.1, 0))) := by
    intro p
    simp [hLgdef, smul_eq_mul]
  have hleft : Function.LeftInverse Lg Lf := by
    rintro ⟨a, b⟩
    rw [hLfapp, hLgapp]
    refine Prod.ext rfl ?_
    simp only [hDsplit a b]
    field_simp
    ring
  have hright : Function.RightInverse Lg Lf := by
    rintro ⟨u, v⟩
    rw [hLgapp, hLfapp]
    refine Prod.ext rfl ?_
    simp only [hDsplit u ((D (0, 1))⁻¹ * (v - D (u, 0)))]
    field_simp
    ring
  set L : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := ContinuousLinearEquiv.equivOfInverse Lf Lg hleft hright with hLdef
  set G : ℂ × ℂ → ℂ × ℂ := fun p ↦ (p.1, biEval P p) with hGdef
  have hG : HasStrictFDerivAt G (L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (z₀, w₀) := by
    have : (L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) = Lf := rfl
    rw [this, hLfdef]
    exact hasStrictFDerivAt_fst.prodMk hF
  refine ⟨hG.toOpenPartialHomeomorph G, hG.mem_toOpenPartialHomeomorph_source,
    hG.toOpenPartialHomeomorph_coe, ?_⟩
  exact hG.to_localInverse.differentiableAt

/-! ### The local homeomorphism -/

/-- **The root projection is a local homeomorphism over the separable locus.**  The straightening
chart carries the root variety onto a horizontal slice of the plane, and the projection is the
resulting chart of the variety. -/
theorem isLocalHomeomorphOn_rootProj (P : Polynomial (Polynomial ℂ)) {U : Set ℂ}
    (hsep : ∀ z ∈ U, (spec P z).Separable) :
    IsLocalHomeomorphOn (rootProj P) (rootProj P ⁻¹' U) := by
  rintro ⟨⟨z₀, w₀⟩, hmem⟩ he
  have hzU : z₀ ∈ U := he
  have hroot : (spec P z₀).eval w₀ = 0 := hmem
  have hsimple : (spec P z₀).derivative.eval w₀ ≠ 0 :=
    Polynomial.Separable.aeval_derivative_ne_zero (hsep z₀ hzU) hroot
  obtain ⟨φ, hφsrc, hφcoe, -⟩ := exists_graphChart P hsimple
  have hGroot : ∀ q : rootVariety P, φ (q : ℂ × ℂ) = ((q : ℂ × ℂ).1, 0) := by
    intro q
    rw [hφcoe]
    exact Prod.ext rfl q.2
  have hsymm : ∀ z : ℂ, ((z, (0 : ℂ)) : ℂ × ℂ) ∈ φ.target →
      biEval P (φ.symm (z, 0)) = 0 ∧ (φ.symm (z, 0)).1 = z := by
    intro z hz
    have h := φ.right_inv hz
    rw [hφcoe] at h
    exact ⟨(Prod.ext_iff.mp h).2, (Prod.ext_iff.mp h).1⟩
  refine ⟨{ toFun := rootProj P
            invFun := fun z ↦ if h : biEval P (φ.symm (z, 0)) = 0 then ⟨φ.symm (z, 0), h⟩
              else ⟨(z₀, w₀), hmem⟩
            source := {q : rootVariety P | (q : ℂ × ℂ) ∈ φ.source}
            target := {z : ℂ | ((z, (0 : ℂ)) : ℂ × ℂ) ∈ φ.target}
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := (φ.open_source.preimage continuous_subtype_val)
            open_target := φ.open_target.preimage (by fun_prop)
            continuousOn_toFun := (continuous_rootProj P).continuousOn
            continuousOn_invFun := ?_ }, hφsrc, rfl⟩
  · intro q hq
    have h := φ.map_source hq
    rwa [hGroot q] at h
  · intro z hz
    obtain ⟨h0, _⟩ := hsymm z hz
    simp only [dif_pos h0]
    exact φ.map_target hz
  · intro q hq
    have h := φ.left_inv hq
    rw [hGroot q] at h
    have h0 : biEval P (φ.symm ((rootProj P q), 0)) = 0 := by
      rw [show ((rootProj P q : ℂ), (0 : ℂ)) = ((q : ℂ × ℂ).1, (0 : ℂ)) from rfl, h]
      exact q.2
    simp only [dif_pos h0]
    exact Subtype.ext h
  · intro z hz
    obtain ⟨h0, h1⟩ := hsymm z hz
    simp only [dif_pos h0]
    exact h1
  · rw [Topology.IsEmbedding.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr (f := fun z : ℂ ↦ φ.symm (z, 0)) ?_ ?_
    · exact φ.continuousOn_symm.comp (by fun_prop) fun z hz ↦ hz
    · intro z hz
      obtain ⟨h0, _⟩ := hsymm z hz
      simp only [Function.comp_apply, dif_pos h0]

/-! ### The covering map -/

/-- **The root projection of a monic family is a covering map over any separable set.** -/
theorem isCoveringMapOn_rootProj {P : Polynomial (Polynomial ℂ)} (hP : P.Monic) {U : Set ℂ}
    (hsep : ∀ z ∈ U, (spec P z).Separable) :
    IsCoveringMapOn (rootProj P) U := by
  have hfin : ∀ x ∈ U, ((rootProj P) ⁻¹' {x}).Finite := fun x _ ↦ finite_fiber hP x
  have hloc : ∀ e ∈ rootProj P ⁻¹' U,
      ∃ ψ : OpenPartialHomeomorph (rootVariety P) ℂ, e ∈ ψ.source ∧ ⇑ψ = rootProj P := by
    intro e he
    obtain ⟨ψ, hψsrc, hψeq⟩ := isLocalHomeomorphOn_rootProj P hsep e he
    exact ⟨ψ, hψsrc, hψeq.symm⟩
  exact (isClosedMap_rootProj hP).isCoveringMapOn_of_openPartialHomeomorph hfin hloc

end Rigidity.RET.Analytic

end
