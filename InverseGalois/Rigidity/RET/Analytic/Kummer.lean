/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootBranch
import InverseGalois.Rigidity.RET.Analytic.Separating

/-!
# The power covering, and the correspondence on it

The `n`-th power map of the punctured plane is a covering of the plane punctured at the origin, and
its deck group is the group of `n`-th roots of unity.  The coordinate of the total space is a
holomorphic function of moderate growth on it — holomorphic because a continuous branch of a root
is, of moderate growth because the coordinate is the `n`-th root of the base coordinate — and it
takes distinct values at the points of every fibre.

That is the separating function the Galois correspondence for a covering asks for, so the
correspondence applies to this covering and produces a Galois extension of the rational functions
of the base coordinate whose group is the group of `n`-th roots of unity: the Kummer extension,
obtained from the topology of the covering rather than from the equation `yⁿ = T`.

## Main definitions

* `Rigidity.RET.kummerProj` — the projection of the power covering, as a map to the plane.

## Main results

* `Rigidity.RET.isLocalHomeomorph_kummerProj`, `Rigidity.RET.range_kummerProj` — the power map is a
  covering of the plane punctured at the origin.
* `Rigidity.RET.hasSeparatingFunction_kummer` — the coordinate separates the points of a fibre.
* `Rigidity.RET.exists_isGalois_ratFunc_rootsOfUnity` — the rational functions of the base
  coordinate have a Galois extension of degree `n` with the `n`-th roots of unity as Galois group.
-/

open Topology

noncomputable section

namespace Rigidity.RET

section Kummer

variable (n : ℕ) [NeZero n]

/-- **The projection of the power covering**: the `n`-th power of the coordinate, read as a map
from the punctured plane to the plane. -/
def kummerProj (n : ℕ) : ℂˣ → ℂ := fun z => (z : ℂ) ^ n

omit [NeZero n] in
theorem kummerProj_apply (z : ℂˣ) : kummerProj n z = (z : ℂ) ^ n := rfl

/-- The coordinate of the punctured plane is an open embedding into the plane. -/
theorem isOpenEmbedding_units_val : IsOpenEmbedding (Units.val : ℂˣ → ℂ) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have hrange : Set.range (Units.val : ℂˣ → ℂ) = ({0} : Set ℂ)ᶜ := by
    ext z
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl⟩
      exact u.ne_zero
    · intro hz
      exact ⟨Units.mk0 z hz, rfl⟩
  rw [hrange]
  exact isOpen_compl_singleton

section Npow
-- The power map of the punctured plane is a covering map; the statement mentions no action, and
-- the scalar action of `ℂˣ` on itself has to be pinned to the multiplication for the covering
-- theorem to apply.
attribute [-instance] Units.mulAction'

/-- **The power map of the punctured plane is a local homeomorphism.** -/
theorem isLocalHomeomorph_npow : IsLocalHomeomorph (fun z : ℂˣ => z ^ n) :=
  (Complex.isQuotientCoveringMap_npow n).isCoveringMap.isLocalHomeomorph

end Npow

/-- **The power map is a local homeomorphism of the punctured plane onto the plane punctured at the
origin.** -/
theorem isLocalHomeomorph_kummerProj : IsLocalHomeomorph (kummerProj n) := by
  have h1 : IsLocalHomeomorph (fun z : ℂˣ => z ^ n) := isLocalHomeomorph_npow n
  have h2 : IsLocalHomeomorph (Units.val : ℂˣ → ℂ) :=
    (isOpenEmbedding_units_val).isLocalHomeomorph
  have hcomp : (Units.val ∘ fun z : ℂˣ => z ^ n) = kummerProj n := by
    funext z
    simp [kummerProj]
  exact hcomp ▸ h2.comp h1

/-- **The power map misses the origin and nothing else.** -/
theorem range_kummerProj : Set.range (kummerProj n) = ((({0} : Finset ℂ) : Set ℂ))ᶜ := by
  ext z
  simp only [Set.mem_range, Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact pow_ne_zero _ u.ne_zero
  · intro hz
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (NeZero.pos n)
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne n)] at hw
      exact hz hw.symm
    exact ⟨Units.mk0 w hw0, by simpa [kummerProj] using hw⟩

/-! ### The deck group -/

omit [NeZero n] in
theorem rootsOfUnity_smul (a : ↥(rootsOfUnity n ℂ)) (z : ℂˣ) : a • z = (a : ℂˣ) * z := by
  rw [Subgroup.smul_def, Units.smul_eq_mul]

omit [NeZero n] in
theorem rootsOfUnity_val_pow (a : ↥(rootsOfUnity n ℂ)) : ((a : ℂˣ) : ℂ) ^ n = 1 := by
  have h : ((a : ℂˣ)) ^ n = 1 := a.2
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

instance continuousConstSMul_rootsOfUnity : ContinuousConstSMul ↥(rootsOfUnity n ℂ) ℂˣ := by
  refine ⟨fun a => ?_⟩
  have hfun : (fun z : ℂˣ => a • z) = fun z : ℂˣ => (a : ℂˣ) * z :=
    funext fun z => rootsOfUnity_smul n a z
  rw [hfun]
  exact continuous_const.mul continuous_id

/-- **The roots of unity move the power covering over its base.** -/
instance isOverBase_rootsOfUnity : IsOverBase ↥(rootsOfUnity n ℂ) (kummerProj n) where
  smul_eq a z := by
    rw [kummerProj_apply, kummerProj_apply, rootsOfUnity_smul, Units.val_mul, mul_pow,
      rootsOfUnity_val_pow, one_mul]

omit [NeZero n] in
/-- **The roots of unity act transitively on each fibre of the power covering.** -/
theorem transitive_rootsOfUnity (y y' : ℂˣ) (h : kummerProj n y = kummerProj n y') :
    ∃ b : ↥(rootsOfUnity n ℂ), y' = b • y := by
  have hpow : (y' * y⁻¹) ^ n = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_mul, mul_pow, Units.val_one]
    rw [kummerProj_apply, kummerProj_apply] at h
    rw [Units.val_inv_eq_inv_val, inv_pow, ← h]
    exact mul_inv_cancel₀ (pow_ne_zero _ y.ne_zero)
  refine ⟨⟨y' * y⁻¹, by rwa [mem_rootsOfUnity]⟩, ?_⟩
  rw [rootsOfUnity_smul]
  simp

/-! ### The separating function -/

/-- **The coordinate of the total space is holomorphic on the power covering**: it is a continuous
branch of an `n`-th root of the base coordinate. -/
theorem isHolo_kummer_val : IsHolo (kummerProj n) (fun z : ℂˣ => (z : ℂ)) := by
  intro y
  obtain ⟨e, hy, he⟩ := isLocalHomeomorph_kummerProj n y
  have hchart : IsChartAt (kummerProj n) e y := ⟨hy, he⟩
  refine ⟨e, hchart, ?_⟩
  have hcont : ContinuousOn (fun w => ((e.symm w : ℂˣ) : ℂ)) e.target :=
    Units.continuous_val.comp_continuousOn e.continuousOn_symm
  have hpow : ∀ w ∈ e.target, ((e.symm w : ℂˣ) : ℂ) ^ n = w := by
    intro w hw
    have h1 : kummerProj n (e.symm w) = e (e.symm w) := congrFun he _
    rw [← kummerProj_apply, h1, e.right_inv hw]
  have h0 : ∀ w ∈ e.target, w ≠ 0 := by
    intro w hw
    rw [← hpow w hw]
    exact pow_ne_zero _ (e.symm w).ne_zero
  exact analyticAt_of_pow_eq (NeZero.pos n) e.open_target hcont hpow h0 hchart.mem_target

/-- **The coordinate of the total space is of moderate growth on the power covering**: it is the
`n`-th root of the base coordinate, so it is bounded by it at infinity and bounded near the
puncture. -/
theorem isModerate_kummer_val :
    IsModerate (kummerProj n) {0} (fun z : ℂˣ => (z : ℂ)) where
  punct := by
    intro s hs
    have hs0 : s = 0 := by simpa using hs
    subst hs0
    refine ⟨1, one_pos, 1, zero_le_one, 0, fun y hy => ?_⟩
    have hball : ‖kummerProj n y‖ < 1 := by
      have h := hy.1
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero] at h
      exact h
    rw [kummerProj_apply, norm_pow] at hball
    have hlt : ‖(y : ℂ)‖ < 1 := by
      by_contra hcon
      push_neg at hcon
      exact absurd hball (not_lt.2 (one_le_pow₀ hcon))
    simpa using hlt.le
  infty := by
    refine ⟨1, 1, 1, zero_le_one, fun y hy => ?_⟩
    rw [kummerProj_apply, norm_pow] at hy ⊢
    have h1 : (1 : ℝ) ≤ ‖(y : ℂ)‖ := by
      by_contra hcon
      push_neg at hcon
      exact absurd hy (not_le.2 (pow_lt_one₀ (norm_nonneg _) hcon (NeZero.ne n)))
    rw [one_mul, pow_one]
    exact le_self_pow₀ h1 (NeZero.ne n)

/-- **The coordinate separates the points of a fibre of the power covering.** -/
theorem hasSeparatingFunction_kummer :
    HasSeparatingFunction (isLocalHomeomorph_kummerProj n) {0} ↥(rootsOfUnity n ℂ) := by
  refine ⟨fun z : ℂˣ => (z : ℂ), ⟨isHolo_kummer_val n, isModerate_kummer_val n⟩, 1, ?_⟩
  intro a b hab
  rw [rootsOfUnity_smul, rootsOfUnity_smul, mul_one, mul_one] at hab
  exact Subtype.ext (Units.ext hab)

/-- **The rational functions of the base coordinate have a Galois extension of degree `n` whose
Galois group is the group of `n`-th roots of unity** — the Kummer extension, produced by the
Galois correspondence for the power covering out of its topology and one function on it. -/
theorem exists_isGalois_ratFunc_rootsOfUnity :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℂ) L),
      IsGalois (RatFunc ℂ) L ∧ Nonempty (↥(rootsOfUnity n ℂ) ≃* (L ≃ₐ[RatFunc ℂ] L)) ∧
        Module.finrank (RatFunc ℂ) L = n := by
  obtain ⟨L, hL, halg, hgal, hiso, hdeg⟩ :=
    exists_isGalois_ratFunc_of_hasSeparatingFunction (H := ↥(rootsOfUnity n ℂ))
      (isLocalHomeomorph_kummerProj n) (range_kummerProj n) (transitive_rootsOfUnity n)
      (hasSeparatingFunction_kummer n)
  exact ⟨L, hL, halg, hgal, hiso, by
    rw [hdeg, HasEnoughRootsOfUnity.natCard_rootsOfUnity ℂ n]⟩

end Kummer

end Rigidity.RET

end
