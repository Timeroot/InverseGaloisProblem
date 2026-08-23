/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The Galois action on the completions at the infinite places

A Galois automorphism of a number field fixing an infinite place preserves the absolute value
attached to that place, so it is an isometry of the field for the metric of the place.  Being an
isometry it is uniformly continuous, and it therefore extends to an automorphism of the completion
at that place.  The decomposition group of the place acts on the completion by ring automorphisms.

An automorphism that moves the place is no less useful: it carries the absolute value of a place to
the absolute value of its image, so it is an isometry from the field with the metric of one place to
the field with the metric of the other, and extends to an isomorphism between the two completions.

This is the archimedean counterpart of the action on the adic completions, and the two are built in
the same way: an isometry of a dense subfield extends to the completion, and the extension inherits
the multiplicativity from the dense subfield.

## Main definitions

* `InverseGalois.CFT.withAbsGalEquiv`: a Galois automorphism, read as a map from the field with the
  metric of one place to the field with the metric of its image.
* `InverseGalois.CFT.infiniteCompletionGalEquiv`: **the induced isomorphism between the completion
  at a place and the completion at its image.**
* `InverseGalois.CFT.withAbsAut`: a Galois automorphism fixing a place, read as a map of the field
  with the metric of that place.
* `InverseGalois.CFT.infiniteCompletionAut`: **the induced automorphism of the completion.**

## Main results

* `InverseGalois.CFT.apply_of_smul_eq`: an automorphism fixing a place preserves its absolute
  value.
* `InverseGalois.CFT.instMulSemiringActionInfiniteCompletion`: **the decomposition group at an
  infinite place acts on the completion there.**
* `InverseGalois.CFT.infiniteCompletionAut_coe`: the action on the dense subfield is the Galois
  action.

## Tags

number field, infinite place, completion, Galois action, decomposition group
-/

namespace InverseGalois.CFT

open MulAction NumberField NumberField.InfinitePlace

/-! ### A shortcut for the field structure of the completion -/

section Shortcut

variable {K : Type*} [Field K] (w : InfinitePlace K)

set_option synthInstance.maxHeartbeats 1000000 in
/-- The completion at an infinite place is a field.  This repeats the instance coming from the
normed field structure, so that the algebraic structure of the completion is found directly
instead of through the whole normed hierarchy. -/
noncomputable instance instFieldInfiniteCompletion : Field w.Completion := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- The completion at an infinite place is a commutative monoid under multiplication.  This
repeats the instance coming from the field structure, so that the group of units of the completion
is found directly instead of through the whole normed hierarchy. -/
noncomputable instance instCommMonoidInfiniteCompletion : CommMonoid w.Completion := inferInstance

end Shortcut

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (w : InfinitePlace K)

/-! ### An automorphism fixing a place is an isometry -/

/-- **An automorphism fixing a place preserves its absolute value.** -/
theorem apply_of_smul_eq {σ : Gal(K/k)} (hσ : σ • w = w) (x : K) : w (σ x) = w x := by
  calc w (σ x) = (σ • w) (σ x) := by rw [hσ]
    _ = w x := by rw [InfinitePlace.smul_apply, σ.symm_apply_apply]

/-- An automorphism fixing a place preserves its absolute value, read through the inverse. -/
theorem apply_symm_of_smul_eq {σ : Gal(K/k)} (hσ : σ • w = w) (x : K) : w (σ.symm x) = w x := by
  conv_rhs => rw [← hσ]
  rw [InfinitePlace.smul_apply]

/-! ### The completions at a place and at its image -/

/-- **An automorphism carries the absolute value of a place to the absolute value of its image.** -/
theorem smul_apply_smul (σ : Gal(K/k)) (x : K) : (σ • w) (σ x) = w x := by
  rw [InfinitePlace.smul_apply, σ.symm_apply_apply]

/-- **A Galois automorphism, read as a map from the field with the metric of one place to the field
with the metric of its image.** -/
def withAbsGalEquiv (σ : Gal(K/k)) : WithAbs w.1 ≃+* WithAbs (σ • w).1 :=
  ((WithAbs.equiv w.1).trans σ.toRingEquiv).trans (WithAbs.equiv (σ • w).1).symm

@[simp]
theorem norm_withAbsGalEquiv (σ : Gal(K/k)) (x : WithAbs w.1) :
    ‖withAbsGalEquiv w σ x‖ = ‖x‖ := by
  rw [WithAbs.norm_eq_abv, WithAbs.norm_eq_abv]
  exact smul_apply_smul w σ _

@[simp]
theorem norm_withAbsGalEquiv_symm (σ : Gal(K/k)) (y : WithAbs (σ • w).1) :
    ‖(withAbsGalEquiv w σ).symm y‖ = ‖y‖ := by
  have h := norm_withAbsGalEquiv w σ ((withAbsGalEquiv w σ).symm y)
  rw [(withAbsGalEquiv w σ).apply_symm_apply] at h
  exact h.symm

theorem isometry_withAbsGalEquiv (σ : Gal(K/k)) : Isometry (withAbsGalEquiv w σ) := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  show (σ • w).1 (σ (WithAbs.equiv w.1 x) - σ (WithAbs.equiv w.1 y))
    = w.1 (WithAbs.equiv w.1 x - WithAbs.equiv w.1 y)
  rw [← map_sub]
  exact smul_apply_smul w σ _

theorem isometry_withAbsGalEquiv_symm (σ : Gal(K/k)) :
    Isometry (withAbsGalEquiv w σ).symm := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← norm_withAbsGalEquiv w σ, map_sub,
    (withAbsGalEquiv w σ).apply_symm_apply, (withAbsGalEquiv w σ).apply_symm_apply]

/-- **The isomorphism between the completion at an infinite place and the completion at its
image** under a Galois automorphism. -/
noncomputable def infiniteCompletionGalEquiv (σ : Gal(K/k)) :
    w.Completion ≃+* (σ • w).Completion :=
  UniformSpace.Completion.mapRingEquiv (withAbsGalEquiv w σ)
    (isometry_withAbsGalEquiv w σ).continuous (isometry_withAbsGalEquiv_symm w σ).continuous

theorem continuous_infiniteCompletionGalEquiv (σ : Gal(K/k)) :
    Continuous (infiniteCompletionGalEquiv w σ) :=
  UniformSpace.Completion.continuous_map

@[simp]
theorem infiniteCompletionGalEquiv_coe (σ : Gal(K/k)) (x : WithAbs w.1) :
    infiniteCompletionGalEquiv w σ (x : w.Completion)
      = ((withAbsGalEquiv w σ x : WithAbs (σ • w).1) : (σ • w).Completion) :=
  UniformSpace.Completion.mapRingHom_coe (isometry_withAbsGalEquiv w σ).continuous x

/-- **The isomorphism of completions is an isometry.** -/
@[simp]
theorem norm_infiniteCompletionGalEquiv (σ : Gal(K/k)) (z : w.Completion) :
    ‖infiniteCompletionGalEquiv w σ z‖ = ‖z‖ := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq (continuous_norm.comp (continuous_infiniteCompletionGalEquiv w σ))
      continuous_norm
  · intro x
    rw [infiniteCompletionGalEquiv_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe, norm_withAbsGalEquiv]

/-! ### An automorphism fixing a place -/

/-- **A Galois automorphism fixing an infinite place, read as a map of the field with the metric of
that place.** -/
def withAbsAut (σ : Gal(K/k)) (_hσ : σ • w = w) : WithAbs w.1 ≃+* WithAbs w.1 :=
  ((WithAbs.equiv w.1).trans σ.toRingEquiv).trans (WithAbs.equiv w.1).symm

@[simp]
theorem norm_withAbsAut (σ : Gal(K/k)) (hσ : σ • w = w) (x : WithAbs w.1) :
    ‖withAbsAut w σ hσ x‖ = ‖x‖ := by
  rw [WithAbs.norm_eq_abv, WithAbs.norm_eq_abv]
  exact apply_of_smul_eq w hσ _

@[simp]
theorem norm_withAbsAut_symm (σ : Gal(K/k)) (hσ : σ • w = w) (y : WithAbs w.1) :
    ‖(withAbsAut w σ hσ).symm y‖ = ‖y‖ := by
  have h := norm_withAbsAut w σ hσ ((withAbsAut w σ hσ).symm y)
  rw [(withAbsAut w σ hσ).apply_symm_apply] at h
  exact h.symm

theorem isometry_withAbsAut (σ : Gal(K/k)) (hσ : σ • w = w) :
    Isometry (withAbsAut w σ hσ) := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  show w.1 (σ (WithAbs.equiv w.1 x) - σ (WithAbs.equiv w.1 y))
    = w.1 (WithAbs.equiv w.1 x - WithAbs.equiv w.1 y)
  rw [← map_sub]
  exact apply_of_smul_eq w hσ _

theorem isometry_withAbsAut_symm (σ : Gal(K/k)) (hσ : σ • w = w) :
    Isometry (withAbsAut w σ hσ).symm := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  show w.1 (σ.symm (WithAbs.equiv w.1 x) - σ.symm (WithAbs.equiv w.1 y))
    = w.1 (WithAbs.equiv w.1 x - WithAbs.equiv w.1 y)
  rw [← map_sub]
  exact apply_symm_of_smul_eq w hσ _

/-! ### The automorphism of the completion -/

/-- **The automorphism of the completion at an infinite place induced by a Galois automorphism
fixing that place.** -/
noncomputable def infiniteCompletionAut (σ : Gal(K/k)) (hσ : σ • w = w) :
    w.Completion ≃+* w.Completion :=
  UniformSpace.Completion.mapRingEquiv (withAbsAut w σ hσ)
    (isometry_withAbsAut w σ hσ).continuous (isometry_withAbsAut_symm w σ hσ).continuous

theorem continuous_infiniteCompletionAut (σ : Gal(K/k)) (hσ : σ • w = w) :
    Continuous (infiniteCompletionAut w σ hσ) :=
  UniformSpace.Completion.continuous_map

@[simp]
theorem infiniteCompletionAut_coe (σ : Gal(K/k)) (hσ : σ • w = w) (x : WithAbs w.1) :
    infiniteCompletionAut w σ hσ (x : w.Completion)
      = ((withAbsAut w σ hσ x : WithAbs w.1) : w.Completion) :=
  UniformSpace.Completion.mapRingHom_coe (isometry_withAbsAut w σ hσ).continuous x

theorem infiniteCompletionAut_one (z : w.Completion) :
    infiniteCompletionAut w (1 : Gal(K/k)) (one_smul Gal(K/k) w) z = z := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq (continuous_infiniteCompletionAut w (1 : Gal(K/k)) (one_smul Gal(K/k) w))
      continuous_id
  · intro x
    rw [infiniteCompletionAut_coe]
    rfl

theorem infiniteCompletionAut_mul (σ τ : Gal(K/k)) (hσ : σ • w = w) (hτ : τ • w = w)
    (hστ : (σ * τ) • w = w) (z : w.Completion) :
    infiniteCompletionAut w (σ * τ) hστ z
      = infiniteCompletionAut w σ hσ (infiniteCompletionAut w τ hτ z) := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq (continuous_infiniteCompletionAut w (σ * τ) hστ)
      ((continuous_infiniteCompletionAut w σ hσ).comp
        (continuous_infiniteCompletionAut w τ hτ))
  · intro x
    rw [infiniteCompletionAut_coe, infiniteCompletionAut_coe, infiniteCompletionAut_coe]
    rfl

/-! ### The action of the decomposition group -/

/-- **The decomposition group at an infinite place acts on the completion there.** -/
noncomputable instance instMulSemiringActionInfiniteCompletion :
    MulSemiringAction ↥(stabilizer Gal(K/k) w) w.Completion where
  smul σ z := infiniteCompletionAut w σ.1 (mem_stabilizer_iff.mp σ.2) z
  one_smul z := infiniteCompletionAut_one w z
  mul_smul σ τ z := infiniteCompletionAut_mul w σ.1 τ.1 _ _ _ z
  smul_zero σ := map_zero (infiniteCompletionAut w σ.1 (mem_stabilizer_iff.mp σ.2))
  smul_add σ := map_add (infiniteCompletionAut w σ.1 (mem_stabilizer_iff.mp σ.2))
  smul_one σ := map_one (infiniteCompletionAut w σ.1 (mem_stabilizer_iff.mp σ.2))
  smul_mul σ := map_mul (infiniteCompletionAut w σ.1 (mem_stabilizer_iff.mp σ.2))

@[simp]
theorem stabilizer_smul_infiniteCompletion_def (σ : ↥(stabilizer Gal(K/k) w))
    (z : w.Completion) :
    σ • z = infiniteCompletionAut w σ.1 (mem_stabilizer_iff.mp σ.2) z := rfl

/-- The decomposition group preserves the metric of the completion. -/
@[simp]
theorem norm_stabilizer_smul_infiniteCompletion (σ : ↥(stabilizer Gal(K/k) w))
    (z : w.Completion) : ‖σ • z‖ = ‖z‖ := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq
      (continuous_norm.comp
        (continuous_infiniteCompletionAut w σ.1 (mem_stabilizer_iff.mp σ.2)))
      continuous_norm
  · intro x
    rw [stabilizer_smul_infiniteCompletion_def, infiniteCompletionAut_coe,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe, norm_withAbsAut]

/-- **The action of the decomposition group on the dense subfield is the Galois action.** -/
theorem smul_infiniteCompletion_coe (σ : ↥(stabilizer Gal(K/k) w)) (x : WithAbs w.1) :
    σ • (x : w.Completion) = ((withAbsAut w σ.1 (mem_stabilizer_iff.mp σ.2) x : WithAbs w.1) :
      w.Completion) :=
  infiniteCompletionAut_coe w σ.1 (mem_stabilizer_iff.mp σ.2) x

/-- **The decomposition group acts faithfully on the completion**, because it acts faithfully on
the dense subfield. -/
instance instFaithfulSMulStabilizerInfiniteCompletion :
    FaithfulSMul ↥(stabilizer Gal(K/k) w) w.Completion where
  eq_of_smul_eq_smul {σ τ} h := by
    refine Subtype.ext (AlgEquiv.ext fun x => ?_)
    have hx := h ((WithAbs.equiv w.1).symm x : w.Completion)
    rw [smul_infiniteCompletion_coe, smul_infiniteCompletion_coe] at hx
    exact UniformSpace.Completion.coe_injective (WithAbs w.1) hx

end InverseGalois.CFT
