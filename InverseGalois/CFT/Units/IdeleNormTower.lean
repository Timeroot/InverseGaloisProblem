/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleNorm
import InverseGalois.CFT.Units.IdeleRestrict

/-!
# The norm on the ideles of a tower is the composite of the two norms

The norm from the top field of a tower to the bottom is the norm to the middle field followed by the
norm from the middle field.  This is what lets a statement about the norms of a cyclic extension be
applied inside a solvable tower, one step at a time.

The norm is defined through the sum of the conjugates, so the statement to prove is that summing
over the Galois group of the top field is summing over the Galois group of the middle field of the
sums over the Galois group of the top field over the middle.  Lifting an automorphism of the middle
field to the top field and multiplying by an automorphism fixing the middle field is a bijection
from the product of the two Galois groups to the Galois group of the whole extension, so the two
sums have the same terms.

The two ways of moving an idele of the middle field agree by the compatibility of the inclusion with
restriction, and the inclusions of a tower compose, so the two norms have the same image among the
ideles of the top field; the inclusion is injective, so they are equal.

## Main results

* `InverseGalois.CFT.bijective_liftNormal_mul_restrictScalars`: **lifting and multiplying is a
  bijection from the product of the Galois groups of a tower to the Galois group of the whole
  extension.**
* `InverseGalois.CFT.galSum_eq_sum_galSum`: **the sum of the conjugates over the whole extension is
  the sum over the middle field of the moved sums over the top field.**
* `InverseGalois.CFT.ideleNorm_trans`: **the norm on the ideles of a tower is the norm to the middle
  field followed by the norm from the middle field.**

## Tags

number field, idele, norm map, tower, transitivity
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section IdeleNormTower

variable {k F K : Type*} [Field k] [NumberField k] [Field F] [NumberField F] [Field K]
  [NumberField K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]
  [IsGalois k F] [IsGalois F K] [IsGalois k K]

/-! ### The Galois group of a tower -/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

variable (k F) in
omit [NumberField k] [NumberField F] [NumberField K] [IsGalois F K] [IsGalois k K] in
/-- **An automorphism of the top field fixing the middle field restricts to the identity on the
middle field.** -/
theorem restrictNormalHom_restrictScalars (τ : Gal(K/F)) :
    AlgEquiv.restrictNormalHom F (τ.restrictScalars k) = 1 := by
  refine AlgEquiv.ext fun y => (algebraMap F K).injective ?_
  rw [algebraMap_restrictNormalHom F]
  exact τ.commutes y

variable (k) in
omit [NumberField k] [NumberField F] [NumberField K] [IsGalois F K] [IsGalois k K] in
/-- **An automorphism of the top field restricting to the identity on the middle field is an
automorphism over the middle field.** -/
theorem exists_restrictScalars_of_restrictNormalHom_eq_one {g : Gal(K/k)}
    (hg : AlgEquiv.restrictNormalHom F g = 1) : ∃ τ : Gal(K/F), τ.restrictScalars k = g := by
  have hy : ∀ y : F, g.toRingEquiv (algebraMap F K y) = algebraMap F K y := by
    intro y
    show g (algebraMap F K y) = algebraMap F K y
    rw [← algebraMap_restrictNormalHom F, hg]
    rfl
  exact ⟨AlgEquiv.ofRingEquiv (R := F) hy, AlgEquiv.ext fun _ => rfl⟩

variable (k F) in
omit [NumberField k] [NumberField F] [NumberField K] [IsGalois F K] in
/-- **Lifting an automorphism of the middle field and multiplying by an automorphism fixing the
middle field is a bijection from the product of the two Galois groups of a tower to the Galois group
of the whole extension**: restricting to the middle field recovers the first factor, and dividing it
out leaves the second. -/
theorem bijective_liftNormal_mul_restrictScalars :
    Function.Bijective (fun p : Gal(F/k) × Gal(K/F) =>
      p.1.liftNormal K * p.2.restrictScalars k) := by
  have hlift : ∀ h : Gal(F/k), AlgEquiv.restrictNormalHom F (h.liftNormal K) = h := fun h =>
    h.restrict_liftNormal K
  constructor
  · rintro ⟨h₁, τ₁⟩ ⟨h₂, τ₂⟩ hp
    have hr := congrArg (AlgEquiv.restrictNormalHom F) hp
    rw [map_mul, map_mul, restrictNormalHom_restrictScalars k F,
      restrictNormalHom_restrictScalars k F, mul_one, mul_one, hlift, hlift] at hr
    subst hr
    exact Prod.ext rfl (AlgEquiv.restrictScalars_injective k (mul_left_cancel hp))
  · intro g
    have h1 : AlgEquiv.restrictNormalHom F
        (((AlgEquiv.restrictNormalHom F g).liftNormal K)⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hlift, inv_mul_cancel]
    obtain ⟨τ, hτ⟩ := exists_restrictScalars_of_restrictNormalHom_eq_one k h1
    refine ⟨(AlgEquiv.restrictNormalHom F g, τ), ?_⟩
    show (AlgEquiv.restrictNormalHom F g).liftNormal K * AlgEquiv.restrictScalars k τ = g
    rw [hτ, mul_inv_cancel_left]

/-! ### The sum of the conjugates in a tower -/

variable (k F) in
omit [NumberField k] [NumberField F] [IsGalois k F] [IsGalois F K] [IsGalois k K] in
/-- **An automorphism over the middle field acts on the ideles as it does over the bottom
field.** -/
theorem ideleAut_restrictScalars (τ : Gal(K/F)) (x : ↥(idele K)) :
    ideleAut (k := F) τ x = ideleAut (k := k) (τ.restrictScalars k) x := rfl

variable (k F K) in
omit [IsGalois F K] in
/-- **The sum of the conjugates over the whole extension is the sum over the middle field of the
moved sums over the top field**: the Galois group of the whole extension is in bijection with the
product of the two Galois groups of the tower. -/
theorem galSum_eq_sum_galSum (x : ↥(idele K)) :
    galSum k K x = ∑ h : Gal(F/k), ideleAut (k := k) (h.liftNormal K) (galSum F K x) := by
  rw [galSum_apply, ← Fintype.sum_bijective _ (bijective_liftNormal_mul_restrictScalars k F)
    _ (fun g : Gal(K/k) => ideleAut (k := k) g x) fun _ => rfl, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [galSum_apply, map_sum]
  exact Finset.sum_congr rfl fun τ _ => by
    rw [ideleAut_restrictScalars k F, ← ideleAut_mul]

/-! ### Transitivity of the norm -/

variable (k F K) in
/-- **The norm on the ideles of a tower is the norm to the middle field followed by the norm from
the middle field.**  Both sides have the same image among the ideles of the top field, namely the
sum of the conjugates, and the inclusion of the ideles of the bottom field is injective. -/
theorem ideleNorm_trans (x : ↥(idele K)) :
    ideleNorm k F (ideleNorm F K x) = ideleNorm k K x := by
  refine ideleComap_injective k K ?_
  have hL : ideleComap k K (ideleNorm k F (ideleNorm F K x))
      = ∑ h : Gal(F/k), ideleAut (k := k) (h.liftNormal K) (galSum F K x) := by
    rw [← ideleComap_trans k F K, ideleComap_ideleNorm, galSum_apply, map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hres : AlgEquiv.restrictNormalHom F (h.liftNormal K) = h := h.restrict_liftNormal K
    rw [← ideleComap_ideleNorm F K x, ideleAut_ideleComap_restrict F (h.liftNormal K), hres]
  rw [hL, ideleComap_ideleNorm, galSum_eq_sum_galSum k F K]

end IdeleNormTower

end InverseGalois.CFT
