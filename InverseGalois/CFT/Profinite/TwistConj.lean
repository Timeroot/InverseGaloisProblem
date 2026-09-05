/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.H1Conj
import InverseGalois.CFT.Profinite.Twist

/-!
# The equivariance of the twist

The first cohomology of a normal subgroup carries the conjugation action of the ambient group, and
the twisting construction is built from a map of the coefficients.  For the two to be compatible
the map of the coefficients has to move as well: an element of the ambient group carries a
homomorphism between two of its modules to the homomorphism obtained by translating the argument
backwards and the value forwards, and **this is an action of the ambient group on the group of
homomorphisms of the coefficients** for which the map induced in cohomology by a homomorphism is
equivariant.

The twist is then equivariant on the nose.  A class obtained from an element of the base group and
a homomorphism of the coefficients is conjugated by conjugating the class the base group provides —
which for Kummer theory is the Galois action on the units — and by moving the homomorphism.  This
is the last thing needed to read the twisted first cohomology as a module over the quotient.

## Main definitions

* `InverseGalois.CFT.homSMul`: the conjugate of a homomorphism of the coefficients.
* `InverseGalois.CFT.homMulDistribMulAction`: the group of homomorphisms of the coefficients as a
  module over the ambient group.

## Main results

* `InverseGalois.CFT.conjH1_coeffH1`: **conjugation commutes with the map induced by a
  homomorphism of the coefficients**, the homomorphism being conjugated too.
* `InverseGalois.CFT.conjH1_twistClass`: **the twist is equivariant.**

## Tags

Galois cohomology, conjugation, coefficients, twist, equivariance
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### The action on homomorphisms of the coefficients -/

section Hom

variable {G : Type*} [Group G] {M E : Type*} [CommGroup M] [CommGroup E]
variable [MulDistribMulAction G M] [MulDistribMulAction G E]

/-- **The conjugate of a homomorphism of the coefficients**: translate the argument backwards and
the value forwards. -/
def homSMul (σ : G) (w : M →* E) : M →* E :=
  ((MulDistribMulAction.toMonoidHom E σ).comp w).comp (MulDistribMulAction.toMonoidHom M σ⁻¹)

@[simp]
theorem homSMul_apply (σ : G) (w : M →* E) (m : M) : homSMul σ w m = σ • w (σ⁻¹ • m) := rfl

theorem one_homSMul (w : M →* E) : homSMul (1 : G) w = w :=
  MonoidHom.ext fun m => by simp only [homSMul_apply, inv_one, one_smul]

theorem homSMul_comp (σ τ : G) (w : M →* E) : homSMul σ (homSMul τ w) = homSMul (σ * τ) w :=
  MonoidHom.ext fun m => by simp only [homSMul_apply, mul_inv_rev, mul_smul]

theorem homSMul_mul (σ : G) (w v : M →* E) :
    homSMul σ (w * v) = homSMul σ w * homSMul σ v :=
  MonoidHom.ext fun m => by simp only [homSMul_apply, MonoidHom.mul_apply, smul_mul']

theorem homSMul_one (σ : G) : homSMul σ (1 : M →* E) = 1 :=
  MonoidHom.ext fun m => by simp only [homSMul_apply, MonoidHom.one_apply, smul_one]

variable (G M E) in
/-- **The homomorphisms between two modules over a group form a module over that group.** -/
instance homMulDistribMulAction : MulDistribMulAction G (M →* E) where
  smul := homSMul
  one_smul := one_homSMul
  mul_smul σ τ w := (homSMul_comp σ τ w).symm
  smul_mul := homSMul_mul
  smul_one := homSMul_one

end Hom

/-! ### Conjugation and a map of the coefficients -/

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] {N : Subgroup G}
variable {M E : Type*} [CommGroup M] [CommGroup E]
variable [MulDistribMulAction G M] [MulDistribMulAction G E]

/-- **Conjugation commutes with the map induced by a homomorphism of the coefficients**, provided
the homomorphism of the coefficients is conjugated as well. -/
theorem conjH1_coeffH1 (hN : N.Normal) (σ : G) (w : M →* E)
    (hw : ∀ (x : ↥N) (m : M), w (x • m) = x • w m)
    (hσw : ∀ (x : ↥N) (m : M), homSMul σ w (x • m) = x • homSMul σ w m)
    (z : SmoothH1 ↥N M) :
    conjH1 hN σ (coeffH1 w hw z) = coeffH1 (homSMul σ w) hσw (conjH1 hN σ z) := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  rw [coeffH1_smoothH1Mk, conjH1_smoothH1Mk, conjH1_smoothH1Mk, coeffH1_smoothH1Mk]
  refine smoothH1Mk_congr (funext fun x : ↥N => ?_) _ _ _ _
  rw [conjCochain_apply, coeffMap₁_apply, coeffMap₁_apply, conjCochain_apply, homSMul_apply,
    inv_smul_smul]

end Conj

/-! ### The equivariance of the twist -/

section Twist

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] {N : Subgroup G}
variable {M E A : Type*} [CommGroup M] [CommGroup E] [CommGroup A]
variable [MulDistribMulAction G M] [MulDistribMulAction G E]
variable (hN : N.Normal)
variable (htrivM : ∀ (x : ↥N) (m : M), x • m = m) (htrivE : ∀ (x : ↥N) (e : E), x • e = e)
variable (κ : A →* SmoothH1 ↥N M) (ρ : G → A → A)

/-- **The twist is equivariant**: conjugating the class attached to an element of the base group
and a homomorphism of the coefficients is taking the class attached to the conjugated element and
the conjugated homomorphism. -/
theorem conjH1_twistClass (hκ : ∀ (σ : G) (a : A), conjH1 hN σ (κ a) = κ (ρ σ a))
    (σ : G) (a : A) (w : M →* E) :
    conjH1 hN σ (twistClass htrivM htrivE κ a w)
      = twistClass htrivM htrivE κ (ρ σ a) (homSMul σ w) := by
  simp only [twistClass]
  rw [conjH1_coeffH1 hN σ w (smul_eq_of_trivial htrivM htrivE w)
    (smul_eq_of_trivial htrivM htrivE (homSMul σ w)) (κ a), hκ]

end Twist

end InverseGalois.CFT
