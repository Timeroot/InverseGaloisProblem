/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.TwistAction

/-!
# Pushing the coefficients of a twisted class forward

A twisted class is the class attached to an element of a base group and a homomorphism of the
cyclic coefficients into a finite module: it is the image of a fixed class under that homomorphism.
Reading it that way makes it obvious what happens when the finite module is enlarged — **pushing
the coefficients forward along a homomorphism of the modules is the same as composing the
homomorphism of the cyclic coefficients with it.**  Nothing in the base group moves, so the
twisting map out of the tensor product commutes with the identity on the units tensored with
composition on the homomorphisms.

This is the companion, in the coefficient direction, of the naturality of the twisting map in the
group.  A construction which is free to enlarge the module it is working with needs both: the first
to compare what happens over a subgroup with what happens over the whole group, the second to
compare what happens for one module with what happens for a larger one.

The map of the tensor product which that naturality names is itself equivariant, and this is where
the hypothesis on the homomorphism of the modules is used: conjugating a homomorphism of the cyclic
coefficients translates its value forwards, and an equivariant homomorphism of the modules commutes
with that translation.  So the map of the tensor product is a map of modules over the group, and
over the quotient by any subgroup moving neither factor.

## Main definitions

* `InverseGalois.CFT.homCoeffAddHom`: composition with a homomorphism of the modules, on the
  additive copy of the group of homomorphisms of the cyclic coefficients.
* `InverseGalois.CFT.tensorCoeffMap`: **the induced map of the tensor product of the base group
  with the homomorphisms of the cyclic coefficients.**

## Main results

* `InverseGalois.CFT.coeffH1_twistClass`: **a twisted class pushed forward is the twisted class of
  the composite homomorphism.**
* `InverseGalois.CFT.coeffH1_twistMap`: **the twisting map is natural in the coefficients.**
* `InverseGalois.CFT.tensorCoeffMap_smul` and
  `InverseGalois.CFT.tensorCoeffMap_quotient_smul`: **the induced map of the tensor product is
  equivariant**, for the group and for the quotient by a subgroup moving neither factor.

## Tags

group cohomology, twist, coefficients, naturality, tensor product
-/

namespace InverseGalois.CFT

open TensorProduct

section Coeff

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M E E' A : Type*} [CommGroup M] [CommGroup E] [CommGroup E'] [CommGroup A]
variable [MulDistribMulAction G M] [MulDistribMulAction G E] [MulDistribMulAction G E']
variable (htrivM : ∀ (g : G) (m : M), g • m = m) (htrivE : ∀ (g : G) (e : E), g • e = e)
  (htrivE' : ∀ (g : G) (e : E'), g • e = e)
variable (κ : A →* SmoothH1 G M) (φ : E →* E')

/-- **A twisted class pushed forward along a homomorphism of the modules is the twisted class
attached to the composite homomorphism of the cyclic coefficients.**  Both are the image of the
same fixed class under the same homomorphism of the coefficients. -/
theorem coeffH1_twistClass (a : A) (w : M →* E) :
    coeffH1 φ (smul_eq_of_trivial htrivE htrivE' φ) (twistClass htrivM htrivE κ a w)
      = twistClass htrivM htrivE' κ a (φ.comp w) :=
  coeffH1_comp w (smul_eq_of_trivial htrivM htrivE w) φ (smul_eq_of_trivial htrivE htrivE' φ)
    (smul_eq_of_trivial htrivM htrivE' (φ.comp w)) (κ a)

variable (M E E') in
/-- **Composition with a homomorphism of the modules**, read on the additive copy of the group of
homomorphisms of the cyclic coefficients. -/
def homCoeffAddHom : Additive (M →* E) →+ Additive (M →* E') :=
  MonoidHom.toAdditive (MonoidHom.compHom φ)

@[simp]
theorem homCoeffAddHom_apply (w : M →* E) :
    homCoeffAddHom M E E' φ (Additive.ofMul w) = Additive.ofMul (φ.comp w) := rfl

variable (M E E' A) in
/-- **The map of the tensor product induced by a homomorphism of the modules**: the identity on the
base group and composition on the homomorphisms of the cyclic coefficients. -/
def tensorCoeffMap :
    Additive A ⊗[ℤ] Additive (M →* E) →ₗ[ℤ] Additive A ⊗[ℤ] Additive (M →* E') :=
  TensorProduct.map LinearMap.id (homCoeffAddHom M E E' φ).toIntLinearMap

@[simp]
theorem tensorCoeffMap_tmul (a : A) (w : M →* E) :
    tensorCoeffMap M E E' A φ (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul w)
      = Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul (φ.comp w) := rfl

/-- **The twisting map is natural in the coefficients**: pushing the class forward along a
homomorphism of the modules is the twisting map applied to the identity on the base group tensored
with composition on the homomorphisms of the cyclic coefficients. -/
theorem coeffH1_twistMap (z : Additive A ⊗[ℤ] Additive (M →* E)) :
    MonoidHom.toAdditive (coeffH1 φ (smul_eq_of_trivial htrivE htrivE' φ))
        (twistMap htrivM htrivE κ z)
      = twistMap htrivM htrivE' κ (tensorCoeffMap M E E' A φ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul x y =>
    exact congrArg Additive.ofMul
      (coeffH1_twistClass htrivM htrivE htrivE' κ φ x.toMul y.toMul)

end Coeff

/-! ### The equivariance of the map of the tensor product -/

section Tensor

variable {G : Type*} [Group G] {M E E' A : Type*} [CommGroup M] [CommGroup E] [CommGroup E']
  [CommGroup A]
variable [MulDistribMulAction G M] [MulDistribMulAction G E] [MulDistribMulAction G E']
  [MulDistribMulAction G A]
variable (φ : E →* E') (hφ : ∀ (g : G) (e : E), φ (g • e) = g • φ e)

include hφ in
/-- **Composing with an equivariant homomorphism of the modules commutes with the conjugation of a
homomorphism of the cyclic coefficients**, both conjugations translating the value forwards. -/
theorem comp_homSMul (σ : G) (w : M →* E) : φ.comp (homSMul σ w) = homSMul σ (φ.comp w) :=
  MonoidHom.ext fun m => hφ σ (w (σ⁻¹ • m))

include hφ in
/-- **The map of the tensor product induced by an equivariant homomorphism of the modules is
equivariant** for the action moving each factor. -/
theorem tensorCoeffMap_smul (σ : G) (z : Additive A ⊗[ℤ] Additive (M →* E)) :
    tensorCoeffMap M E E' A φ (σ • z) = σ • tensorCoeffMap M E E' A φ z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', smul_add]
  | tmul x y =>
    show tensorCoeffMap M E E' A φ
        (Additive.ofMul (σ • x.toMul) ⊗ₜ[ℤ] Additive.ofMul (homSMul σ y.toMul)) = _
    rw [tensorCoeffMap_tmul, comp_homSMul φ hφ]
    rfl

variable {N : Subgroup G} [N.Normal] [ActsTrivially N A] [ActsTrivially N (M →* E)]
  [ActsTrivially N (M →* E')]

include hφ in
/-- **The map of the tensor product is equivariant for the quotient by a subgroup moving neither
factor.** -/
theorem tensorCoeffMap_quotient_smul (q : G ⧸ N) (z : Additive A ⊗[ℤ] Additive (M →* E)) :
    tensorCoeffMap M E E' A φ (q • z) = q • tensorCoeffMap M E E' A φ z := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective q
  rw [tensorSMul_quotientMk, tensorSMul_quotientMk]
  exact tensorCoeffMap_smul φ hφ σ z

end Tensor

end InverseGalois.CFT
