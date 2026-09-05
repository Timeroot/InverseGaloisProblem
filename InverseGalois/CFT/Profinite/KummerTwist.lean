/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerConj
import InverseGalois.CFT.Profinite.TwistTensor

/-!
# Kummer theory with the coefficients of a lifting problem

A lifting problem over a number field presents its kernel as a finite module `E` killed by a prime,
acted on by the Galois group of a finite Galois extension and trivially by everything above it.
The first cohomology of the group above it with coefficients in `E` is what an obstruction is built
from, and this file computes it.

Kummer theory computes that cohomology when the coefficients are the roots of unity: the classes
are the units of the field modulo `p`-th powers.  The twist carries that computation to `E`, an
abstract product of copies of the roots of unity, and the answer is **the tensor product of the
units of the field with the group of homomorphisms of the roots of unity into the coefficients**.
Both sides are modules over the Galois group of the finite extension — the units by the Galois
action, the homomorphisms by translation of the value, the cohomology by conjugation — and the
identification respects the three.

That last statement is proved twice over: once on a pure tensor, where it is the equivariance of
the twist together with the equivariance of the Kummer homomorphism, and once on the whole tensor
product, where it says that **the identification carries the action of the Galois group of the base
factor by factor to conjugation.**  The subgroup fixing the field moves neither factor — it
restricts to the identity on the field, hence acts trivially on its units, and it acts trivially on
the source and on the target of a homomorphism of the coefficients, hence trivially on the
homomorphism — so the action is an action of the Galois group of the finite extension itself.

## Main definitions

* `InverseGalois.CFT.kummerTwistEquiv`: the identification.

## Main results

* `InverseGalois.CFT.kummerTwistEquiv_tmul`: the identification on a pure tensor.
* `InverseGalois.CFT.conjH1_kummerTwistClass`: **the identification is equivariant** for the Galois
  group of the base.
* `InverseGalois.CFT.conjH1_kummerTwistEquiv`: **the identification carries the action on the
  tensor product to conjugation.**
* `InverseGalois.CFT.smul_units_eq_self_of_mem_fixingSubgroup` and
  `InverseGalois.CFT.homSMul_eq_self_of_mem_fixingSubgroup`: the subgroup fixing the field moves
  neither factor of the tensor product.

## Tags

Kummer theory, Galois cohomology, twist, lifting problem, roots of unity
-/

namespace InverseGalois.CFT

open groupCohomology TensorProduct

section Twist

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k ↥K]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M] {ι : M →* (↥K)ˣ}
variable {p : ℕ} [NeZero p] [MulDistribMulAction Gal(Ω/k) M]
variable {E : Type*} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
variable (h : IsKummerData ↥K Ω M ι p) (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)

omit [IsGalois k Ω] [FiniteDimensional k ↥K] [NeZero p]
  [MulDistribMulAction Gal(Ω/↥K) M] in
include htriv in
/-- The subgroup fixing an intermediate field acts trivially on coefficients the whole Galois group
acts trivially on. -/
theorem smul_fixingSubgroup_eq_of_trivial (x : ↥K.fixingSubgroup) (m : M) : x • m = m :=
  htriv (x : Gal(Ω/k)) m

variable (htrivE : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable {J : Type*} [Fintype J] [DecidableEq J] (α : E ≃* (J → M))
variable (hEp : ∀ e : E, e ^ p = 1)

/-- **Kummer theory with the coefficients of a lifting problem**: the first cohomology of the
subgroup fixing the field, with coefficients in a finite module killed by `p` which is a product of
copies of the roots of unity, is the tensor product of the units of the field with the group of
homomorphisms of the roots of unity into the coefficients. -/
noncomputable def kummerTwistEquiv [IsCyclic M] :
    Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E) ≃+ Additive (SmoothH1 ↥K.fixingSubgroup E) :=
  twistEquiv (smul_fixingSubgroup_eq_of_trivial htriv) htrivE (kummerSubHom h htriv) α
    (kummerSubHom_surjective h htriv) hEp (le_of_eq (ker_kummerSubHom h htriv))

@[simp]
theorem kummerTwistEquiv_tmul [IsCyclic M] (a : (↥K)ˣ) (w : M →* E) :
    kummerTwistEquiv h htriv htrivE α hEp (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul w)
      = Additive.ofMul (twistClass (smul_fixingSubgroup_eq_of_trivial htriv) htrivE
        (kummerSubHom h htriv) a w) := rfl

variable [Normal k ↥K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The twisted Kummer class is equivariant** for the Galois group of the base: it acts on the
units of the field by restriction, on the homomorphisms of the coefficients by translation of the
value, and on the cohomology of the subgroup fixing the field by conjugation. -/
theorem conjH1_kummerTwistClass
    (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
      σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
        = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
    (σ : Gal(Ω/k)) (a : (↥K)ˣ) (w : M →* E) :
    conjH1 (normal_fixingSubgroup K) σ
        (twistClass (smul_fixingSubgroup_eq_of_trivial htriv) htrivE (kummerSubHom h htriv) a w)
      = twistClass (smul_fixingSubgroup_eq_of_trivial htriv) htrivE (kummerSubHom h htriv)
        (AlgEquiv.restrictNormalHom (↥K) σ • a) (homSMul σ w) :=
  conjH1_twistClass (normal_fixingSubgroup K) (smul_fixingSubgroup_eq_of_trivial htriv) htrivE
    (kummerSubHom h htriv) (fun σ a => AlgEquiv.restrictNormalHom (↥K) σ • a)
    (conjH1_kummerSubHom h hfix htriv) σ a w

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The twisted Kummer map out of the tensor product is equivariant** for the Galois group of the
base, which acts on the units of the field by restriction and on the homomorphisms of the
coefficients by translation of the argument backwards and of the value forwards. -/
theorem conjH1_kummerTwistMap
    (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
      σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
        = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
    (σ : Gal(Ω/k)) (z : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)) :
    MonoidHom.toAdditive (conjH1 (normal_fixingSubgroup K) σ)
        (twistMap (smul_fixingSubgroup_eq_of_trivial htriv) htrivE (kummerSubHom h htriv) z)
      = twistMap (smul_fixingSubgroup_eq_of_trivial htriv) htrivE (kummerSubHom h htriv)
        (TensorProduct.map
          (MonoidHom.toAdditive (MulDistribMulAction.toMonoidHom ((↥K)ˣ)
            (AlgEquiv.restrictNormalHom (↥K) σ))).toIntLinearMap
          (MonoidHom.toAdditive (homSMulHom σ)).toIntLinearMap z) :=
  conjH1_twistMap (normal_fixingSubgroup K) (smul_fixingSubgroup_eq_of_trivial htriv) htrivE
    (kummerSubHom h htriv)
    (fun σ => MulDistribMulAction.toMonoidHom ((↥K)ˣ) (AlgEquiv.restrictNormalHom (↥K) σ))
    (conjH1_kummerSubHom h hfix htriv) σ z

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The Kummer twist carries the action of the Galois group of the base on the tensor product to
conjugation on the first cohomology**: the units of the field are moved by restriction, the
homomorphisms of the roots of unity into the coefficients by translation of the argument backwards
and of the value forwards. -/
theorem conjH1_kummerTwistEquiv [IsCyclic M]
    (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
      σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
        = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
    (σ : Gal(Ω/k)) (z : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)) :
    MonoidHom.toAdditive (conjH1 (normal_fixingSubgroup K) σ)
        (kummerTwistEquiv h htriv htrivE α hEp z)
      = kummerTwistEquiv h htriv htrivE α hEp
        (TensorProduct.map
          (MonoidHom.toAdditive (MulDistribMulAction.toMonoidHom ((↥K)ˣ)
            (AlgEquiv.restrictNormalHom (↥K) σ))).toIntLinearMap
          (MonoidHom.toAdditive (homSMulHom σ)).toIntLinearMap z) :=
  conjH1_kummerTwistMap h htriv htrivE hfix σ z

end Twist

/-! ### The subgroup fixing the field moves neither factor -/

section Fixing

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The subgroup fixing an intermediate field acts trivially on the units of that field**, so the
Galois action on them is an action of the Galois group of the field itself. -/
theorem smul_units_eq_self_of_mem_fixingSubgroup [Normal k ↥K] {σ : Gal(Ω/k)}
    (hσ : σ ∈ K.fixingSubgroup) (a : (↥K)ˣ) : AlgEquiv.restrictNormalHom (↥K) σ • a = a := by
  have hσ1 : AlgEquiv.restrictNormalHom (↥K) σ = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    exact hσ
  rw [hσ1, one_smul]

variable {M E : Type*} [CommGroup M] [CommGroup E]
variable [MulDistribMulAction Gal(Ω/k) M] [MulDistribMulAction Gal(Ω/k) E]

/-- **The subgroup fixing an intermediate field acts trivially on the homomorphisms of the
coefficients**, when the whole Galois group acts trivially on the roots of unity and the subgroup
acts trivially on the coefficients. -/
theorem homSMul_eq_self_of_mem_fixingSubgroup (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
    (htrivE : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e) {σ : Gal(Ω/k)}
    (hσ : σ ∈ K.fixingSubgroup) (w : M →* E) : homSMul σ w = w :=
  homSMul_eq_self_of_mem (smul_fixingSubgroup_eq_of_trivial (K := K) htriv) htrivE hσ w

end Fixing

end InverseGalois.CFT
