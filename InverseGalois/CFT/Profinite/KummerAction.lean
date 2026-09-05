/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerTwist
import InverseGalois.CFT.Profinite.TransgressionInflate
import InverseGalois.CFT.Profinite.TwistAction

/-!
# Kummer theory over the Galois group of the finite extension

The twisted Kummer identification matches the tensor product of the units of a finite normal
subextension with the homomorphisms of the roots of unity into the coefficients against the first
cohomology of the subgroup fixing that subextension.  Both sides are moved by the Galois group of
the base, and this file reads that movement as an action of the Galois group of the subextension:
**the Galois group of the base acts on the units of a normal subextension by restriction**, the
subgroup fixing it acts trivially on the units and on the homomorphisms of the coefficients, hence
trivially on the tensor product, and it acts trivially on the first cohomology of itself.  The
quotient therefore acts on both sides and the identification is equivariant for it.

That is what an obstruction is read against.  The obstruction of a lifting problem lives in the
second cohomology of the Galois group of the base with coefficients in the kernel, and the part of
it which is locally trivial is measured by the first cohomology of the Galois group of a finite
subextension with coefficients in the units of that subextension tensored with the homomorphisms of
the roots of unity — a group of the finite level, with no profinite group left in it.

## Main definitions

* `InverseGalois.CFT.restrictUnitsMulDistribMulAction`: **the Galois group of the base acting on
  the units of a normal subextension.**

## Main results

* `InverseGalois.CFT.actsTrivially_units` and `InverseGalois.CFT.actsTrivially_hom`: the subgroup
  fixing the subextension acts trivially on each factor of the tensor product.
* `InverseGalois.CFT.conjH1_kummerTwistEquiv_smul`: the identification carries the action of the
  Galois group of the base to conjugation.
* `InverseGalois.CFT.kummerTwistEquiv_smul`: **the identification is equivariant for the quotient
  by the subgroup fixing the subextension.**

## Tags

Kummer theory, Galois cohomology, twist, group action, quotient
-/

namespace InverseGalois.CFT

open groupCohomology TensorProduct

/-! ### The units of a normal subextension -/

section Units

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [Normal k ↥K]

/-- **The Galois group of the base acts on the units of a normal intermediate field**, an
automorphism acting by its restriction to that field. -/
noncomputable instance restrictUnitsMulDistribMulAction :
    MulDistribMulAction Gal(Ω/k) ((↥K)ˣ) :=
  MulDistribMulAction.compHom ((↥K)ˣ) (AlgEquiv.restrictNormalHom (↥K))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- The Galois group of the base acts on the units of a normal intermediate field by
restriction. -/
theorem restrictUnits_smul (σ : Gal(Ω/k)) (a : (↥K)ˣ) :
    σ • a = AlgEquiv.restrictNormalHom (↥K) σ • a := rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The subgroup fixing a normal intermediate field acts trivially on its units**, so the
quotient by it acts there. -/
instance actsTrivially_units : ActsTrivially K.fixingSubgroup ((↥K)ˣ) :=
  ⟨fun _ hn a => smul_units_eq_self_of_mem_fixingSubgroup hn a⟩

end Units

/-! ### The homomorphisms of the coefficients -/

section Hom

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω}
variable {M E : Type*} [CommGroup M] [CommGroup E]
variable [MulDistribMulAction Gal(Ω/k) M] [MulDistribMulAction Gal(Ω/k) E]

/-- **The subgroup fixing an intermediate field acts trivially on the homomorphisms of the
coefficients**, when the whole Galois group acts trivially on the roots of unity and the subgroup
acts trivially on the coefficients. -/
theorem actsTrivially_hom (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
    (htrivE : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e) :
    ActsTrivially K.fixingSubgroup (M →* E) :=
  ⟨fun _ hn w => homSMul_eq_self_of_mem_fixingSubgroup htriv htrivE hn w⟩

end Hom

/-! ### The identification as a map of modules -/

section Twist

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k ↥K]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M] {ι : M →* (↥K)ˣ}
variable {p : ℕ} [NeZero p] [MulDistribMulAction Gal(Ω/k) M]
variable {E : Type*} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
variable (h : IsKummerData ↥K Ω M ι p) (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivE : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable {J : Type*} [Fintype J] [DecidableEq J] (α : E ≃* (J → M))
variable (hEp : ∀ e : E, e ^ p = 1) [Normal k ↥K] [IsCyclic M]
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
include hfix in
/-- **The Kummer twist carries the action of the Galois group of the base on the tensor product to
conjugation on the first cohomology**, the action on the tensor product being the one which moves
each factor. -/
theorem conjH1_kummerTwistEquiv_smul (σ : Gal(Ω/k))
    (z : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)) :
    MonoidHom.toAdditive (conjH1 (normal_fixingSubgroup K) σ)
        (kummerTwistEquiv h htriv htrivE α hEp z)
      = kummerTwistEquiv h htriv htrivE α hEp (σ • z) :=
  conjH1_twistMap_smul (normal_fixingSubgroup K) (smul_fixingSubgroup_eq_of_trivial htriv) htrivE
    (kummerSubHom h htriv) (conjH1_kummerSubHom h hfix htriv) σ z

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
include hfix in
/-- **Kummer theory over the Galois group of the finite extension**: the identification of the
tensor product of the units of a normal subextension with the homomorphisms of the roots of unity
into the coefficients against the first cohomology of the subgroup fixing that subextension is
equivariant for the quotient by that subgroup. -/
theorem kummerTwistEquiv_smul [ActsTrivially K.fixingSubgroup (M →* E)]
    (g : Gal(Ω/k) ⧸ K.fixingSubgroup) (z : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)) :
    kummerTwistEquiv h htriv htrivE α hEp (g • z)
      = Additive.ofMul (g • (kummerTwistEquiv h htriv htrivE α hEp z).toMul) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  exact (conjH1_kummerTwistEquiv_smul h htriv htrivE α hEp hfix σ z).symm

end Twist

end InverseGalois.CFT
