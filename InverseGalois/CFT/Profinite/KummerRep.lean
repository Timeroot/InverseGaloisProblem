/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Discrete
import InverseGalois.CFT.Profinite.KummerAction

/-!
# The twisted Kummer identification as an isomorphism of representations

The first cohomology of the subgroup fixing a normal subextension, with coefficients in the kernel
of a lifting problem, is the tensor product of the units of that subextension with the
homomorphisms of the roots of unity into the kernel, and the Galois group of the base moves the two
sides alike.  This file says that in the language of representations: the two sides are isomorphic
objects of the category of integral representations of the quotient by the subgroup, and so have
the same cohomology.

The point of saying it there is that everything above the subextension is written with smooth
cochains on an infinite Galois group, while class field theory — the theorems of Tate and of
Nakayama, and the duality behind a local-global principle — is written with representations of a
finite group.  A group of classes which the first language produces can be handed to the second
exactly here: **the everywhere locally trivial classes of the first cohomology of the quotient,
with values in the first cohomology of the subgroup, become a subgroup of the first cohomology of a
finite group with coefficients in the units of a field tensored with a finite module, and the two
readings vanish together.**

## Main definitions

* `InverseGalois.CFT.repIsoOfAddEquiv`: an equivariant identification of an additive module with
  the additive copy of a multiplicative one, read as an isomorphism of representations.
* `InverseGalois.CFT.kummerRepIso`: **the twisted Kummer identification, as an isomorphism of
  representations of the quotient by the subgroup fixing the subextension.**
* `InverseGalois.CFT.kummerSha1`: the everywhere locally trivial classes at the level of that
  quotient, read with the units of the subextension as coefficients.

## Main results

* `InverseGalois.CFT.smoothH1EquivOfAddEquiv`: the smooth first cohomology of a discrete group with
  multiplicative coefficients is the first cohomology of any representation identified with them.
* `InverseGalois.CFT.kummerSmoothH1Equiv`: **the first cohomology of the quotient with values in
  the first cohomology of the subgroup fixing the subextension is the first cohomology of the same
  quotient with coefficients in the units of the subextension tensored with the homomorphisms of
  the roots of unity into the kernel.**
* `InverseGalois.CFT.sha1Level_eq_bot_iff`: **the two readings of the everywhere locally trivial
  classes vanish together.**

## Tags

Kummer theory, group cohomology, representation, Galois cohomology, local-global principle
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory groupCohomology TensorProduct

/-! ### An equivariant identification, read in the category of representations -/

section Generic

variable (Q S T : Type) [Group Q] [CommGroup S] [MulDistribMulAction Q S]
  [AddCommGroup T] [DistribMulAction Q T]
variable (e : T ≃+ Additive S)
  (he : ∀ (g : Q) (t : T), e (g • t) = Additive.ofMul (g • (e t).toMul))

/-- **An equivariant identification of an additive module with the additive copy of a
multiplicative one is an isomorphism of representations.**  Both sides are the same abelian group
with the same action of the group; the only content is that the identification respects it. -/
noncomputable def repIsoOfAddEquiv :
    Rep.ofDistribMulAction ℤ Q T ≅ Rep.ofMulDistribMulAction Q S :=
  Action.mkIso e.toIntLinearEquiv.toModuleIso fun g =>
    ModuleCat.hom_ext (LinearMap.ext fun t => he g t)

/-- The isomorphism of representations is the given identification. -/
theorem repIsoOfAddEquiv_hom_apply (t : T) : (repIsoOfAddEquiv Q S T e he).hom.hom t = e t := rfl

/-- Its inverse is the inverse identification. -/
theorem repIsoOfAddEquiv_inv_apply (s : Additive S) :
    (repIsoOfAddEquiv Q S T e he).inv.hom s = e.symm s := rfl

variable [TopologicalSpace Q] [DiscreteTopology Q]

/-- **The smooth first cohomology of a discrete group is the first cohomology of any representation
identified with its coefficients.**  On a discrete group every cochain is smooth, so the smooth
cohomology is the cohomology of the additive copy of the coefficients, and an equivariant
identification of that copy carries the cohomology across. -/
noncomputable def smoothH1EquivOfAddEquiv :
    SmoothH1 Q S ≃* Multiplicative ↥(H1 (Rep.ofDistribMulAction ℤ Q T)) :=
  (discreteSmoothH1Equiv Q S).trans
    (AddEquiv.toMultiplicative
      (((groupCohomology.functor ℤ Q 1).mapIso
        (repIsoOfAddEquiv Q S T e he)).symm.toLinearEquiv.toAddEquiv))

end Generic

/-! ### Kummer theory over the Galois group of the subextension -/

section Kummer

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω}
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M] {ι : M →* (↥K)ˣ}
variable {p : ℕ} [NeZero p] [MulDistribMulAction Gal(Ω/k) M]
variable {E : Type} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
variable (h : IsKummerData ↥K Ω M ι p) (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivE : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable {J : Type} [Fintype J] [DecidableEq J] (α : E ≃* (J → M))
variable (hEp : ∀ e : E, e ^ p = 1) [Normal k ↥K] [IsCyclic M]
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
variable [ActsTrivially K.fixingSubgroup (M →* E)]

/-- **The twisted Kummer identification, as an isomorphism of representations of the quotient by
the subgroup fixing the subextension.**  The tensor product of the units of the subextension with
the homomorphisms of the roots of unity into the kernel of a lifting problem is, as a module over
that quotient, the first cohomology of the subgroup with coefficients in the kernel. -/
noncomputable def kummerRepIso :
    Rep.ofDistribMulAction ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)
        (Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E))
      ≅ Rep.ofMulDistribMulAction (Gal(Ω/k) ⧸ K.fixingSubgroup)
        (SmoothH1 ↥K.fixingSubgroup E) :=
  repIsoOfAddEquiv _ _ _ (kummerTwistEquiv h htriv htrivE α hEp)
    (kummerTwistEquiv_smul h htriv htrivE α hEp hfix)

/-- **The first cohomology of the Galois group of a normal subextension with values in the first
cohomology of the subgroup fixing it is the first cohomology of the same group with coefficients in
the units of the subextension tensored with the homomorphisms of the roots of unity into the
kernel.**  This is the group a local-global principle in the first cohomology computes, written on
the side of class field theory. -/
noncomputable def kummerSmoothH1Equiv (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k))) :
    SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E)
      ≃* Multiplicative ↥(H1 (Rep.ofDistribMulAction ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)
        (Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)))) :=
  haveI : DiscreteTopology (Gal(Ω/k) ⧸ K.fixingSubgroup) := QuotientGroup.discreteTopology hop
  smoothH1EquivOfAddEquiv _ _ _ (kummerTwistEquiv h htriv htrivE α hEp)
    (kummerTwistEquiv_smul h htriv htrivE α hEp hfix)

/-- **The everywhere locally trivial classes at the level of the quotient, read with the units of
the subextension as coefficients.** -/
noncomputable def kummerSha1 (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k)))
    (S : Set (Subgroup Gal(Ω/k))) :
    Subgroup (Multiplicative ↥(H1 (Rep.ofDistribMulAction ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)
      (Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E))))) :=
  (sha1Level E K.fixingSubgroup hop S).map (kummerSmoothH1Equiv h htriv htrivE α hEp hfix hop)

/-- **The two readings of the everywhere locally trivial classes vanish together**, so the
condition under which a locally trivial class of the second cohomology is inflated from a level is
a condition on the first cohomology of a finite group with coefficients in the units of a field. -/
theorem sha1Level_eq_bot_iff (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k)))
    (S : Set (Subgroup Gal(Ω/k))) :
    sha1Level E K.fixingSubgroup hop S = ⊥
      ↔ kummerSha1 h htriv htrivE α hEp hfix hop S = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _
    (kummerSmoothH1Equiv h htriv htrivE α hEp hfix hop).injective).symm

end Kummer

end InverseGalois.CFT
