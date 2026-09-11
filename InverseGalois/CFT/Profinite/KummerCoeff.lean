/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.DiscreteComap
import InverseGalois.CFT.Profinite.KummerRep
import InverseGalois.CFT.Profinite.TransgressionCoeff
import InverseGalois.CFT.Profinite.TwistCoeff

/-!
# Pushing the coefficients forward through the twisted Kummer identification

A homomorphism of the kernels of two lifting problems induces a map of the first cohomology of the
subgroup fixing a normal subextension, and hence a map of the first cohomology of the quotient with
those groups as coefficients.  The twisted Kummer identification reads both of those groups as the
first cohomology of a finite group with coefficients in the units of the subextension tensored with
the homomorphisms of the roots of unity into the kernel.  This file says that the two readings
agree: the map induced by the homomorphism of the kernels is, on the other side of the
identification, the map induced by composition with that homomorphism.

That is what makes the obstruction of a lifting problem answerable.  A locally trivial class of the
second cohomology is inflated from a level as soon as the map of the coefficients annihilates the
everywhere locally trivial classes at that level; the annihilation is a demand on a group of classes
attached to a profinite group, and the identification turns it into the same demand on the first
cohomology of a finite group with coefficients in a tensor product — which is the shape a theorem
about representations of a finite group can meet.

## Main definitions

* `InverseGalois.CFT.repHomOfAddHom`: an equivariant homomorphism of additive modules, read as a
  morphism of the associated representations.
* `InverseGalois.CFT.kummerCoeffRepHom`: **the morphism of representations induced by a
  homomorphism of the kernels**, on the units of the subextension tensored with the homomorphisms
  of the roots of unity.

## Main results

* `InverseGalois.CFT.smoothH1EquivOfAddEquiv_coeffH1`: the identification of the smooth first
  cohomology with the cohomology of a representation is natural in the coefficients.
* `InverseGalois.CFT.kummerSmoothH1Equiv_coeffH1`: **the twisted Kummer identification carries the
  map of the coefficients at the level of the quotient to the map induced by composition.**
* `InverseGalois.CFT.coeffTransH1_inflH1_eq_one_of_map_kummerCoeffRepHom`: **a homomorphism of the
  kernels annihilating one class read through the identification kills the obstruction inflated
  from it.**
* `InverseGalois.CFT.coeffTransH1_inflH1_eq_one_of_kummerSha1`: **a homomorphism of the kernels
  whose induced map of representations annihilates the everywhere locally trivial classes, read
  with the units of the subextension as coefficients, kills every inflated obstruction.**

## Tags

Kummer theory, group cohomology, representation, Galois cohomology, local-global principle
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory groupCohomology TensorProduct

/-! ### An equivariant homomorphism, read in the category of representations -/

section Generic

variable (Q S S' T T' : Type) [Group Q] [CommGroup S] [CommGroup S'] [MulDistribMulAction Q S]
  [MulDistribMulAction Q S'] [AddCommGroup T] [AddCommGroup T'] [DistribMulAction Q T]
  [DistribMulAction Q T']
variable (e : T ≃+ Additive S)
  (he : ∀ (g : Q) (t : T), e (g • t) = Additive.ofMul (g • (e t).toMul))
variable (e' : T' ≃+ Additive S')
  (he' : ∀ (g : Q) (t : T'), e' (g • t) = Additive.ofMul (g • (e' t).toMul))
variable (f : T →+ T') (hf : ∀ (g : Q) (t : T), f (g • t) = g • f t)

/-- **An equivariant homomorphism of additive modules is a morphism of the associated
representations.**  The underlying map is the homomorphism itself; the only content is that it
respects the action. -/
noncomputable def repHomOfAddHom :
    Rep.ofDistribMulAction ℤ Q T ⟶ Rep.ofDistribMulAction ℤ Q T' where
  hom := ModuleCat.ofHom f.toIntLinearMap
  comm g := by
    ext t
    exact hf g t

variable (ψ : S →* S') (hψ : ∀ (g : Q) (s : S), ψ (g • s) = g • ψ s)

/-- **Two identifications intertwining a homomorphism of the multiplicative coefficients with one
of the additive coefficients make a commuting square of representations.** -/
theorem coeffRepHom_comp_repIsoOfAddEquiv_inv
    (hsq : ∀ t : T, e' (f t) = Additive.ofMul (ψ (Additive.toMul (e t)))) :
    discreteCoeffRepHom ψ hψ ≫ (repIsoOfAddEquiv Q S' T' e' he').inv
      = (repIsoOfAddEquiv Q S T e he).inv ≫ repHomOfAddHom Q T T' f hf := by
  ext s
  have h := hsq (e.symm s)
  rw [e.apply_symm_apply] at h
  show e'.symm (Additive.ofMul (ψ (Additive.toMul s))) = f (e.symm s)
  rw [← h, AddEquiv.symm_apply_apply]

variable [TopologicalSpace Q] [DiscreteTopology Q]

/-- **The identification of the smooth first cohomology with the first cohomology of a
representation is natural in the coefficients**: a homomorphism of the multiplicative coefficients
intertwined with one of the additive coefficients induces the same map on either side. -/
theorem smoothH1EquivOfAddEquiv_coeffH1
    (hsq : ∀ t : T, e' (f t) = Additive.ofMul (ψ (Additive.toMul (e t)))) (z : SmoothH1 Q S) :
    smoothH1EquivOfAddEquiv Q S' T' e' he' (coeffH1 ψ hψ z)
      = Multiplicative.ofAdd ((groupCohomology.map (MonoidHom.id Q)
          (repHomOfAddHom Q T T' f hf) 1).hom
          (Multiplicative.toAdd (smoothH1EquivOfAddEquiv Q S T e he z))) := by
  have h2 := congrArg (fun m : Rep.ofMulDistribMulAction Q S ⟶ Rep.ofDistribMulAction ℤ Q T' =>
      (groupCohomology.functor ℤ Q 1).map m)
    (coeffRepHom_comp_repIsoOfAddEquiv_inv Q S S' T T' e he e' he' f hf ψ hψ hsq)
  simp only [groupCohomology.functor_map, groupCohomology.map_id_comp] at h2
  show Multiplicative.ofAdd ((groupCohomology.map (MonoidHom.id Q)
      (repIsoOfAddEquiv Q S' T' e' he').inv 1).hom
      (Multiplicative.toAdd (discreteSmoothH1Hom Q S' (coeffH1 ψ hψ z)))) = _
  rw [discreteSmoothH1Hom_coeffH1]
  show Multiplicative.ofAdd ((groupCohomology.map (MonoidHom.id Q)
      (repIsoOfAddEquiv Q S' T' e' he').inv 1).hom
      ((groupCohomology.map (MonoidHom.id Q) (discreteCoeffRepHom ψ hψ) 1).hom
        (Multiplicative.toAdd (discreteSmoothH1Hom Q S z)))) = _
  refine congrArg Multiplicative.ofAdd ?_
  have h3 := congrArg (fun m : H1 (Rep.ofMulDistribMulAction Q S) ⟶
      H1 (Rep.ofDistribMulAction ℤ Q T') =>
    m.hom (Multiplicative.toAdd (discreteSmoothH1Hom Q S z))) h2
  simpa using h3

end Generic

/-! ### The map of the coefficients through the twisted Kummer identification -/

section Kummer

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω}
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M] {ι : M →* (↥K)ˣ}
variable {p : ℕ} [NeZero p] [MulDistribMulAction Gal(Ω/k) M]
variable {E E' : Type} [CommGroup E] [CommGroup E'] [MulDistribMulAction Gal(Ω/k) E]
  [MulDistribMulAction Gal(Ω/k) E']
variable (h : IsKummerData ↥K Ω M ι p) (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivE : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable (htrivE' : ∀ (x : ↥K.fixingSubgroup) (e : E'), x • e = e)
variable {J J' : Type} [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
variable (α : E ≃* (J → M)) (α' : E' ≃* (J' → M))
variable (hEp : ∀ e : E, e ^ p = 1) (hEp' : ∀ e : E', e ^ p = 1)
variable [Normal k ↥K] [IsCyclic M]
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
variable [ActsTrivially K.fixingSubgroup (M →* E)] [ActsTrivially K.fixingSubgroup (M →* E')]
variable (φ : E →* E') (hφ : ∀ (σ : Gal(Ω/k)) (e : E), φ (σ • e) = σ • φ e)

omit [Normal k ↥K] [ActsTrivially K.fixingSubgroup (M →* E)]
  [ActsTrivially K.fixingSubgroup (M →* E')] in
/-- **The twisted Kummer identification is natural in the kernel**: pushing a class forward along a
homomorphism of the kernels is the identification applied to the identity on the units of the
subextension tensored with composition on the homomorphisms of the roots of unity. -/
theorem coeffH1_kummerTwistEquiv
    (hψ : ∀ (x : ↥K.fixingSubgroup) (e : E), φ (x • e) = x • φ e)
    (z : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)) :
    MonoidHom.toAdditive (coeffH1 φ hψ) (kummerTwistEquiv h htriv htrivE α hEp z)
      = kummerTwistEquiv h htriv htrivE' α' hEp' (tensorCoeffMap M E E' ((↥K)ˣ) φ z) :=
  coeffH1_twistMap (smul_fixingSubgroup_eq_of_trivial htriv) htrivE htrivE'
    (kummerSubHom h htriv) φ z

variable (K M E E') in
/-- **The morphism of representations induced by a homomorphism of the kernels**, on the units of
the subextension tensored with the homomorphisms of the roots of unity into the kernel. -/
noncomputable def kummerCoeffRepHom :
    Rep.ofDistribMulAction ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)
        (Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E))
      ⟶ Rep.ofDistribMulAction ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)
        (Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E')) :=
  repHomOfAddHom _ _ _ (tensorCoeffMap M E E' ((↥K)ˣ) φ).toAddMonoidHom
    (tensorCoeffMap_quotient_smul φ hφ)

/-- **The twisted Kummer identification carries the map of the coefficients at the level of the
quotient to the map induced by composition** with the homomorphism of the kernels. -/
theorem kummerSmoothH1Equiv_coeffH1 (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k)))
    (x : SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E)) :
    kummerSmoothH1Equiv h htriv htrivE' α' hEp' hfix hop
        (coeffQuotTransH1 K.fixingSubgroup φ hφ x)
      = Multiplicative.ofAdd ((groupCohomology.map
          (MonoidHom.id (Gal(Ω/k) ⧸ K.fixingSubgroup)) (kummerCoeffRepHom K M E E' φ hφ) 1).hom
          (Multiplicative.toAdd (kummerSmoothH1Equiv h htriv htrivE α hEp hfix hop x))) := by
  haveI : DiscreteTopology (Gal(Ω/k) ⧸ K.fixingSubgroup) := QuotientGroup.discreteTopology hop
  exact smoothH1EquivOfAddEquiv_coeffH1 _ _ _ _ _ (kummerTwistEquiv h htriv htrivE α hEp)
    (kummerTwistEquiv_smul h htriv htrivE α hEp hfix)
    (kummerTwistEquiv h htriv htrivE' α' hEp')
    (kummerTwistEquiv_smul h htriv htrivE' α' hEp' hfix)
    (tensorCoeffMap M E E' ((↥K)ˣ) φ).toAddMonoidHom (tensorCoeffMap_quotient_smul φ hφ)
    (coeffH1 φ fun (g : ↥K.fixingSubgroup) m => hφ (g : Gal(Ω/k)) m)
    (coeffH1_quotient_smul φ hφ)
    (fun z => (coeffH1_kummerTwistEquiv h htriv htrivE htrivE' α α' hEp hEp' φ _ z).symm) x

include htrivE' α' hEp' in
/-- **A homomorphism of the kernels whose induced map of representations annihilates the class read
through twisted Kummer theory kills the obstruction inflated from that class.**  The two are the
same statement read on either side of the identification. -/
theorem coeffTransH1_inflH1_eq_one_of_map_kummerCoeffRepHom
    (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k)))
    (x : SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E))
    (hzero : (groupCohomology.map (MonoidHom.id (Gal(Ω/k) ⧸ K.fixingSubgroup))
      (kummerCoeffRepHom K M E E' φ hφ) 1).hom
        (Multiplicative.toAdd (kummerSmoothH1Equiv h htriv htrivE α hEp hfix hop x)) = 0) :
    coeffTransH1 K.fixingSubgroup φ hφ
        (inflH1 K.fixingSubgroup (SmoothH1 ↥K.fixingSubgroup E) hop x) = 1 := by
  rw [coeffTransH1_inflH1_eq_one_iff K.fixingSubgroup φ hφ hop x]
  refine (kummerSmoothH1Equiv h htriv htrivE' α' hEp' hfix hop).injective ?_
  rw [_root_.map_one, kummerSmoothH1Equiv_coeffH1 h htriv htrivE htrivE' α α' hEp hEp' hfix φ hφ
    hop x, hzero]
  rfl

include htrivE' α' hEp' in
/-- **A homomorphism of the kernels whose induced map of representations annihilates the everywhere
locally trivial classes kills every inflated obstruction.**  The obstruction attached to a class of
the level is the image of that class, and the identification turns the two into the same
statement. -/
theorem coeffTransH1_inflH1_eq_one_of_kummerSha1
    (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k))) {S : Set (Subgroup Gal(Ω/k))}
    (hzero : ∀ y ∈ kummerSha1 h htriv htrivE α hEp hfix hop S,
      (groupCohomology.map (MonoidHom.id (Gal(Ω/k) ⧸ K.fixingSubgroup))
        (kummerCoeffRepHom K M E E' φ hφ) 1).hom (Multiplicative.toAdd y) = 0)
    (x : SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E))
    (hx : x ∈ sha1Level E K.fixingSubgroup hop S) :
    coeffTransH1 K.fixingSubgroup φ hφ
        (inflH1 K.fixingSubgroup (SmoothH1 ↥K.fixingSubgroup E) hop x) = 1 :=
  coeffTransH1_inflH1_eq_one_of_map_kummerCoeffRepHom h htriv htrivE htrivE' α α' hEp hEp' hfix
    φ hφ hop x (hzero _ (Subgroup.mem_map_of_mem _ hx))

end Kummer

end InverseGalois.CFT
