/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerRep
import InverseGalois.CFT.TateCohomology.GroupCongr

/-!
# The twisted Kummer identification over the Galois group of the level

The quotient of an infinite Galois group by the subgroup fixing a normal intermediate field is the
Galois group of that intermediate field: restriction to it is surjective and the subgroup fixing it
is the kernel.  The two groups are therefore the same group presented differently, and the
cohomology of a representation does not notice the difference.

That is the last step of the translation.  The everywhere locally trivial classes of a transgression
are produced on the quotient, because that is the group the inflation of a cochain naturally uses,
while class field theory computes with the Galois group of a finite extension of number fields.
Transporting cohomology along the isomorphism of the two groups carries the twisted Kummer
identification the rest of the way: **the first cohomology of the quotient with values in the first
cohomology of the subgroup becomes the first cohomology of the Galois group of the intermediate
field with coefficients in any representation identified with the units of that field tensored with
the homomorphisms of the roots of unity into the kernel of a lifting problem** — for instance the
tensor product of the representation on the units with a representation of the coefficients, which
is the object the theorems of Tate and Nakayama are stated about.

## Main definitions

* `InverseGalois.CFT.repIsoOfEquivSmul`: an identification of a module with the coefficients of a
  representation, equivariant along an isomorphism of the acting groups, read as an isomorphism of
  representations.
* `InverseGalois.CFT.groupCohomologyEquivOfSmul`, `InverseGalois.CFT.h1MulEquivOfSmul`: **the
  cohomology it carries across**, in every degree and in the first degree respectively.
* `InverseGalois.CFT.quotientFixingSubgroupEquiv`: **the quotient of an infinite Galois group by the
  subgroup fixing a normal intermediate field is the Galois group of that field.**
* `InverseGalois.CFT.kummerFiniteH1Equiv`: **the twisted Kummer identification over the Galois group
  of the intermediate field.**
* `InverseGalois.CFT.kummerFiniteSha1`: the everywhere locally trivial classes read there.

## Main results

* `InverseGalois.CFT.quotientFixingSubgroupEquiv_mk`: the identification of the quotient with the
  Galois group of the intermediate field is restriction.
* `InverseGalois.CFT.sha1Level_eq_bot_iff_finite`: **the everywhere locally trivial classes and
  their reading over the Galois group of the intermediate field vanish together.**

## Tags

Kummer theory, group cohomology, representation, Galois cohomology, local-global principle
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory groupCohomology TensorProduct

/-! ### Cohomology along an isomorphism of the acting groups -/

section Generic

variable {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
variable {T : Type} [AddCommGroup T] [DistribMulAction G T] (B : Rep ℤ G')
variable (φ : T ≃+ ↥B.V) (hφ : ∀ (g : G) (t : T), φ (g • t) = B.ρ (e g) (φ t))

/-- **An identification of a module with the coefficients of a representation, equivariant along an
isomorphism of the acting groups, is an isomorphism of representations** — of the given
representation restricted along the isomorphism, and the representation the module carries. -/
noncomputable def repIsoOfEquivSmul :
    (Action.res _ (e : G →* G')).obj B ≅ Rep.ofDistribMulAction ℤ G T :=
  Action.mkIso φ.symm.toIntLinearEquiv.toModuleIso fun g =>
    ModuleCat.hom_ext (LinearMap.ext fun b => by
      have hb := hφ g (φ.symm b)
      rw [φ.apply_symm_apply] at hb
      show φ.symm (B.ρ (e g) b) = g • φ.symm b
      rw [← hb, φ.symm_apply_apply])

/-- The isomorphism of representations is the given identification, which is a bijection. -/
theorem bijective_repIsoOfEquivSmul :
    Function.Bijective ⇑(repIsoOfEquivSmul e B φ hφ).hom.hom.hom := φ.symm.bijective

/-- **The cohomology of a representation is the cohomology of any module identified with its
coefficients equivariantly along an isomorphism of the acting groups.** -/
noncomputable def groupCohomologyEquivOfSmul (n : ℕ) :
    groupCohomology B n ≅ groupCohomology (Rep.ofDistribMulAction ℤ G T) n :=
  Tate.groupCohomologyCongr e (repIsoOfEquivSmul e B φ hφ).hom
    (bijective_repIsoOfEquivSmul e B φ hφ) n

/-- **The same in the first degree**, written multiplicatively so that it composes with the smooth
first cohomology of a discrete group. -/
noncomputable def h1MulEquivOfSmul :
    Multiplicative ↥(H1 (Rep.ofDistribMulAction ℤ G T)) ≃* Multiplicative ↥(H1 B) :=
  AddEquiv.toMultiplicative
    (groupCohomologyEquivOfSmul e B φ hφ 1).symm.toLinearEquiv.toAddEquiv

end Generic

/-! ### The quotient by the subgroup fixing a normal intermediate field -/

section Level

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable (K : IntermediateField k Ω) [Normal k ↥K]

/-- **The quotient of an infinite Galois group by the subgroup fixing a normal intermediate field is
the Galois group of that field.**  Restriction to the field is surjective and the subgroup fixing it
is the kernel. -/
noncomputable def quotientFixingSubgroupEquiv :
    Gal(Ω/k) ⧸ K.fixingSubgroup ≃* Gal(↥K/k) :=
  QuotientGroup.liftEquiv _ (restrictNormalHom_surjective_level K)
    (IntermediateField.restrictNormalHom_ker K).symm

/-- The identification of the quotient with the Galois group of the intermediate field takes the
class of an automorphism to its restriction. -/
theorem quotientFixingSubgroupEquiv_mk (σ : Gal(Ω/k)) :
    quotientFixingSubgroupEquiv K (QuotientGroup.mk σ)
      = AlgEquiv.restrictNormalHom (↥K) σ := rfl

end Level

/-! ### The twisted Kummer identification over the Galois group of the level -/

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
variable (B : Rep ℤ Gal(↥K/k))
  (φ : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E) ≃+ ↥B.V)
  (hφ : ∀ (g : Gal(Ω/k) ⧸ K.fixingSubgroup) (t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)),
    φ (g • t) = B.ρ (quotientFixingSubgroupEquiv K g) (φ t))

/-- **The twisted Kummer identification over the Galois group of the intermediate field**: the first
cohomology of the quotient with values in the first cohomology of the subgroup fixing the field is
the first cohomology of the Galois group of that field with coefficients in any representation
identified with the units of the field tensored with the homomorphisms of the roots of unity into
the kernel of a lifting problem. -/
noncomputable def kummerFiniteH1Equiv (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k))) :
    SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E)
      ≃* Multiplicative ↥(H1 B) :=
  (kummerSmoothH1Equiv h htriv htrivE α hEp hfix hop).trans
    (h1MulEquivOfSmul (quotientFixingSubgroupEquiv K) B φ hφ)

/-- **The everywhere locally trivial classes, read over the Galois group of the intermediate
field.** -/
noncomputable def kummerFiniteSha1 (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k)))
    (S : Set (Subgroup Gal(Ω/k))) : Subgroup (Multiplicative ↥(H1 B)) :=
  (sha1Level E K.fixingSubgroup hop S).map
    (kummerFiniteH1Equiv h htriv htrivE α hEp hfix B φ hφ hop)

/-- **The everywhere locally trivial classes and their reading over the Galois group of the
intermediate field vanish together**, so the condition under which a locally trivial class of the
second cohomology is inflated from a level is a condition on the first cohomology of a
representation of the Galois group of a finite extension of number fields. -/
theorem sha1Level_eq_bot_iff_finite (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k)))
    (S : Set (Subgroup Gal(Ω/k))) :
    sha1Level E K.fixingSubgroup hop S = ⊥
      ↔ kummerFiniteSha1 h htriv htrivE α hEp hfix B φ hφ hop S = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _
    (kummerFiniteH1Equiv h htriv htrivE α hEp hfix B φ hφ hop).injective).symm

end Kummer

end InverseGalois.CFT
