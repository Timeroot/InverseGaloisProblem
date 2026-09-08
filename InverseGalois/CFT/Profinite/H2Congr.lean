/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.FixingSubgroup
import InverseGalois.CFT.Profinite.Res

/-!
# The second cohomology transported along an isomorphism of topological groups

Substituting one variable for another in a two cochain is undone by substituting back, so an
isomorphism of topological groups which is smooth in both directions and matches the two actions on
the coefficients carries the second cohomology of one group isomorphically onto that of the other.
This is the statement of the previous file for the first cohomology, in the next degree, and the
proof sees only the substitution.

The use here is the Galois group over an intermediate field.  Galois theory identifies it with the
subgroup of the big Galois group which fixes that field, and the identification is smooth in both
directions, so **a class of the second cohomology of the big group dies over the intermediate field
exactly when it dies on the subgroup which fixes it.**  One side is what a local-global principle
delivers - the everywhere locally trivial classes of a number field vanish over a field carrying
enough roots of unity - and the other side is what a transgression argument consumes, since a
transgression is built from a primitive of the cocycle on the kernel of the projection to a finite
level.  The two are the same statement, and this file says so.

## Main definitions

* `InverseGalois.CFT.smoothH2Congr`: **transport of the second cohomology along an isomorphism of
  topological groups.**

## Main results

* `InverseGalois.CFT.isSmoothHom_galSubHom`: reading an automorphism over an intermediate field as
  one over the base is a smooth homomorphism.
* `InverseGalois.CFT.comapH2_galSubHom_eq`: the class read over the intermediate field is the class
  restricted to the subgroup which fixes it, transported.
* `InverseGalois.CFT.resH2_fixingSubgroup_eq_one_iff`: **a class dies over an intermediate field
  exactly when it dies on the subgroup which fixes that field.**

## Tags

profinite group, Galois cohomology, fixing subgroup, second cohomology, transport
-/

namespace InverseGalois.CFT

open IntermediateField groupCohomology

/-! ### Transport along an isomorphism -/

section Transport

variable {G Q : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction Q M]

/-- **The second cohomology transported along an isomorphism of topological groups** which is
smooth in both directions and matches the two actions on the coefficients.  Substituting one
variable for another in a two cochain is undone by substituting back. -/
def smoothH2Congr (e : G ≃* Q) (he : ∀ (g : G) (m : M), g • m = e g • m)
    (hs : IsSmoothHom e.toMonoidHom) (hs' : IsSmoothHom e.symm.toMonoidHom) :
    SmoothH2 Q M ≃* SmoothH2 G M where
  toFun := comapH2 e.toMonoidHom he hs
  invFun := comapH2 e.symm.toMonoidHom (smul_symm_of_smul e he) hs'
  left_inv z := by
    obtain ⟨a, ha, has, rfl⟩ := smoothH2Mk_surjective z
    rw [comapH2_smoothH2Mk, comapH2_smoothH2Mk]
    refine smoothH2Mk_congr _ _ ha has (funext fun p => ?_)
    show a (e (e.symm p.1), e (e.symm p.2)) = a p
    rw [e.apply_symm_apply, e.apply_symm_apply]
  right_inv z := by
    obtain ⟨a, ha, has, rfl⟩ := smoothH2Mk_surjective z
    rw [comapH2_smoothH2Mk, comapH2_smoothH2Mk]
    refine smoothH2Mk_congr _ _ ha has (funext fun p => ?_)
    show a (e.symm (e p.1), e.symm (e p.2)) = a p
    rw [e.symm_apply_apply, e.symm_apply_apply]
  map_mul' x y := _root_.map_mul _ x y

/-- The transported class is computed on cocycles. -/
theorem smoothH2Congr_smoothH2Mk (e : G ≃* Q) (he : ∀ (g : G) (m : M), g • m = e g • m)
    (hs : IsSmoothHom e.toMonoidHom) (hs' : IsSmoothHom e.symm.toMonoidHom) {a : Q × Q → M}
    (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a) :
    smoothH2Congr e he hs hs' (smoothH2Mk a ha has)
      = smoothH2Mk (comap₂ e.toMonoidHom a) (isMulCocycle₂_comap₂ e.toMonoidHom he ha)
        (hs.isSmooth₂ has) := rfl

end Transport

/-! ### The Galois group over an intermediate field -/

section Galois

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable (K : IntermediateField k Ω)
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M]
  [MulDistribMulAction Gal(Ω/↥K) M]

/-- **Reading an automorphism over an intermediate field as one over the base is a smooth
homomorphism**, so it carries continuous cochains of the big group to continuous cochains of the
Galois group over the field. -/
theorem isSmoothHom_galSubHom : IsSmoothHom (galSubHom K) :=
  isSmoothHom_of_continuous (continuous_galSubHom K)

variable (hπ : ∀ (g : Gal(Ω/↥K)) (m : M), g • m = galSubHom K g • m)

include hπ

omit [IsGalois k Ω] in
/-- The Galois correspondence for an intermediate field matches the action of the Galois group over
it with the action of the subgroup which fixes it. -/
theorem smul_fixingSubgroupEquiv_symm (g : Gal(Ω/↥K)) (m : M) :
    g • m = (fixingSubgroupEquiv K).symm g • m := hπ g m

/-- **The second cohomology over an intermediate field is the second cohomology of the subgroup
which fixes it**, the Galois correspondence being smooth in both directions. -/
def galSubH2Congr : SmoothH2 ↥K.fixingSubgroup M ≃* SmoothH2 Gal(Ω/↥K) M :=
  smoothH2Congr (fixingSubgroupEquiv K).symm (smul_fixingSubgroupEquiv_symm K hπ)
    (isSmoothHom_fixingSubgroupEquiv_symm K)
    ((MulEquiv.symm_symm (fixingSubgroupEquiv K)).symm ▸ isSmoothHom_fixingSubgroupEquiv K)

/-- **The class read over an intermediate field is the class restricted to the subgroup which fixes
it**, transported along the Galois correspondence: both are computed by the same cocycle. -/
theorem comapH2_galSubHom_eq (z : SmoothH2 Gal(Ω/k) M) :
    comapH2 (galSubHom K) hπ (isSmoothHom_galSubHom K) z
      = galSubH2Congr K hπ (resH2 K.fixingSubgroup z) := by
  obtain ⟨a, ha, has, rfl⟩ := smoothH2Mk_surjective z
  rfl

/-- **A class of the second cohomology dies over an intermediate field exactly when it dies on the
subgroup which fixes that field.** -/
theorem resH2_fixingSubgroup_eq_one_iff (z : SmoothH2 Gal(Ω/k) M) :
    resH2 K.fixingSubgroup z = 1
      ↔ comapH2 (galSubHom K) hπ (isSmoothHom_galSubHom K) z = 1 := by
  rw [comapH2_galSubHom_eq K hπ z, map_eq_one_iff _ (galSubH2Congr K hπ).injective]

/-- **A class of the second cohomology which dies over an intermediate field dies on the subgroup
which fixes that field.** -/
theorem resH2_fixingSubgroup_eq_one {z : SmoothH2 Gal(Ω/k) M}
    (h : comapH2 (galSubHom K) hπ (isSmoothHom_galSubHom K) z = 1) :
    resH2 K.fixingSubgroup z = 1 :=
  (resH2_fixingSubgroup_eq_one_iff K hπ z).2 h

end Galois

end InverseGalois.CFT
