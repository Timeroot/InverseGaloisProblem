/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.H1Conj
import InverseGalois.CFT.Profinite.Krull

/-!
# The Galois group over an intermediate field is the subgroup which fixes it, topologically

An automorphism of a Galois extension which fixes an intermediate field is the same thing as an
automorphism of the extension over that field, and Galois theory records this as an isomorphism of
groups.  Each side carries a topology: the subgroup of the big Galois group has the topology it
inherits, and the Galois group over the intermediate field has its own, built from the finite
extensions of that field.  **The isomorphism respects both.**

One direction is a matter of enlarging a finite extension of the base until it contains the
intermediate field, at which point it becomes a finite extension of that field too; the other is a
matter of shrinking a finite extension of the intermediate field to a finite extension of the base
inside it, which is what the Krull topology of the big group provides.  Neither direction is formal:
the two topologies are defined from different lattices of finite extensions, and the content is that
those lattices are cofinal in each other.

The consequence used elsewhere is that continuous cochains match up, so the first cohomology of the
Galois group over the intermediate field is the first cohomology of the subgroup which fixes it.
That is proved here for an arbitrary isomorphism of topological groups which is smooth in both
directions, since the argument sees only the substitution of one variable for another.

## Main definitions

* `InverseGalois.CFT.galSubHom`: an automorphism over an intermediate field, read as an
  automorphism over the base.
* `InverseGalois.CFT.smoothH1Congr`: **transport of the first cohomology along an isomorphism
  of topological groups.**

## Main results

* `InverseGalois.CFT.continuous_galSubHom`: an automorphism over an intermediate field depends
  continuously on itself, read over the base.
* `InverseGalois.CFT.isSmoothHom_fixingSubgroupEquiv`: the Galois correspondence for an
  intermediate field is smooth.
* `InverseGalois.CFT.isSmoothHom_fixingSubgroupEquiv_symm`: **so is its inverse.**

## Tags

infinite Galois theory, Krull topology, fixing subgroup, profinite group, Galois cohomology
-/

namespace InverseGalois.CFT

open IntermediateField groupCohomology

/-! ### The two topologies on the Galois group over an intermediate field -/

section Topology

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k ↥K]

/-- An automorphism of the extension over an intermediate field, read as an automorphism over the
base which fixes that field. -/
def galSubHom : Gal(Ω/↥K) →* Gal(Ω/k) :=
  K.fixingSubgroup.subtype.comp (fixingSubgroupEquiv K).symm.toMonoidHom

omit [IsGalois k Ω] [FiniteDimensional k ↥K] in
/-- Reading an automorphism over an intermediate field as one over the base does not change it. -/
theorem galSubHom_apply (τ : Gal(Ω/↥K)) (x : Ω) : galSubHom K τ x = τ x := rfl

omit [IsGalois k Ω] [FiniteDimensional k ↥K] in
/-- The Galois correspondence for an intermediate field, followed by the inclusion of the subgroup
which fixes it. -/
theorem coe_fixingSubgroupEquiv_symm (τ : Gal(Ω/↥K)) :
    (((fixingSubgroupEquiv K).symm τ : ↥K.fixingSubgroup) : Gal(Ω/k)) = galSubHom K τ := rfl

omit [IsGalois k Ω] in
/-- **An automorphism over an intermediate field depends continuously on itself, read over the
base.**  A finite extension of the base is enlarged by the intermediate field, which is finite over
the base, so the result is finite over the intermediate field as well; an automorphism fixing the
enlargement fixes the original extension. -/
theorem continuous_galSubHom : Continuous (galSubHom K) := by
  refine continuous_of_continuousAt_one (galSubHom K) ?_
  rw [ContinuousAt, map_one, Filter.tendsto_def]
  intro V hV
  obtain ⟨F, hfin, hle⟩ := (krullTopology_mem_nhds_one_iff k Ω V).1 hV
  haveI := hfin
  set E : IntermediateField ↥K Ω := IntermediateField.extendScalars (le_sup_right : K ≤ F ⊔ K)
    with hE
  have hEfin : FiniteDimensional ↥K ↥E := by
    have h1 : FiniteDimensional k ↥(F ⊔ K) := inferInstance
    have h2 : FiniteDimensional k ↥E := h1
    exact Module.Finite.right k ↥K ↥E
  haveI := hEfin
  refine Filter.mem_of_superset (E.fixingSubgroup_isOpen.mem_nhds E.fixingSubgroup.one_mem)
    fun τ hτ => hle ?_
  show galSubHom K τ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hxE : x ∈ E := (le_sup_left : F ≤ F ⊔ K) hx
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x hxE

omit [IsGalois k Ω] in
/-- **The inverse of the Galois correspondence for an intermediate field is continuous.** -/
theorem continuous_fixingSubgroupEquiv_symm :
    Continuous ((fixingSubgroupEquiv K).symm : Gal(Ω/↥K) → ↥K.fixingSubgroup) :=
  continuous_induced_rng.2 (continuous_galSubHom K)

omit [IsGalois k Ω] in
/-- **The inverse of the Galois correspondence for an intermediate field is smooth**, so it carries
continuous cochains on the subgroup to continuous cochains on the Galois group over the field. -/
theorem isSmoothHom_fixingSubgroupEquiv_symm :
    IsSmoothHom ((fixingSubgroupEquiv K).symm.toMonoidHom) :=
  isSmoothHom_of_continuous (continuous_fixingSubgroupEquiv_symm K)

/-- **The Galois correspondence for an intermediate field is smooth.**  An open subgroup of the
Galois group over the intermediate field contains the automorphisms fixing a finite extension of
it, which is a finite extension of the base as well, and the Krull topology of the big group makes
the automorphisms fixing it a neighbourhood of the unit. -/
theorem isSmoothHom_fixingSubgroupEquiv :
    IsSmoothHom ((fixingSubgroupEquiv K).toMonoidHom) := by
  intro N hN
  obtain ⟨E, hfin, hgal, hle⟩ := exists_fixingSubgroup_le hN
  haveI := hfin
  have hfin' : FiniteDimensional k ↥(E.restrictScalars k) := by
    have : FiniteDimensional k ↥E := Module.Finite.trans (↥K) ↥E
    exact this
  haveI := hfin'
  obtain ⟨E', hfin', hnorm', hle'⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal k Ω ((E.restrictScalars k).fixingSubgroup : Set _)).1
      ((E.restrictScalars k).fixingSubgroup_isOpen.mem_nhds
        (E.restrictScalars k).fixingSubgroup.one_mem)
  haveI := hfin'
  haveI := hnorm'
  refine ⟨(E'.fixingSubgroup).comap K.fixingSubgroup.subtype,
    isOpenNormal_comap_subtype _ (isOpenNormal_fixingSubgroup E'), fun x hx => ?_⟩
  rw [Subgroup.mem_comap]
  refine hle ?_
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hy' : y ∈ E.restrictScalars k := hy
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hle' (Subgroup.mem_comap.1 hx)) y hy'

end Topology

/-! ### Transport of the first cohomology along an isomorphism -/

section Transport

variable {G Q : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction Q M]

omit [TopologicalSpace G] [TopologicalSpace Q] in
/-- If an isomorphism of groups matches the two actions on a module then so does its inverse. -/
theorem smul_symm_of_smul (e : G ≃* Q) (he : ∀ (g : G) (m : M), g • m = e g • m) (q : Q) (m : M) :
    q • m = e.symm q • m := by
  rw [he (e.symm q) m, e.apply_symm_apply]

/-- **The first cohomology transported along an isomorphism of topological groups** which is smooth
in both directions and matches the two actions on the coefficients.  Substituting one variable for
another in a cochain is undone by substituting back. -/
def smoothH1Congr (e : G ≃* Q) (he : ∀ (g : G) (m : M), g • m = e g • m)
    (hs : IsSmoothHom e.toMonoidHom) (hs' : IsSmoothHom e.symm.toMonoidHom) :
    SmoothH1 Q M ≃* SmoothH1 G M where
  toFun := comapH1 e.toMonoidHom he hs
  invFun := comapH1 e.symm.toMonoidHom (smul_symm_of_smul e he) hs'
  left_inv z := by
    obtain ⟨u, hu, hus, rfl⟩ := smoothH1Mk_surjective z
    rw [comapH1_smoothH1Mk, comapH1_smoothH1Mk]
    exact smoothH1Mk_congr (funext fun q => congrArg u (e.apply_symm_apply q)) _ _ _ _
  right_inv z := by
    obtain ⟨u, hu, hus, rfl⟩ := smoothH1Mk_surjective z
    rw [comapH1_smoothH1Mk, comapH1_smoothH1Mk]
    exact smoothH1Mk_congr (funext fun g => congrArg u (e.symm_apply_apply g)) _ _ _ _
  map_mul' x y := _root_.map_mul _ x y

/-- The transported class is computed on cocycles. -/
theorem smoothH1Congr_smoothH1Mk (e : G ≃* Q) (he : ∀ (g : G) (m : M), g • m = e g • m)
    (hs : IsSmoothHom e.toMonoidHom) (hs' : IsSmoothHom e.symm.toMonoidHom) {u : Q → M}
    (hu : IsMulCocycle₁ u) (hus : IsSmooth₁ u) :
    smoothH1Congr e he hs hs' (smoothH1Mk u hu hus)
      = smoothH1Mk (fun g => u (e g)) (isMulCocycle₁_comap₁ e.toMonoidHom he hu) (hs.isSmooth₁ hus)
  := rfl

end Transport

end InverseGalois.CFT
