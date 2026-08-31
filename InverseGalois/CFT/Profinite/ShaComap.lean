/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Res

/-!
# Local triviality travels along a homomorphism

A continuous homomorphism of profinite groups carries a subgroup of the source into a subgroup of
the target whenever the images land there, and the square formed by the two restrictions and the
two maps induced in cohomology commutes: both composites replace a cochain by its values on the
images of the subgroup of the source.  Both composites are literally the same function of a
representing cocycle, so the square commutes on the nose.

That is all one needs to move the everywhere locally trivial classes along the homomorphism.  If
every subgroup of a family in the source is carried into some subgroup of a family in the target,
then a class dying on the second family pulls back to a class dying on the first.  For a subfield
of a Galois extension this says the everywhere locally trivial classes of the base restrict to
everywhere locally trivial classes of the subfield, the decomposition subgroups upstairs sitting
inside the decomposition subgroups downstairs.

## Main definitions

* `InverseGalois.CFT.subgroupHom`: the homomorphism between subgroups induced by a homomorphism
  carrying the one into the other.

## Main results

* `InverseGalois.CFT.resH1_comapH1`, `InverseGalois.CFT.resH2_comapH2`: **restriction to a subgroup
  commutes with the map induced by a continuous homomorphism.**
* `InverseGalois.CFT.comapH1_mem_sha1`, `InverseGalois.CFT.comapH2_mem_sha2`: **a class dying on
  every subgroup of a family pulls back to a class dying on every subgroup of a family carried into
  it.**

## Tags

profinite group, Galois cohomology, restriction, functoriality, local-global principle
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### The induced homomorphism of subgroups -/

section SubgroupHom

variable {G Q : Type*} [Group G] [Group Q]

/-- The homomorphism between two subgroups induced by a homomorphism of the ambient groups carrying
the one into the other. -/
def subgroupHom (π : G →* Q) {D' : Subgroup G} {D : Subgroup Q} (hle : ∀ x ∈ D', π x ∈ D) :
    ↥D' →* ↥D where
  toFun x := ⟨π (x : G), hle (x : G) x.2⟩
  map_one' := Subtype.ext (map_one π)
  map_mul' x y := Subtype.ext (map_mul π (x : G) (y : G))

@[simp]
theorem subgroupHom_apply (π : G →* Q) {D' : Subgroup G} {D : Subgroup Q}
    (hle : ∀ x ∈ D', π x ∈ D) (x : ↥D') : (subgroupHom π hle x : Q) = π (x : G) := rfl

variable [TopologicalSpace G] [TopologicalSpace Q]

/-- The induced homomorphism of subgroups is continuous for the subspace topologies. -/
theorem continuous_subgroupHom {π : G →* Q} (hc : Continuous π) {D' : Subgroup G}
    {D : Subgroup Q} (hle : ∀ x ∈ D', π x ∈ D) : Continuous (subgroupHom π hle) :=
  Continuous.subtype_mk (hc.comp continuous_subtype_val) _

/-- **The induced homomorphism of subgroups is smooth.** -/
theorem isSmoothHom_subgroupHom {π : G →* Q} (hc : Continuous π) {D' : Subgroup G}
    {D : Subgroup Q} (hle : ∀ x ∈ D', π x ∈ D) : IsSmoothHom (subgroupHom π hle) :=
  isSmoothHom_of_continuous (continuous_subgroupHom hc hle)

end SubgroupHom

/-! ### Restriction commutes with the induced map in cohomology -/

section Square

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
  [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction Q M]
variable {π : G →* Q} (hπ : ∀ (g : G) (m : M), g • m = π g • m) (hsm : IsSmoothHom π)

include hπ hsm

/-- **Restriction to a subgroup commutes with the map in the first cohomology induced by a
continuous homomorphism.** -/
theorem resH1_comapH1 (hc : Continuous π) {D' : Subgroup G} {D : Subgroup Q}
    (hle : ∀ x ∈ D', π x ∈ D) (z : SmoothH1 Q M) :
    resH1 D' (comapH1 π hπ hsm z)
      = comapH1 (subgroupHom π hle) (fun x m => hπ (x : G) m)
          (isSmoothHom_subgroupHom hc hle) (resH1 D z) := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  rfl

/-- **Restriction to a subgroup commutes with the map in the second cohomology induced by a
continuous homomorphism.** -/
theorem resH2_comapH2 (hc : Continuous π) {D' : Subgroup G} {D : Subgroup Q}
    (hle : ∀ x ∈ D', π x ∈ D) (z : SmoothH2 Q M) :
    resH2 D' (comapH2 π hπ hsm z)
      = comapH2 (subgroupHom π hle) (fun x m => hπ (x : G) m)
          (isSmoothHom_subgroupHom hc hle) (resH2 D z) := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective z
  rfl

/-! ### The locally trivial classes travel -/

/-- **A class of the first cohomology dying on every subgroup of a family pulls back to a class
dying on every subgroup of a family carried into it.** -/
theorem comapH1_mem_sha1 (hc : Continuous π) {S : Set (Subgroup Q)} {S' : Set (Subgroup G)}
    (hS : ∀ D' ∈ S', ∃ D ∈ S, ∀ x ∈ D', π x ∈ D) {z : SmoothH1 Q M} (hz : z ∈ sha1 M S) :
    comapH1 π hπ hsm z ∈ sha1 M S' := by
  rw [mem_sha1]
  intro D' hD'
  obtain ⟨D, hD, hle⟩ := hS D' hD'
  rw [resH1_comapH1 hπ hsm hc hle, mem_sha1.1 hz D hD, map_one]

/-- **A class of the second cohomology dying on every subgroup of a family pulls back to a class
dying on every subgroup of a family carried into it.** -/
theorem comapH2_mem_sha2 (hc : Continuous π) {S : Set (Subgroup Q)} {S' : Set (Subgroup G)}
    (hS : ∀ D' ∈ S', ∃ D ∈ S, ∀ x ∈ D', π x ∈ D) {z : SmoothH2 Q M} (hz : z ∈ sha2 M S) :
    comapH2 π hπ hsm z ∈ sha2 M S' := by
  rw [mem_sha2]
  intro D' hD'
  obtain ⟨D, hD, hle⟩ := hS D' hD'
  rw [resH2_comapH2 hπ hsm hc hle, mem_sha2.1 hz D hD, map_one]

/-- The locally trivial classes of the first cohomology map into the locally trivial classes. -/
theorem sha1_le_comap_sha1 (hc : Continuous π) {S : Set (Subgroup Q)} {S' : Set (Subgroup G)}
    (hS : ∀ D' ∈ S', ∃ D ∈ S, ∀ x ∈ D', π x ∈ D) :
    sha1 M S ≤ (sha1 M S').comap (comapH1 π hπ hsm) :=
  fun _ hz => Subgroup.mem_comap.2 (comapH1_mem_sha1 hπ hsm hc hS hz)

/-- The locally trivial classes of the second cohomology map into the locally trivial classes. -/
theorem sha2_le_comap_sha2 (hc : Continuous π) {S : Set (Subgroup Q)} {S' : Set (Subgroup G)}
    (hS : ∀ D' ∈ S', ∃ D ∈ S, ∀ x ∈ D', π x ∈ D) :
    sha2 M S ≤ (sha2 M S').comap (comapH2 π hπ hsm) :=
  fun _ hz => Subgroup.mem_comap.2 (comapH2_mem_sha2 hπ hsm hc hS hz)

end Square

end InverseGalois.CFT
