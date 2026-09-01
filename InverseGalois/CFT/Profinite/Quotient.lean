/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.InfRes

/-!
# The finite levels of the cohomology of a topological group

An open normal subgroup which acts trivially on the coefficients is a *level*: the quotient by it
acts on the coefficients, the quotient is discrete, and the projection has open kernel, so that
composing with the projection is inflation from that level.  This file records the action of the
quotient, packages inflation, and transports the results on inflation and restriction to this
setting.

Two facts make the levels cofinal.  Smoothness of a cochain is by definition constancy on the
cosets of an open normal subgroup, and smoothness of the action is triviality on one; the
intersection of the two is again open and normal.  So every class of the first or second cohomology
is represented by a cocycle constant on the cosets of a single level, and is therefore inflated
from that level.

## Main definitions

* `InverseGalois.CFT.ActsTrivially`: a subgroup fixes every point of the coefficients.
* `InverseGalois.CFT.quotientMulDistribMulAction`: the action of the quotient by such a subgroup.
* `InverseGalois.CFT.inflH1`, `InverseGalois.CFT.inflH2`: **inflation from a level.**

## Main results

* `InverseGalois.CFT.inflH1_injective`: **inflation is injective in the first cohomology.**
* `InverseGalois.CFT.exists_inflH1_eq`, `InverseGalois.CFT.exists_inflH2_eq`: **a class
  represented at a level is inflated from it.**
* `InverseGalois.CFT.exists_isOpenNormal_smooth₁`,
  `InverseGalois.CFT.exists_isOpenNormal_smooth₂`: **every class is represented at a level.**

## Tags

profinite group, Galois cohomology, inflation, smooth cochain, finite level
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### A subgroup acting trivially -/

section ActsTrivially

/-- A subgroup of a group acting on a commutative group *acts trivially* when each of its elements
fixes every point.  This is the condition under which the quotient by the subgroup acts. -/
class ActsTrivially {G : Type*} [Group G] (N : Subgroup G) (M : Type*) [CommGroup M]
    [MulDistribMulAction G M] : Prop where
  /-- Each element of the subgroup fixes every point. -/
  smul_eq_self : ∀ n ∈ N, ∀ m : M, n • m = m

variable {G : Type*} [Group G] (N : Subgroup G) (M : Type*) [CommGroup M]
  [MulDistribMulAction G M] [ActsTrivially N M] [N.Normal]

/-- The automorphisms of the coefficients defined by the quotient by a subgroup acting
trivially. -/
def quotientAut : G ⧸ N →* MulAut M :=
  QuotientGroup.lift N (MulDistribMulAction.toMulAut G M) fun n hn =>
    MulEquiv.ext fun m => ActsTrivially.smul_eq_self n hn m

/-- **The action of the quotient by a subgroup acting trivially.** -/
instance quotientMulDistribMulAction : MulDistribMulAction (G ⧸ N) M :=
  MulDistribMulAction.compHom M (quotientAut N M)

/-- The quotient acts as the group does. -/
theorem quotientMk_smul (g : G) (m : M) : (QuotientGroup.mk g : G ⧸ N) • m = g • m := rfl

/-- An open subgroup acting trivially makes the action smooth. -/
theorem isSmoothAction_of_actsTrivially [TopologicalSpace G] (hopen : IsOpen (N : Set G)) :
    IsSmoothAction G M :=
  ⟨N, ⟨inferInstance, hopen⟩, ActsTrivially.smul_eq_self⟩

end ActsTrivially

/-! ### The projection to a level -/

section Projection

variable {G : Type*} [Group G] [TopologicalSpace G] (N : Subgroup G) [N.Normal]

/-- The kernel of the projection to the quotient by an open normal subgroup is open and normal. -/
theorem isOpenNormal_ker_mk' (hopen : IsOpen (N : Set G)) :
    IsOpenNormal (QuotientGroup.mk' N : G →* G ⧸ N).ker := by
  rw [QuotientGroup.ker_mk']
  exact ⟨inferInstance, hopen⟩

/-- The projection to the quotient by an open normal subgroup is a smooth homomorphism. -/
theorem isSmoothHom_mk' (hopen : IsOpen (N : Set G)) :
    IsSmoothHom (QuotientGroup.mk' N : G →* G ⧸ N) :=
  isSmoothHom_of_isOpenNormal_ker (isOpenNormal_ker_mk' N hopen)

omit [TopologicalSpace G] in
/-- The projection to a quotient is surjective. -/
theorem mk'_surjective : Function.Surjective (QuotientGroup.mk' N : G →* G ⧸ N) := fun q => by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨g, rfl⟩

end Projection

/-! ### Inflation from a level -/

section Inflation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G)
  [N.Normal] (M : Type*) [CommGroup M] [MulDistribMulAction G M] [ActsTrivially N M]

/-- **Inflation from a level, in the first cohomology.** -/
def inflH1 (hopen : IsOpen (N : Set G)) : SmoothH1 (G ⧸ N) M →* SmoothH1 G M :=
  comapH1 (QuotientGroup.mk' N) (fun _ _ => rfl) (isSmoothHom_mk' N hopen)

/-- **Inflation from a level, in the second cohomology.** -/
def inflH2 (hopen : IsOpen (N : Set G)) : SmoothH2 (G ⧸ N) M →* SmoothH2 G M :=
  comapH2 (QuotientGroup.mk' N) (fun _ _ => rfl) (isSmoothHom_mk' N hopen)

omit [IsTopologicalGroup G] in
/-- **Inflation is injective in the first cohomology.** -/
theorem inflH1_injective (hopen : IsOpen (N : Set G)) :
    Function.Injective (inflH1 N M hopen) :=
  comapH1_injective (fun _ _ => rfl) (isSmoothHom_mk' N hopen) (mk'_surjective N)

/-- **A class of the first cohomology whose restriction to a level is a coboundary is inflated from
that level.** -/
theorem exists_inflH1_eq (hopen : IsOpen (N : Set G)) {v : G → M} (hv : IsMulCocycle₁ v)
    (hvs : IsSmooth₁ v) (t : M) (ht : ∀ n ∈ N, n • t / t = v n) :
    ∃ x : SmoothH1 (G ⧸ N) M, inflH1 N M hopen x = smoothH1Mk v hv hvs := by
  haveI : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hopen
  haveI : IsSmoothAction G M := isSmoothAction_of_actsTrivially N M hopen
  refine exists_comapH1_eq (fun _ _ => rfl) (isSmoothHom_mk' N hopen) (mk'_surjective N) hv hvs
    t fun n hn => ht n ?_
  rwa [QuotientGroup.ker_mk'] at hn

/-- **A class of the second cohomology represented by a cocycle constant on the cosets of a level
is inflated from that level.** -/
theorem exists_inflH2_eq (hopen : IsOpen (N : Set G)) {a : G × G → M} (ha : IsMulCocycle₂ a)
    (has : IsSmooth₂ a) (hs : ∀ x y : G, ∀ n ∈ N, ∀ m ∈ N, a (x * n, y * m) = a (x, y)) :
    ∃ x : SmoothH2 (G ⧸ N) M, inflH2 N M hopen x = smoothH2Mk a ha has := by
  haveI : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hopen
  refine exists_comapH2_eq (fun _ _ => rfl) (isSmoothHom_mk' N hopen) (mk'_surjective N) ha has
    fun x y n hn m hm => hs x y n ?_ m ?_
  · rwa [QuotientGroup.ker_mk'] at hn
  · rwa [QuotientGroup.ker_mk'] at hm

end Inflation

/-! ### Every class lives at a level -/

section Levels

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*} [CommGroup M]
  [MulDistribMulAction G M] [IsSmoothAction G M]

/-- **Every class of the first cohomology is represented at a level**: by a cocycle constant on the
cosets of an open normal subgroup which acts trivially on the coefficients. -/
theorem exists_isOpenNormal_smooth₁ (x : SmoothH1 G M) :
    ∃ N : Subgroup G, IsOpenNormal N ∧ (∀ n ∈ N, ∀ m : M, n • m = m) ∧
      ∃ (u : G → M) (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u),
        (∀ g : G, ∀ n ∈ N, u (g * n) = u g) ∧ smoothH1Mk u hu hs = x := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  obtain ⟨N₁, hN₁, hu₁⟩ := hs
  obtain ⟨N₂, hN₂, hact⟩ := IsSmoothAction.exists_isOpenNormal (G := G) (M := M)
  exact ⟨N₁ ⊓ N₂, hN₁.inf hN₂, fun n hn m => hact n hn.2 m, u, hu, ⟨N₁, hN₁, hu₁⟩,
    fun g n hn => hu₁ g n hn.1, rfl⟩

/-- **Every class of the second cohomology is represented at a level**: by a cocycle constant on
the cosets of an open normal subgroup which acts trivially on the coefficients. -/
theorem exists_isOpenNormal_smooth₂ (x : SmoothH2 G M) :
    ∃ N : Subgroup G, IsOpenNormal N ∧ (∀ n ∈ N, ∀ m : M, n • m = m) ∧
      ∃ (a : G × G → M) (ha : IsMulCocycle₂ a) (hs : IsSmooth₂ a),
        (∀ x y : G, ∀ n ∈ N, ∀ m ∈ N, a (x * n, y * m) = a (x, y)) ∧ smoothH2Mk a ha hs = x := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
  obtain ⟨N₁, hN₁, ha₁⟩ := hs
  obtain ⟨N₂, hN₂, hact⟩ := IsSmoothAction.exists_isOpenNormal (G := G) (M := M)
  exact ⟨N₁ ⊓ N₂, hN₁.inf hN₂, fun n hn m => hact n hn.2 m, a, ha, ⟨N₁, hN₁, ha₁⟩,
    fun x y n hn m hm => ha₁ x y n hn.1 m hm.1, rfl⟩

end Levels

end InverseGalois.CFT
