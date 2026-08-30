/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Comap

/-!
# Restriction to a subgroup, and the classes that die on a family of them

A subgroup of a topological group carries the subspace topology and the inclusion is continuous, so
composing a cochain with it preserves smoothness and gives restriction.  The subgroup also inherits
smoothness of the action, an open normal subgroup of the ambient group meeting it in one.

A family of subgroups then cuts out the classes whose restriction to every member of the family is
trivial.  For the Galois group of a number field and the family of decomposition subgroups these
are the everywhere locally trivial classes, whose group is the obstruction to a local-global
principle; the definition here is the general one, a subgroup of the first or second cohomology
attached to an arbitrary family of subgroups.

## Main definitions

* `InverseGalois.CFT.resH1`, `InverseGalois.CFT.resH2`: **restriction to a subgroup.**
* `InverseGalois.CFT.sha1`, `InverseGalois.CFT.sha2`: **the classes whose restriction to every
  subgroup of a family is trivial.**

## Main results

* `InverseGalois.CFT.isSmoothHom_subtype`: the inclusion of a subgroup is a smooth homomorphism.
* `InverseGalois.CFT.resH1_eq_one_iff`: restriction of a class to a subgroup is trivial exactly
  when the cocycle is a coboundary on that subgroup.
* `InverseGalois.CFT.smoothH1Mk_mem_sha1`, `InverseGalois.CFT.smoothH2Mk_mem_sha2`: membership
  read off a representing cocycle.

## Tags

profinite group, Galois cohomology, restriction, decomposition group, local-global principle
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### The inclusion of a subgroup -/

section Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G)

/-- The inclusion of a subgroup is continuous for the subspace topology. -/
theorem continuous_subtype : Continuous (H.subtype) := continuous_subtype_val

/-- **The inclusion of a subgroup is a smooth homomorphism.** -/
theorem isSmoothHom_subtype : IsSmoothHom (H.subtype) :=
  isSmoothHom_of_continuous (continuous_subtype H)

section Coefficients

variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- The intersection of a subgroup with an open normal subgroup is open and normal in it. -/
theorem isOpenNormal_comap_subtype {N : Subgroup G} (hN : IsOpenNormal N) :
    IsOpenNormal (N.comap H.subtype) := by
  refine ⟨hN.normal.comap _, ?_⟩
  rw [Subgroup.coe_comap]
  exact hN.isOpen.preimage (continuous_subtype H)

/-- **A subgroup inherits smoothness of the action.** -/
instance isSmoothAction_subtype [IsSmoothAction G M] : IsSmoothAction H M := by
  obtain ⟨N, hN, hact⟩ := IsSmoothAction.exists_isOpenNormal (G := G) (M := M)
  exact ⟨N.comap H.subtype, isOpenNormal_comap_subtype H hN, fun n hn m => hact n hn m⟩

/-- **Restriction of a class of the first cohomology to a subgroup.** -/
def resH1 : SmoothH1 G M →* SmoothH1 H M :=
  comapH1 H.subtype (fun _ _ => rfl) (isSmoothHom_subtype H)

/-- **Restriction of a class of the second cohomology to a subgroup.** -/
def resH2 : SmoothH2 G M →* SmoothH2 H M :=
  comapH2 H.subtype (fun _ _ => rfl) (isSmoothHom_subtype H)

/-- Restriction is computed on cocycles. -/
theorem resH1_smoothH1Mk {u : G → M} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) :
    resH1 H (smoothH1Mk u hu hs)
      = smoothH1Mk (comap₁ H.subtype u) (isMulCocycle₁_comap₁ _ (fun _ _ => rfl) hu)
        ((isSmoothHom_subtype H).isSmooth₁ hs) := rfl

/-- Restriction is computed on cocycles. -/
theorem resH2_smoothH2Mk {a : G × G → M} (ha : IsMulCocycle₂ a) (hs : IsSmooth₂ a) :
    resH2 H (smoothH2Mk a ha hs)
      = smoothH2Mk (comap₂ H.subtype a) (isMulCocycle₂_comap₂ _ (fun _ _ => rfl) ha)
        ((isSmoothHom_subtype H).isSmooth₂ hs) := rfl

/-- **The restriction of a class to a subgroup is trivial exactly when the cocycle is a coboundary
on that subgroup.** -/
theorem resH1_eq_one_iff {u : G → M} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) :
    resH1 H (smoothH1Mk u hu hs) = 1 ↔ ∃ t : M, ∀ h ∈ H, h • t / t = u h := by
  rw [resH1_smoothH1Mk, smoothH1Mk_eq_one_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun h hh => congrFun ht ⟨h, hh⟩⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, funext fun h => ht h h.2⟩

/-- **The restriction of a class to a subgroup is trivial exactly when the cocycle is the coboundary
of a smooth cochain on that subgroup.** -/
theorem resH2_eq_one_iff {a : G × G → M} (ha : IsMulCocycle₂ a) (hs : IsSmooth₂ a) :
    resH2 H (smoothH2Mk a ha hs) = 1 ↔
      ∃ u : H → M, IsSmooth₁ u ∧ coboundary₂ u = comap₂ H.subtype a := by
  rw [resH2_smoothH2Mk, smoothH2Mk_eq_one_iff]

end Coefficients

end Subgroup

/-! ### The classes that die on a family of subgroups -/

section Family

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*} [CommGroup M]
  [MulDistribMulAction G M]

variable (M) in
/-- **The classes of the first cohomology whose restriction to every subgroup of a family is
trivial.**  For the family of decomposition subgroups of the Galois group of a number field these
are the everywhere locally trivial classes. -/
def sha1 (S : Set (Subgroup G)) : Subgroup (SmoothH1 G M) :=
  ⨅ D ∈ S, (resH1 D).ker

variable (M) in
/-- **The classes of the second cohomology whose restriction to every subgroup of a family is
trivial.**  For the family of decomposition subgroups of the Galois group of a number field these
are the everywhere locally trivial classes. -/
def sha2 (S : Set (Subgroup G)) : Subgroup (SmoothH2 G M) :=
  ⨅ D ∈ S, (resH2 D).ker

@[simp]
theorem mem_sha1 {S : Set (Subgroup G)} {z : SmoothH1 G M} :
    z ∈ sha1 M S ↔ ∀ D ∈ S, resH1 D z = 1 := by
  simp [sha1, Subgroup.mem_iInf, MonoidHom.mem_ker]

@[simp]
theorem mem_sha2 {S : Set (Subgroup G)} {z : SmoothH2 G M} :
    z ∈ sha2 M S ↔ ∀ D ∈ S, resH2 D z = 1 := by
  simp [sha2, Subgroup.mem_iInf, MonoidHom.mem_ker]

/-- A larger family of subgroups is a stronger condition. -/
theorem sha1_mono {S T : Set (Subgroup G)} (h : S ⊆ T) : sha1 M T ≤ sha1 M S :=
  fun _ hz => mem_sha1.2 fun D hD => mem_sha1.1 hz D (h hD)

/-- A larger family of subgroups is a stronger condition. -/
theorem sha2_mono {S T : Set (Subgroup G)} (h : S ⊆ T) : sha2 M T ≤ sha2 M S :=
  fun _ hz => mem_sha2.2 fun D hD => mem_sha2.1 hz D (h hD)

/-- **A class is locally trivial exactly when its cocycle is a coboundary on every subgroup of the
family.** -/
theorem smoothH1Mk_mem_sha1 {S : Set (Subgroup G)} {u : G → M} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u) :
    smoothH1Mk u hu hs ∈ sha1 M S ↔ ∀ D ∈ S, ∃ t : M, ∀ d ∈ D, d • t / t = u d := by
  simp only [mem_sha1, resH1_eq_one_iff]

/-- **A class is locally trivial exactly when its cocycle is a coboundary on every subgroup of the
family.** -/
theorem smoothH2Mk_mem_sha2 {S : Set (Subgroup G)} {a : G × G → M} (ha : IsMulCocycle₂ a)
    (hs : IsSmooth₂ a) :
    smoothH2Mk a ha hs ∈ sha2 M S ↔
      ∀ D ∈ S, ∃ u : D → M, IsSmooth₁ u ∧ coboundary₂ u = comap₂ D.subtype a := by
  simp only [mem_sha2, resH2_eq_one_iff]

end Family

end InverseGalois.CFT
