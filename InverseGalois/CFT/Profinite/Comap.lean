/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Cochain

/-!
# Smooth cochains along a homomorphism of topological groups

A homomorphism of topological groups whose target acts on a commutative group makes the source act
as well, and a cochain of the target is carried to one of the source simply by composing with the
homomorphism.  The cocycle relation and the coboundary are preserved, so the construction descends
to cohomology in degrees one and two, provided that composing preserves smoothness.

Two conditions guarantee that, and they are the two ways the map will be used.  A continuous
homomorphism pulls an open normal subgroup back to an open normal subgroup, which is restriction to
a closed subgroup; a homomorphism with open kernel pulls every subgroup back to one containing that
kernel, which is inflation from a finite level and which makes *every* cochain of the target
smooth, not only the smooth ones.

## Main definitions

* `InverseGalois.CFT.comap₁`, `InverseGalois.CFT.comap₂`: a cochain composed with a homomorphism.
* `InverseGalois.CFT.IsSmoothHom`: every open normal subgroup of the target pulls back to a
  subgroup containing an open normal subgroup of the source.
* `InverseGalois.CFT.comapH1`, `InverseGalois.CFT.comapH2`: **the induced maps in cohomology.**

## Main results

* `InverseGalois.CFT.isSmoothHom_of_continuous`,
  `InverseGalois.CFT.isSmoothHom_of_isOpenNormal_ker`: the two sources of the smoothness condition.
* `InverseGalois.CFT.isSmooth₂_comap₂_of_isOpenNormal_ker`: with an open kernel every composed
  cochain is smooth.
* `InverseGalois.CFT.comapH2_smoothH2Mk`: the map in cohomology is computed on cocycles.

## Tags

profinite group, Galois cohomology, inflation, restriction, smooth cochain
-/

namespace InverseGalois.CFT

open groupCohomology

section Defs

variable {G Q M : Type*} [Group G] [Group Q]

/-- A one cochain of the target composed with a homomorphism. -/
def comap₁ (π : G →* Q) (u : Q → M) : G → M := fun g => u (π g)

/-- A two cochain of the target composed with a homomorphism. -/
def comap₂ (π : G →* Q) (a : Q × Q → M) : G × G → M := fun p => a (π p.1, π p.2)

@[simp]
theorem comap₁_apply (π : G →* Q) (u : Q → M) (g : G) : comap₁ π u g = u (π g) := rfl

@[simp]
theorem comap₂_apply (π : G →* Q) (a : Q × Q → M) (x y : G) :
    comap₂ π a (x, y) = a (π x, π y) := rfl

end Defs

section OpenKernel

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [Group Q] (π : G →* Q)

/-- With an open kernel every composed one cochain is smooth. -/
theorem isSmooth₁_comap₁_of_isOpenNormal_ker (hker : IsOpenNormal π.ker) (u : Q → M) :
    IsSmooth₁ (comap₁ π u) := by
  refine ⟨π.ker, hker, fun x n hn => ?_⟩
  simp only [comap₁_apply, map_mul, MonoidHom.mem_ker.mp hn, mul_one]

/-- With an open kernel every composed two cochain is smooth. -/
theorem isSmooth₂_comap₂_of_isOpenNormal_ker (hker : IsOpenNormal π.ker) (a : Q × Q → M) :
    IsSmooth₂ (comap₂ π a) := by
  refine ⟨π.ker, hker, fun x y n hn m hm => ?_⟩
  simp only [comap₂_apply, map_mul, MonoidHom.mem_ker.mp hn, MonoidHom.mem_ker.mp hm, mul_one]

end OpenKernel

section SmoothHom

variable {G Q : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]

/-- A homomorphism of topological groups is *smooth* when every open normal subgroup of the target
pulls back to a subgroup containing an open normal subgroup of the source.  This is what makes
composition with the homomorphism preserve smoothness of cochains. -/
def IsSmoothHom (π : G →* Q) : Prop :=
  ∀ N : Subgroup Q, IsOpenNormal N → ∃ N' : Subgroup G, IsOpenNormal N' ∧ N' ≤ N.comap π

/-- **A continuous homomorphism is smooth**, the preimage of an open normal subgroup being open and
normal. -/
theorem isSmoothHom_of_continuous {π : G →* Q} (hc : Continuous π) : IsSmoothHom π := by
  refine fun N hN => ⟨N.comap π, ⟨hN.normal.comap π, ?_⟩, le_rfl⟩
  rw [Subgroup.coe_comap]
  exact hN.isOpen.preimage hc

/-- **A homomorphism with open kernel is smooth**, every preimage containing the kernel. -/
theorem isSmoothHom_of_isOpenNormal_ker {π : G →* Q} (hker : IsOpenNormal π.ker) :
    IsSmoothHom π := fun N _ =>
  ⟨π.ker, hker, fun x hx => Subgroup.mem_comap.2 (by rw [MonoidHom.mem_ker.mp hx]; exact N.one_mem)⟩

variable {M : Type*} {π : G →* Q}

/-- A smooth homomorphism carries a smooth one cochain to a smooth one cochain. -/
theorem IsSmoothHom.isSmooth₁ (hπ : IsSmoothHom π) {u : Q → M} (hu : IsSmooth₁ u) :
    IsSmooth₁ (comap₁ π u) := by
  obtain ⟨N, hN, hu⟩ := hu
  obtain ⟨N', hN', hle⟩ := hπ N hN
  refine ⟨N', hN', fun x n hn => ?_⟩
  simp only [comap₁_apply, map_mul, hu (π x) (π n) (Subgroup.mem_comap.1 (hle hn))]

/-- A smooth homomorphism carries a smooth two cochain to a smooth two cochain. -/
theorem IsSmoothHom.isSmooth₂ (hπ : IsSmoothHom π) {a : Q × Q → M} (ha : IsSmooth₂ a) :
    IsSmooth₂ (comap₂ π a) := by
  obtain ⟨N, hN, ha⟩ := ha
  obtain ⟨N', hN', hle⟩ := hπ N hN
  refine ⟨N', hN', fun x y n hn m hm => ?_⟩
  simp only [comap₂_apply, map_mul,
    ha (π x) (π y) (π n) (Subgroup.mem_comap.1 (hle hn)) (π m) (Subgroup.mem_comap.1 (hle hm))]

end SmoothHom

section Cocycle

variable {G Q M : Type*} [Group G] [Group Q] [CommGroup M] [MulDistribMulAction G M]
  [MulDistribMulAction Q M] (π : G →* Q) (hπ : ∀ (g : G) (m : M), g • m = π g • m)

include hπ

/-- Composing with a homomorphism carries a one cocycle to a one cocycle. -/
theorem isMulCocycle₁_comap₁ {u : Q → M} (hu : IsMulCocycle₁ u) : IsMulCocycle₁ (comap₁ π u) := by
  intro g h
  simp only [comap₁_apply, map_mul, hu (π g) (π h), hπ]

/-- Composing with a homomorphism carries a two cocycle to a two cocycle. -/
theorem isMulCocycle₂_comap₂ {a : Q × Q → M} (ha : IsMulCocycle₂ a) :
    IsMulCocycle₂ (comap₂ π a) := by
  intro g h j
  simp only [comap₂_apply, map_mul, ha (π g) (π h) (π j), hπ]

/-- Composing with a homomorphism commutes with the coboundary. -/
theorem coboundary₂_comap₁ (u : Q → M) :
    coboundary₂ (comap₁ π u) = comap₂ π (coboundary₂ u) := by
  ext p
  simp only [coboundary₂, comap₁_apply, comap₂, map_mul, hπ]

end Cocycle

section SmoothAction

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [Group Q] [CommGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction Q M] (π : G →* Q)
  (hπ : ∀ (g : G) (m : M), g • m = π g • m)

include hπ

/-- An open kernel makes the pulled back action smooth. -/
theorem isSmoothAction_of_isOpenNormal_ker (hker : IsOpenNormal π.ker) : IsSmoothAction G M := by
  refine ⟨π.ker, hker, fun n hn m => ?_⟩
  rw [hπ n m, MonoidHom.mem_ker.mp hn, one_smul]

end SmoothAction

section Cohomology

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
  [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction Q M]
variable (π : G →* Q) (hπ : ∀ (g : G) (m : M), g • m = π g • m) (hsm : IsSmoothHom π)

include hπ hsm

/-- Composition with a smooth homomorphism, on one cocycles. -/
def comapCocycle₁ : smoothCocycle₁ Q M →* smoothCocycle₁ G M where
  toFun u := ⟨comap₁ π u.1, isMulCocycle₁_comap₁ π hπ u.2.1, hsm.isSmooth₁ u.2.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Composition with a smooth homomorphism, on two cocycles. -/
def comapCocycle₂ : smoothCocycle₂ Q M →* smoothCocycle₂ G M where
  toFun a := ⟨comap₂ π a.1, isMulCocycle₂_comap₂ π hπ a.2.1, hsm.isSmooth₂ a.2.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The map in the first cohomology induced by a smooth homomorphism.**  For a homomorphism with
open kernel this is inflation from a finite level, and for a continuous inclusion it is
restriction. -/
def comapH1 : SmoothH1 Q M →* SmoothH1 G M :=
  QuotientGroup.map _ _ (comapCocycle₁ π hπ hsm) <| by
    rintro ⟨u, hu, hus⟩ ⟨t, ht⟩
    refine Subgroup.mem_comap.2 ⟨t, ?_⟩
    ext g
    rw [hπ g t]
    exact congrFun ht (π g)

/-- **The map in the second cohomology induced by a smooth homomorphism.**  For a homomorphism with
open kernel this is inflation from a finite level, and for a continuous inclusion it is
restriction. -/
def comapH2 : SmoothH2 Q M →* SmoothH2 G M :=
  QuotientGroup.map _ _ (comapCocycle₂ π hπ hsm) <| by
    rintro ⟨a, ha, has⟩ ⟨u, hu, rfl⟩
    exact Subgroup.mem_comap.2
      ⟨comap₁ π u, hsm.isSmooth₁ hu, coboundary₂_comap₁ π hπ u⟩

/-- **The map in cohomology is computed on cocycles.** -/
theorem comapH1_smoothH1Mk {u : Q → M} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) :
    comapH1 π hπ hsm (smoothH1Mk u hu hs)
      = smoothH1Mk (comap₁ π u) (isMulCocycle₁_comap₁ π hπ hu) (hsm.isSmooth₁ hs) := rfl

/-- **The map in cohomology is computed on cocycles.** -/
theorem comapH2_smoothH2Mk {a : Q × Q → M} (ha : IsMulCocycle₂ a) (hs : IsSmooth₂ a) :
    comapH2 π hπ hsm (smoothH2Mk a ha hs)
      = smoothH2Mk (comap₂ π a) (isMulCocycle₂_comap₂ π hπ ha) (hsm.isSmooth₂ hs) := rfl

end Cohomology

end InverseGalois.CFT
