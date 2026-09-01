/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Res

/-!
# The first cohomology of a trivial module

When the group acts trivially on the coefficients the cocycle relation says exactly that the
cochain is a homomorphism, and the coboundaries are all trivial, so the first cohomology is the
group of smooth homomorphisms into the coefficients.  Smoothness of a homomorphism is openness of
its kernel: a homomorphism constant on the cosets of an open normal subgroup kills that subgroup,
and a subgroup containing an open one is open.

This is the shape in which the everywhere locally trivial classes of a number field are used.  A
class of the first cohomology of the absolute Galois group with coefficients in a finite module
which is trivial over a finite extension restricts there to a homomorphism whose kernel cuts out an
abelian extension, and local triviality says that the decomposition subgroups lie in that kernel,
that is, that every place splits completely.

## Main definitions

* `InverseGalois.CFT.cocycleHom`: **a one cocycle for a trivial action, as a homomorphism.**

## Main results

* `InverseGalois.CFT.isSmooth₁_of_ker_le`: a homomorphism killing an open normal subgroup is
  smooth.
* `InverseGalois.CFT.isOpenNormal_ker_cocycleHom`: **the kernel of a smooth one cocycle for a
  trivial action is open and normal.**
* `InverseGalois.CFT.smoothH1Mk_eq_one_iff_of_trivial`: **for a trivial action a one cocycle is
  trivial in cohomology only if it is trivial.**
* `InverseGalois.CFT.smoothH1Mk_mem_sha1_of_trivial`: **for a trivial action a class dies on a
  family of subgroups exactly when every one of them lies in the kernel.**

## Tags

profinite group, Galois cohomology, trivial module, smooth homomorphism, decomposition group
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### A cocycle for a trivial action is a homomorphism -/

section Hom

variable {G : Type*} [Group G] {M : Type*} [CommGroup M] [MulDistribMulAction G M]
  (htriv : ∀ (g : G) (m : M), g • m = m)

include htriv

/-- For a trivial action a one cocycle takes a product to the product of its values. -/
theorem map_mul_of_isMulCocycle₁_of_trivial {u : G → M} (hu : IsMulCocycle₁ u) (g h : G) :
    u (g * h) = u g * u h := by
  rw [hu g h, htriv]
  exact mul_comm _ _

/-- **A one cocycle for a trivial action, as a homomorphism.** -/
def cocycleHom {u : G → M} (hu : IsMulCocycle₁ u) : G →* M where
  toFun := u
  map_one' := map_one_of_isMulCocycle₁ hu
  map_mul' := map_mul_of_isMulCocycle₁_of_trivial htriv hu

@[simp]
theorem cocycleHom_apply {u : G → M} (hu : IsMulCocycle₁ u) (g : G) :
    cocycleHom htriv hu g = u g := rfl

/-- For a trivial action a homomorphism is a one cocycle. -/
theorem isMulCocycle₁_of_hom (f : G →* M) : IsMulCocycle₁ (f : G → M) := by
  intro g h
  rw [htriv, map_mul, mul_comm]

end Hom

/-! ### Smoothness is an open kernel -/

section Smooth

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*} [CommGroup M]

/-- A homomorphism killing an open normal subgroup is a smooth one cochain. -/
theorem isSmooth₁_of_ker_le {f : G →* M} {N : Subgroup G} (hN : IsOpenNormal N)
    (hle : N ≤ f.ker) : IsSmooth₁ (f : G → M) :=
  ⟨N, hN, fun x n hn => by rw [map_mul, MonoidHom.mem_ker.1 (hle hn), mul_one]⟩

end Smooth

/-! ### The classes of a trivial module -/

section Trivial

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*} [CommGroup M]
  [MulDistribMulAction G M] (htriv : ∀ (g : G) (m : M), g • m = m)

include htriv

/-- A trivial action is smooth. -/
theorem isSmoothAction_of_trivial : IsSmoothAction G M :=
  ⟨⊤, isOpenNormal_top, fun n _ m => htriv n m⟩

/-- **For a trivial action a one cocycle is trivial in cohomology only if it is trivial**, every
coboundary being trivial. -/
theorem smoothH1Mk_eq_one_iff_of_trivial {u : G → M} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) :
    smoothH1Mk u hu hs = 1 ↔ u = 1 := by
  rw [smoothH1Mk_eq_one_iff]
  constructor
  · rintro ⟨t, rfl⟩
    funext g
    simp [htriv g t]
  · rintro rfl
    exact ⟨1, by funext g; simp [htriv g (1 : M)]⟩

/-- **The kernel of a smooth one cocycle for a trivial action is open and normal.** -/
theorem isOpenNormal_ker_cocycleHom [IsTopologicalGroup G] {u : G → M} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u) : IsOpenNormal (cocycleHom htriv hu).ker := by
  obtain ⟨N, hN, hcon⟩ := hs
  refine ⟨MonoidHom.normal_ker _, Subgroup.isOpen_mono (H₁ := N) (fun n hn => ?_) hN.isOpen⟩
  have h1 := hcon 1 n hn
  rw [one_mul] at h1
  rw [MonoidHom.mem_ker, cocycleHom_apply, h1, map_one_of_isMulCocycle₁ hu]

/-- **For a trivial action the restriction of a class to a subgroup is trivial exactly when the
subgroup lies in the kernel of the cocycle.** -/
theorem resH1_eq_one_iff_of_trivial (H : Subgroup G) {u : G → M} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u) : resH1 H (smoothH1Mk u hu hs) = 1 ↔ ∀ h ∈ H, u h = 1 := by
  rw [resH1_eq_one_iff]
  constructor
  · rintro ⟨t, ht⟩ h hh
    have h1 := ht h hh
    rwa [htriv, div_self', eq_comm] at h1
  · intro h
    exact ⟨1, fun x hx => by rw [htriv, div_self', h x hx]⟩

/-- **For a trivial action a class dies on a family of subgroups exactly when every one of them
lies in the kernel of the cocycle.** -/
theorem smoothH1Mk_mem_sha1_of_trivial {S : Set (Subgroup G)} {u : G → M} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u) :
    smoothH1Mk u hu hs ∈ sha1 M S ↔ ∀ D ∈ S, ∀ d ∈ D, u d = 1 := by
  simp only [mem_sha1, resH1_eq_one_iff_of_trivial htriv]

/-- **For a trivial action a class dies on a family of subgroups exactly when every one of them
lies in the kernel of the associated homomorphism.** -/
theorem smoothH1Mk_mem_sha1_iff_le_ker {S : Set (Subgroup G)} {u : G → M} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u) :
    smoothH1Mk u hu hs ∈ sha1 M S ↔ ∀ D ∈ S, D ≤ (cocycleHom htriv hu).ker := by
  rw [smoothH1Mk_mem_sha1_of_trivial htriv hu hs]
  exact forall_congr' fun D => forall_congr' fun _ => Iff.rfl

end Trivial

end InverseGalois.CFT
