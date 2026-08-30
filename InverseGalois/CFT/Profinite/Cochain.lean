/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.IndexTwo

/-!
# Smooth cochains on a topological group

The cohomology of an infinite Galois group is computed by the cochains that come from a finite
level, that is by the functions on the group which are constant on the cosets of an open normal
subgroup.  This file sets up those cochains and the two cohomology groups they compute in degrees
one and two, for a topological group acting on a commutative group in such a way that an open
normal subgroup acts trivially.

Everything is phrased with explicit cocycles, in the multiplicative language of
`groupCohomology.IsMulCocycle₁` and `groupCohomology.IsMulCocycle₂`, so that a class at a finite
level can be inflated simply by composing with the projection, and a class can be restricted to a
closed subgroup simply by restricting the cochain.

## Main definitions

* `InverseGalois.CFT.IsOpenNormal`: a subgroup is open and normal.
* `InverseGalois.CFT.IsSmoothAction`: an open normal subgroup acts trivially.
* `InverseGalois.CFT.IsSmooth₁`, `InverseGalois.CFT.IsSmooth₂`: a cochain is constant on the cosets
  of an open normal subgroup.
* `InverseGalois.CFT.SmoothH1`, `InverseGalois.CFT.SmoothH2`: the first and second cohomology of a
  topological group computed by smooth cochains.

## Main results

* `InverseGalois.CFT.smoothH1Mk_eq_one_iff`, `InverseGalois.CFT.smoothH2Mk_eq_one_iff`: a class
  vanishes exactly when its cocycle is the coboundary of a smooth cochain.
* `InverseGalois.CFT.smoothH2Mk_surjective`: every class is the class of a smooth cocycle.

## Tags

profinite group, Galois cohomology, smooth cochain, continuous cochain, cocycle
-/

namespace InverseGalois.CFT

open groupCohomology

section OpenNormal

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A subgroup of a topological group is *open normal* when it is both open and normal.  These are
the subgroups at which a smooth cochain becomes constant. -/
structure IsOpenNormal (N : Subgroup G) : Prop where
  /-- The subgroup is normal. -/
  normal : N.Normal
  /-- The subgroup is open. -/
  isOpen : IsOpen (N : Set G)

/-- The whole group is open and normal. -/
theorem isOpenNormal_top : IsOpenNormal (⊤ : Subgroup G) :=
  ⟨inferInstance, by simp⟩

/-- The intersection of two open normal subgroups is open and normal. -/
theorem IsOpenNormal.inf {N N' : Subgroup G} (h : IsOpenNormal N) (h' : IsOpenNormal N') :
    IsOpenNormal (N ⊓ N') := by
  refine ⟨⟨fun n hn g => ⟨?_, ?_⟩⟩, ?_⟩
  · exact h.normal.conj_mem n hn.1 g
  · exact h'.normal.conj_mem n hn.2 g
  · simpa [Subgroup.coe_inf] using h.isOpen.inter h'.isOpen

end OpenNormal

section SmoothDefs

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*}

/-- A one cochain is *smooth* when it is constant on the cosets of an open normal subgroup. -/
def IsSmooth₁ (u : G → M) : Prop :=
  ∃ N : Subgroup G, IsOpenNormal N ∧ ∀ x : G, ∀ n ∈ N, u (x * n) = u x

/-- A two cochain is *smooth* when it is constant on the cosets of an open normal subgroup in each
variable. -/
def IsSmooth₂ (a : G × G → M) : Prop :=
  ∃ N : Subgroup G, IsOpenNormal N ∧ ∀ x y : G, ∀ n ∈ N, ∀ m ∈ N, a (x * n, y * m) = a (x, y)

/-- Smoothness passes from an open normal subgroup to a smaller one. -/
theorem isSmooth₁_of_le {u : G → M} {N N' : Subgroup G} (hN : IsOpenNormal N) (hle : N ≤ N')
    (h : ∀ x : G, ∀ n ∈ N', u (x * n) = u x) : IsSmooth₁ u :=
  ⟨N, hN, fun x n hn => h x n (hle hn)⟩

/-- Smoothness passes from an open normal subgroup to a smaller one. -/
theorem isSmooth₂_of_le {a : G × G → M} {N N' : Subgroup G} (hN : IsOpenNormal N) (hle : N ≤ N')
    (h : ∀ x y : G, ∀ n ∈ N', ∀ m ∈ N', a (x * n, y * m) = a (x, y)) : IsSmooth₂ a :=
  ⟨N, hN, fun x y n hn m hm => h x y n (hle hn) m (hle hm)⟩

end SmoothDefs

section SmoothGroup

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*} [CommGroup M]

/-- The constant cochain one is smooth. -/
theorem isSmooth₁_one : IsSmooth₁ (1 : G → M) := ⟨⊤, isOpenNormal_top, fun _ _ _ => rfl⟩

/-- The constant cochain one is smooth. -/
theorem isSmooth₂_one : IsSmooth₂ (1 : G × G → M) := ⟨⊤, isOpenNormal_top, fun _ _ _ _ _ _ => rfl⟩

/-- A product of smooth one cochains is smooth. -/
theorem IsSmooth₁.mul {u v : G → M} (hu : IsSmooth₁ u) (hv : IsSmooth₁ v) : IsSmooth₁ (u * v) := by
  obtain ⟨N, hN, hu⟩ := hu
  obtain ⟨N', hN', hv⟩ := hv
  refine ⟨N ⊓ N', hN.inf hN', fun x n hn => ?_⟩
  simp only [Pi.mul_apply, hu x n hn.1, hv x n hn.2]

/-- The inverse of a smooth one cochain is smooth. -/
theorem IsSmooth₁.inv {u : G → M} (hu : IsSmooth₁ u) : IsSmooth₁ u⁻¹ := by
  obtain ⟨N, hN, hu⟩ := hu
  exact ⟨N, hN, fun x n hn => by simp only [Pi.inv_apply, hu x n hn]⟩

/-- A product of smooth two cochains is smooth. -/
theorem IsSmooth₂.mul {a b : G × G → M} (ha : IsSmooth₂ a) (hb : IsSmooth₂ b) :
    IsSmooth₂ (a * b) := by
  obtain ⟨N, hN, ha⟩ := ha
  obtain ⟨N', hN', hb⟩ := hb
  refine ⟨N ⊓ N', hN.inf hN', fun x y n hn m hm => ?_⟩
  simp only [Pi.mul_apply, ha x y n hn.1 m hm.1, hb x y n hn.2 m hm.2]

/-- The inverse of a smooth two cochain is smooth. -/
theorem IsSmooth₂.inv {a : G × G → M} (ha : IsSmooth₂ a) : IsSmooth₂ a⁻¹ := by
  obtain ⟨N, hN, ha⟩ := ha
  exact ⟨N, hN, fun x y n hn m hm => by simp only [Pi.inv_apply, ha x y n hn m hm]⟩

end SmoothGroup

section SmoothAction

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]

variable (G M) in
/-- An action of a topological group on a commutative group is *smooth* when some open normal
subgroup acts trivially.  This is the condition on the coefficients under which smooth cochains
compute the cohomology of the group. -/
class IsSmoothAction : Prop where
  /-- Some open normal subgroup acts trivially. -/
  exists_isOpenNormal : ∃ N : Subgroup G, IsOpenNormal N ∧ ∀ n ∈ N, ∀ m : M, n • m = m

/-- The coboundary of a smooth one cochain is a smooth two cochain. -/
theorem IsSmooth₁.coboundary₂ [IsSmoothAction G M] {u : G → M} (hu : IsSmooth₁ u) :
    IsSmooth₂ (CFT.coboundary₂ u) := by
  obtain ⟨N, hN, hu⟩ := hu
  obtain ⟨N', hN', hact⟩ := IsSmoothAction.exists_isOpenNormal (G := G) (M := M)
  haveI := hN.normal
  refine ⟨N ⊓ N', hN.inf hN', fun x y n hn m hm => ?_⟩
  have hconj : y⁻¹ * n * y ∈ N := by simpa using hN.normal.conj_mem n hn.1 y⁻¹
  have hxy : x * n * (y * m) = x * y * (y⁻¹ * n * y * m) := by group
  simp only [CFT.coboundary₂_apply, hxy, hu x n hn.1, hu (x * y) _ (N.mul_mem hconj hm.1),
    hu y m hm.1, mul_smul, hact n hn.2]

/-- The coboundary of an element is a smooth one cochain. -/
theorem isSmooth₁_smul_div [IsSmoothAction G M] (t : M) : IsSmooth₁ (fun g : G => g • t / t) := by
  obtain ⟨N, hN, hact⟩ := IsSmoothAction.exists_isOpenNormal (G := G) (M := M)
  refine ⟨N, hN, fun x n hn => ?_⟩
  simp only [mul_smul, hact n hn t]

end SmoothAction

section Cochains

variable (G : Type*) [Group G] [TopologicalSpace G]
variable (M : Type*) [CommGroup M] [MulDistribMulAction G M]

/-- The smooth one cochains, as a subgroup of all functions on the group. -/
def smoothCochain₁ : Subgroup (G → M) where
  carrier := {u | IsSmooth₁ u}
  one_mem' := isSmooth₁_one
  mul_mem' := IsSmooth₁.mul
  inv_mem' := IsSmooth₁.inv

/-- The smooth one cocycles. -/
def smoothCocycle₁ : Subgroup (G → M) where
  carrier := {u | IsMulCocycle₁ u ∧ IsSmooth₁ u}
  one_mem' := ⟨fun g h => by simp, isSmooth₁_one⟩
  mul_mem' := by
    rintro u v ⟨hu, hus⟩ ⟨hv, hvs⟩
    refine ⟨fun g h => ?_, hus.mul hvs⟩
    simp only [Pi.mul_apply, hu g h, hv g h, smul_mul']
    exact mul_mul_mul_comm _ _ _ _
  inv_mem' := by
    rintro u ⟨hu, hus⟩
    refine ⟨fun g h => ?_, hus.inv⟩
    simp only [Pi.inv_apply, hu g h, smul_inv', mul_inv]

/-- The one coboundaries: the cochains of the form `g ↦ g • t / t`. -/
def smoothCoboundary₁ : Subgroup (G → M) where
  carrier := {u | ∃ t : M, (fun g : G => g • t / t) = u}
  one_mem' := ⟨1, by ext g; simp⟩
  mul_mem' := by
    rintro u v ⟨s, rfl⟩ ⟨t, rfl⟩
    refine ⟨s * t, ?_⟩
    ext g
    simp only [Pi.mul_apply, smul_mul', mul_div_mul_comm]
  inv_mem' := by
    rintro u ⟨s, rfl⟩
    refine ⟨s⁻¹, ?_⟩
    ext g
    simp only [Pi.inv_apply, smul_inv', inv_div_inv, inv_div]

/-- The smooth two cocycles. -/
def smoothCocycle₂ : Subgroup (G × G → M) where
  carrier := {a | IsMulCocycle₂ a ∧ IsSmooth₂ a}
  one_mem' := ⟨fun g h j => by simp, isSmooth₂_one⟩
  mul_mem' := by
    rintro a b ⟨ha, has⟩ ⟨hb, hbs⟩
    refine ⟨fun g h j => ?_, has.mul hbs⟩
    have h1 := ha g h j
    have h2 := hb g h j
    simp only [Pi.mul_apply, smul_mul']
    calc a (g * h, j) * b (g * h, j) * (a (g, h) * b (g, h))
        = a (g * h, j) * a (g, h) * (b (g * h, j) * b (g, h)) := mul_mul_mul_comm _ _ _ _
      _ = g • a (h, j) * a (g, h * j) * (g • b (h, j) * b (g, h * j)) := by rw [h1, h2]
      _ = g • a (h, j) * g • b (h, j) * (a (g, h * j) * b (g, h * j)) :=
          mul_mul_mul_comm _ _ _ _
  inv_mem' := by
    rintro a ⟨ha, has⟩
    refine ⟨fun g h j => ?_, has.inv⟩
    have h1 := ha g h j
    simp only [Pi.inv_apply, smul_inv', ← mul_inv]
    rw [h1]

/-- The smooth two coboundaries: the coboundaries of smooth one cochains. -/
def smoothCoboundary₂ : Subgroup (G × G → M) where
  carrier := {a | ∃ u : G → M, IsSmooth₁ u ∧ coboundary₂ u = a}
  one_mem' := ⟨1, isSmooth₁_one, coboundary₂_one⟩
  mul_mem' := by
    rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u * v, hu.mul hv, coboundary₂_mul u v⟩
  inv_mem' := by
    rintro a ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, hu.inv, coboundary₂_inv u⟩

variable {G M}

/-- A one coboundary is a smooth one cocycle. -/
theorem smoothCoboundary₁_le_smoothCocycle₁ [IsSmoothAction G M] :
    smoothCoboundary₁ G M ≤ smoothCocycle₁ G M := by
  rintro u ⟨t, rfl⟩
  refine ⟨fun g h => ?_, isSmooth₁_smul_div t⟩
  simp only [mul_smul, smul_div']
  rw [div_mul_div_cancel]

/-- A smooth two coboundary is a smooth two cocycle. -/
theorem smoothCoboundary₂_le_smoothCocycle₂ [IsSmoothAction G M] :
    smoothCoboundary₂ G M ≤ smoothCocycle₂ G M := by
  rintro a ⟨u, hu, rfl⟩
  exact ⟨isMulCocycle₂_coboundary₂ u, hu.coboundary₂⟩

end Cochains

section Cohomology

variable (G : Type*) [Group G] [TopologicalSpace G]
variable (M : Type*) [CommGroup M] [MulDistribMulAction G M]

/-- **The first cohomology of a topological group** with coefficients in a smooth module: the
smooth one cocycles modulo the coboundaries. -/
def SmoothH1 : Type _ :=
  smoothCocycle₁ G M ⧸ (smoothCoboundary₁ G M).subgroupOf (smoothCocycle₁ G M)

/-- **The second cohomology of a topological group** with coefficients in a smooth module: the
smooth two cocycles modulo the coboundaries of smooth one cochains. -/
def SmoothH2 : Type _ :=
  smoothCocycle₂ G M ⧸ (smoothCoboundary₂ G M).subgroupOf (smoothCocycle₂ G M)

instance : CommGroup (SmoothH1 G M) :=
  inferInstanceAs (CommGroup (smoothCocycle₁ G M ⧸ _))

instance : CommGroup (SmoothH2 G M) :=
  inferInstanceAs (CommGroup (smoothCocycle₂ G M ⧸ _))

variable {G M}

/-- The class of a smooth one cocycle. -/
def smoothH1Mk (u : G → M) (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) : SmoothH1 G M :=
  QuotientGroup.mk ⟨u, hu, hs⟩

/-- The class of a smooth two cocycle. -/
def smoothH2Mk (a : G × G → M) (ha : IsMulCocycle₂ a) (hs : IsSmooth₂ a) : SmoothH2 G M :=
  QuotientGroup.mk ⟨a, ha, hs⟩

/-- **A one cocycle is trivial in cohomology exactly when it is a coboundary.** -/
theorem smoothH1Mk_eq_one_iff {u : G → M} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) :
    smoothH1Mk u hu hs = 1 ↔ ∃ t : M, (fun g : G => g • t / t) = u :=
  QuotientGroup.eq_one_iff _

/-- **A two cocycle is trivial in cohomology exactly when it is the coboundary of a smooth
cochain.** -/
theorem smoothH2Mk_eq_one_iff {a : G × G → M} (ha : IsMulCocycle₂ a) (hs : IsSmooth₂ a) :
    smoothH2Mk a ha hs = 1 ↔ ∃ u : G → M, IsSmooth₁ u ∧ coboundary₂ u = a :=
  QuotientGroup.eq_one_iff _

/-- **Every class of the first cohomology is the class of a smooth cocycle.** -/
theorem smoothH1Mk_surjective (x : SmoothH1 G M) :
    ∃ (u : G → M) (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u), smoothH1Mk u hu hs = x := by
  obtain ⟨⟨u, hu, hs⟩, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨u, hu, hs, rfl⟩

/-- **Every class of the second cohomology is the class of a smooth cocycle.** -/
theorem smoothH2Mk_surjective (x : SmoothH2 G M) :
    ∃ (a : G × G → M) (ha : IsMulCocycle₂ a) (hs : IsSmooth₂ a), smoothH2Mk a ha hs = x := by
  obtain ⟨⟨a, ha, hs⟩, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨a, ha, hs, rfl⟩

/-- The class of a product of smooth one cocycles is the product of the classes. -/
theorem smoothH1Mk_mul {u v : G → M} (hu : IsMulCocycle₁ u) (hus : IsSmooth₁ u)
    (hv : IsMulCocycle₁ v) (hvs : IsSmooth₁ v) :
    smoothH1Mk (u * v) ((smoothCocycle₁ G M).mul_mem ⟨hu, hus⟩ ⟨hv, hvs⟩).1
        ((smoothCocycle₁ G M).mul_mem ⟨hu, hus⟩ ⟨hv, hvs⟩).2
      = smoothH1Mk u hu hus * smoothH1Mk v hv hvs := rfl

/-- The class of a product of smooth two cocycles is the product of the classes. -/
theorem smoothH2Mk_mul {a b : G × G → M} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a)
    (hb : IsMulCocycle₂ b) (hbs : IsSmooth₂ b) :
    smoothH2Mk (a * b) ((smoothCocycle₂ G M).mul_mem ⟨ha, has⟩ ⟨hb, hbs⟩).1
        ((smoothCocycle₂ G M).mul_mem ⟨ha, has⟩ ⟨hb, hbs⟩).2
      = smoothH2Mk a ha has * smoothH2Mk b hb hbs := rfl

end Cohomology

end InverseGalois.CFT
