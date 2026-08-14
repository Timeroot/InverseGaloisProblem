/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.ProductTranslate
import InverseGalois.Rigidity.RET.Existence

/-!
# Products of geometric Galois covers

A cover of the line and a finite Galois extension of `ℚ̄(T)` are the same thing read two ways, and
under that dictionary the product construction says that the groups realized by geometric Galois
covers are closed under direct products — finite ones, not merely two at a time.

## Main results

* `Rigidity.RET.isGeometricGaloisCover_iff_exists_lineCover` — the dictionary between a geometric
  Galois cover and a cover of the line.
* `Rigidity.RET.IsGeometricGaloisCover.prod` — a product of two groups realized by geometric Galois
  covers is realized by one.
* `Rigidity.RET.IsAffineDeckGroup.pi` — for a finite family the affine branch points add.
* `Rigidity.RET.isGeometricGaloisCover_pi` — a finite product of groups realized by geometric
  Galois covers is realized by one.
-/

open Polynomial IntermediateField

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

/-- **A geometric Galois cover is a cover of the line, and conversely**: the two say the same thing
about a group, one through the bare field extension and the other through the integral model that
addresses the places. -/
theorem isGeometricGaloisCover_iff_exists_lineCover {G : Type} [Group G] :
    IsGeometricGaloisCover G ↔ ∃ L : LineCover, Nonempty (L.deck ≃* G) := by
  constructor
  · rintro ⟨M, hfield, halg, hfd, hgal, ⟨e⟩⟩
    exact ⟨@LineCover.of M hfield halg hfd hgal, ⟨e⟩⟩
  · rintro ⟨L, ⟨e⟩⟩
    exact ⟨L.M, L.field, L.alg, L.findim, L.isGalois, ⟨e⟩⟩

/-- A group realized by a geometric Galois cover is realized with some number of affine branch
points. -/
theorem IsGeometricGaloisCover.exists_isAffineDeckGroup {G : Type} [Group G] [Finite G]
    (h : IsGeometricGaloisCover G) : ∃ n : ℕ, IsAffineDeckGroup n G := by
  obtain ⟨L, e⟩ := isGeometricGaloisCover_iff_exists_lineCover.mp h
  exact ⟨L.branchLocus.ncard, L, e, le_rfl⟩

/-- A group realized with some number of affine branch points is realized by a geometric Galois
cover. -/
theorem IsAffineDeckGroup.isGeometricGaloisCover {n : ℕ} {G : Type} [Group G] [Finite G]
    (h : IsAffineDeckGroup n G) : IsGeometricGaloisCover G := by
  obtain ⟨L, e, -⟩ := h
  exact isGeometricGaloisCover_iff_exists_lineCover.mpr ⟨L, e⟩

/-- **The groups realized by geometric Galois covers are closed under direct products.** -/
theorem IsGeometricGaloisCover.prod {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]
    (h₁ : IsGeometricGaloisCover G₁) (h₂ : IsGeometricGaloisCover G₂) :
    IsGeometricGaloisCover (G₁ × G₂) := by
  obtain ⟨m, hm⟩ := IsGeometricGaloisCover.exists_isAffineDeckGroup h₁
  obtain ⟨n, hn⟩ := IsGeometricGaloisCover.exists_isAffineDeckGroup h₂
  exact IsAffineDeckGroup.isGeometricGaloisCover (IsAffineDeckGroup.prod hm hn)

/-! ### Finite families -/

/-- Splitting off the first factor of a finite product of groups. -/
def consMulEquiv {r : ℕ} (G : Fin (r + 1) → Type) [∀ i, Group (G i)] :
    G 0 × (∀ i : Fin r, G i.succ) ≃* ∀ i, G i where
  __ := Fin.consEquiv G
  map_mul' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.consEquiv]

/-- **The affine branch points of a finite product of groups add.** -/
theorem IsAffineDeckGroup.pi : ∀ {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {n : Fin r → ℕ}, (∀ i, IsAffineDeckGroup (n i) (G i)) →
    IsAffineDeckGroup (∑ i, n i) (∀ i, G i) := by
  intro r
  induction r with
  | zero =>
    intro G _ _ n _
    simpa using isAffineDeckGroup_zero_iff.mpr inferInstance
  | succ r ih =>
    intro G _ _ n h
    have hprod := IsAffineDeckGroup.prod (h 0)
      (ih (G := fun i => G i.succ) (n := fun i => n i.succ) fun i => h i.succ)
    simpa [Fin.sum_univ_succ] using IsAffineDeckGroup.congr hprod (consMulEquiv G)

/-- **A finite product of groups realized by geometric Galois covers is realized by one.** -/
theorem isGeometricGaloisCover_pi {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] (h : ∀ i, IsGeometricGaloisCover (G i)) :
    IsGeometricGaloisCover (∀ i, G i) := by
  choose n hn using fun i => IsGeometricGaloisCover.exists_isAffineDeckGroup (h i)
  exact IsAffineDeckGroup.isGeometricGaloisCover (IsAffineDeckGroup.pi (n := n) hn)

end Rigidity.RET
