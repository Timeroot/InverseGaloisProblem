/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TorsionFree

/-!
# Cohomological triviality of a representation of a p-group

Every representation is a quotient of an induced one built on a free module: the free module on the
vectors of the representation maps onto it, and the functions on the group with values in that free
module map onto the representation by summing the values after undoing the translation.  The
functions on the group have no complete cohomology, so the connecting map of the resulting short
exact sequence identifies the complete cohomology of the representation in a degree with that of
the kernel one degree higher.

The kernel sits inside functions with values in a free module over the integers, so it has no
torsion at any prime, and the vanishing of the complete cohomology of the representation in two
consecutive degrees becomes the same vanishing for the kernel.  For a `p`-group that forces the
kernel to have no complete cohomology at all, and therefore the representation too.

## Main definitions

* `InverseGalois.CFT.Tate.kerObj`: the kernel of a map of representations.
* `InverseGalois.CFT.Tate.freeHom`: the canonical surjection onto a representation from the
  functions on the group with values in the free module on its vectors.

## Main results

* `InverseGalois.CFT.Tate.kerSeq_shortExact`: **the kernel of a surjection of representations sits
  in a short exact sequence.**
* `InverseGalois.CFT.Tate.isZero_tateModule_of_isZero_two`: **a representation of a `p`-group over
  the integers whose complete cohomology vanishes in two consecutive degrees has none in any
  degree.**

## Tags

Tate cohomology, cohomologically trivial, p-group, free resolution
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### The kernel of a map of representations -/

section Kernel

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {N A : Rep k G} (Φ : N ⟶ A)

omit [Finite G] in
/-- The kernel of a map of representations is stable. -/
theorem ker_hom_le_comap (g : G) :
    LinearMap.ker Φ.hom.hom ≤ (LinearMap.ker Φ.hom.hom).comap (N.ρ g) := by
  intro f hf
  have h := LinearMap.congr_fun (hom_equivariant Φ g) f
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp hf, map_zero] at h
  exact LinearMap.mem_ker.mpr h

/-- **The kernel of a map of representations.** -/
def kerObj : Rep k G :=
  Rep.of (N.ρ.subrepresentation (LinearMap.ker Φ.hom.hom) (ker_hom_le_comap Φ))

omit [Finite G] in
theorem subtype_comp_kerObj (g : G) :
    (LinearMap.ker Φ.hom.hom).subtype ∘ₗ (kerObj Φ).ρ g
      = N.ρ g ∘ₗ (LinearMap.ker Φ.hom.hom).subtype :=
  LinearMap.ext fun _ => rfl

/-- **The short exact sequence of the kernel of a surjection of representations.** -/
def kerSeq : ShortComplex (Rep k G) where
  X₁ := kerObj Φ
  X₂ := N
  X₃ := A
  f := mkHom (LinearMap.ker Φ.hom.hom).subtype (subtype_comp_kerObj Φ)
  g := Φ
  zero := by
    ext x
    exact x.2

omit [Finite G] in
/-- **The kernel of a surjection of representations sits in a short exact sequence.** -/
theorem kerSeq_shortExact (hΦ : Function.Surjective Φ.hom.hom) : (kerSeq Φ).ShortExact :=
  shortExact_of_linearMap (Submodule.injective_subtype _) hΦ fun x hx => ⟨⟨x, hx⟩, rfl⟩

omit [Finite G] in
/-- **The kernel has no torsion at `p` as soon as the source has none.** -/
theorem nsmul_eq_zero_kerObj {p : ℕ} (hN : ∀ w : ↥N.V, p • w = 0 → w = 0) :
    ∀ v : ↥(kerObj Φ).V, p • v = 0 → v = 0 := by
  have h : ∀ w : ↥(LinearMap.ker Φ.hom.hom), p • w = 0 → w = 0 := fun w hw =>
    Subtype.ext (hN (w : ↥N.V) (by simpa using congrArg Subtype.val hw))
  exact h

end Kernel

/-! ### The free cover of a representation -/

section Free

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G)

/-- **The canonical map onto a representation from the free module on its vectors.** -/
def freeProj : (↥A.V →₀ k) →ₗ[k] ↥A.V := Finsupp.linearCombination k id

omit [Finite G] in
theorem freeProj_surjective : Function.Surjective (freeProj A) := fun v =>
  ⟨Finsupp.single v 1, by simp [freeProj]⟩

/-- **The functions on the group with values in the free module on the vectors of a
representation.** -/
def freeObj : Rep k G := Rep.of (inducedRep k G (↥A.V →₀ k))

/-- **The underlying map of the free cover**, which spreads a vector out over the free module and
then sums the values after undoing the translation. -/
def freeHomLinear : (G → (↥A.V →₀ k)) →ₗ[k] ↥A.V :=
  augMap A.ρ ∘ₗ (freeProj A).compLeft G

theorem freeHomLinear_equivariant (g : G) :
    freeHomLinear A ∘ₗ (freeObj A).ρ g = A.ρ g ∘ₗ freeHomLinear A := by
  have h1 : (freeProj A).compLeft G ∘ₗ inducedRep k G (↥A.V →₀ k) g
      = inducedRep k G ↥A.V g ∘ₗ (freeProj A).compLeft G := LinearMap.ext fun _ => rfl
  rw [freeHomLinear, LinearMap.comp_assoc,
    show (freeObj A).ρ g = inducedRep k G (↥A.V →₀ k) g from rfl, h1, ← LinearMap.comp_assoc,
    augMap_comp_inducedRep, LinearMap.comp_assoc]

/-- **The canonical surjection onto a representation from an induced free one.** -/
def freeHom : freeObj A ⟶ A := mkHom (freeHomLinear A) (freeHomLinear_equivariant A)

theorem freeHom_surjective : Function.Surjective (freeHom A).hom.hom := by
  have h : Function.Surjective (freeHomLinear A) := by
    rw [freeHomLinear, LinearMap.coe_comp]
    exact (augMap_surjective A.ρ).comp (freeProj_surjective A).comp_left
  exact h

theorem isZero_tateModule_freeObj (n : ℤ) : Limits.IsZero (tateModule (freeObj A) n) :=
  isZero_tateModule_inducedRep n

end Free

/-! ### Two consecutive degrees over the integers -/

section Int

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Fact p.Prime] in
/-- **A finitely supported family of integers killed by a nonzero number vanishes.** -/
theorem eq_zero_of_nsmul_eq_zero_finsupp {α : Type*} (hp : p ≠ 0) (f : α →₀ ℤ)
    (hf : p • f = 0) : f = 0 := by
  ext a
  have h : p • f a = 0 := by simpa using congrArg (fun g : α →₀ ℤ => g a) hf
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.1 h with h' | h'
  · exact absurd (Nat.cast_eq_zero.1 h') hp
  · simpa using h'

omit [Fact p.Prime] [Finite G] in
/-- **The free cover has no torsion at a nonzero number.** -/
theorem nsmul_eq_zero_freeObj (A : Rep ℤ G) (hp : p ≠ 0) :
    ∀ w : ↥(freeObj A).V, p • w = 0 → w = 0 := by
  have h : ∀ w : G → (↥A.V →₀ ℤ), p • w = 0 → w = 0 := fun w hw =>
    funext fun x => eq_zero_of_nsmul_eq_zero_finsupp hp (w x) (congrFun hw x)
  exact h

/-- **A representation of a `p`-group over the integers whose complete cohomology vanishes in two
consecutive degrees has none in any degree.** -/
theorem isZero_tateModule_of_isZero_two (hG : IsPGroup p G) (A : Rep ℤ G) {i : ℤ}
    (hi : Limits.IsZero (tateModule A i)) (hi1 : Limits.IsZero (tateModule A (i + 1))) (n : ℤ) :
    Limits.IsZero (tateModule A n) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).pos.ne'
  have hX : (kerSeq (freeHom A)).ShortExact := kerSeq_shortExact _ (freeHom_surjective A)
  have hbij : ∀ m : ℤ, Function.Bijective (tateδ hX m) := fun m =>
    bijective_tateδ hX m (isZero_tateModule_freeObj A m) (isZero_tateModule_freeObj A (m + 1))
  have htf : ∀ v : ↥(kerObj (freeHom A)).V, p • v = 0 → v = 0 :=
    nsmul_eq_zero_kerObj _ (nsmul_eq_zero_freeObj A hp)
  have hR1 : Limits.IsZero (tateModule (kerObj (freeHom A)) (i + 1)) := by
    refine isZero_of_forall_eq_zero fun y => ?_
    obtain ⟨x, rfl⟩ := (hbij i).2 y
    rw [eq_zero_of_isZero hi x, map_zero]
  have hR2 : Limits.IsZero (tateModule (kerObj (freeHom A)) (i + 1 + 1)) := by
    refine isZero_of_forall_eq_zero fun y => ?_
    obtain ⟨x, rfl⟩ := (hbij (i + 1)).2 y
    rw [eq_zero_of_isZero hi1 x, map_zero]
  have hR : ∀ j : ℤ, Limits.IsZero (tateModule (kerObj (freeHom A)) j) :=
    isZero_tateModule_of_isZero_two_int hG _ htf hR1 hR2
  refine isZero_of_forall_eq_zero fun x => (hbij n).1 ?_
  exact (eq_zero_of_isZero (hR (n + 1)) _).trans (eq_zero_of_isZero (hR (n + 1)) _).symm

end Int

end

end InverseGalois.CFT.Tate
