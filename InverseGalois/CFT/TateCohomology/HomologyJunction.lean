/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Junction

/-!
# Passing from degree minus two to degree minus one

For a finite group the complete cohomology in degree minus one is the classes in the coinvariants
killed by the norm, while in degrees below minus one it is the ordinary homology.  A short exact
sequence of representations has a connecting map from the first homology of the quotient to the
coinvariants of the sub, and the classes it produces are killed by the norm: their images in the
coinvariants of the middle term vanish, and the norm of an injection is again injective on the
invariants.  The connecting map therefore lands in the complete cohomology in degree minus one.

The three term sequence obtained in this way is exact at both of its inner spots, which is what
attaches the ordinary homology in degree one to the complete cohomology in degree minus one.

## Main definitions

* `InverseGalois.CFT.Tate.H1toHm1`: the connecting map from the first homology of the quotient to
  the Tate group in degree minus one of the sub.

## Main results

* `InverseGalois.CFT.Tate.exact_H1_H1toHm1`: exactness at the first homology.
* `InverseGalois.CFT.Tate.exact_H1toHm1_Hm1`: exactness at the Tate group in degree minus one.

## Tags

Tate cohomology, connecting homomorphism, long exact sequence
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-! ### Comparison with the coinvariants functor -/

omit [Fintype G] in
/-- The coinvariants functor agrees with the map induced on coinvariants by an equivariant map. -/
theorem coinvariantsFunctor_map_apply {A B : Rep k G} (φ : A ⟶ B) (x : Coinvariants A.ρ) :
    (Rep.coinvariantsFunctor k G).map φ x
      = Coinvariants.map A.ρ B.ρ φ.hom.hom (hom_equivariant φ) x := rfl

omit [Fintype G] in
/-- **The isomorphism between the homology in degree zero and the coinvariants is natural.** -/
theorem map_homology_H0Iso_hom {A B : Rep k G} (φ : A ⟶ B) (t : groupHomology A 0) :
    (groupHomology.H0Iso B).hom (groupHomology.map (MonoidHom.id G) φ 0 t)
      = Coinvariants.map A.ρ B.ρ φ.hom.hom (hom_equivariant φ)
        ((groupHomology.H0Iso A).hom t) := by
  have h := congrArg (fun m : groupHomology A 0 ⟶ (Rep.coinvariantsFunctor k G).obj B => m t)
    (groupHomology.map_id_comp_H0Iso_hom φ)
  simpa only [CategoryTheory.comp_apply] using h

/-! ### The connecting map into degree minus one -/

section Junction

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

/-- **The connecting map lands in the classes killed by the norm.** -/
theorem coinvariantsNorm_delta (z : groupHomology X.X₃ 1) :
    coinvariantsNorm X.X₁.ρ
      ((groupHomology.H0Iso X.X₁).hom (groupHomology.δ hX 1 0 rfl z)) = 0 := by
  have hrk := (groupHomology.mapShortComplex₁_exact hX (i := 1) (j := 0)
    rfl).moduleCat_range_eq_ker
  have h1 : groupHomology.δ hX 1 0 rfl z ∈
      LinearMap.range (groupHomology.mapShortComplex₁ hX (i := 1) (j := 0) rfl).f.hom := ⟨z, rfl⟩
  rw [hrk] at h1
  have h2 : groupHomology.map (MonoidHom.id G) X.f 0 (groupHomology.δ hX 1 0 rfl z) = 0 := h1
  have h3 : Coinvariants.map X.X₁.ρ X.X₂.ρ X.f.hom.hom (hom_equivariant X.f)
      ((groupHomology.H0Iso X.X₁).hom (groupHomology.δ hX 1 0 rfl z)) = 0 := by
    rw [← map_homology_H0Iso_hom X.f, h2, map_zero]
  refine invariantsMap_injective X.f.hom.hom (hom_equivariant X.f)
    ((Rep.mono_iff_injective X.f).1 hX.mono_f) ?_
  rw [map_zero, ← LinearMap.comp_apply,
    ← coinvariantsNorm_comp_coinvariantsMap X.f.hom.hom (hom_equivariant X.f),
    LinearMap.comp_apply, h3, map_zero]

/-- **The connecting map from the first homology of the quotient to the Tate group in degree
minus one of the sub.** -/
def H1toHm1 : groupHomology X.X₃ 1 →ₗ[k] Hm1 X.X₁.ρ :=
  LinearMap.codRestrict _
    ((groupHomology.H0Iso X.X₁).hom.hom ∘ₗ (groupHomology.δ hX 1 0 rfl).hom)
    fun z => LinearMap.mem_ker.mpr (coinvariantsNorm_delta hX z)

theorem H1toHm1_coe (z : groupHomology X.X₃ 1) :
    (H1toHm1 hX z : Coinvariants X.X₁.ρ)
      = (groupHomology.H0Iso X.X₁).hom (groupHomology.δ hX 1 0 rfl z) := rfl

/-! ### Exactness -/

/-- **The three term sequence is exact at the first homology.** -/
theorem exact_H1_H1toHm1 :
    Function.Exact (groupHomology.map (MonoidHom.id G) X.g 1).hom (H1toHm1 hX) := by
  have hrk := (groupHomology.mapShortComplex₃_exact hX (i := 1) (j := 0)
    rfl).moduleCat_range_eq_ker
  intro z
  constructor
  · intro hz
    have hd : groupHomology.δ hX 1 0 rfl z = 0 := by
      refine (groupHomology.H0Iso X.X₁).toLinearEquiv.injective ?_
      rw [map_zero]
      exact congrArg Subtype.val hz
    have hm : z ∈ LinearMap.ker
        (groupHomology.mapShortComplex₃ hX (i := 1) (j := 0) rfl).g.hom := hd
    rw [← hrk] at hm
    exact hm
  · rintro ⟨w, rfl⟩
    have hm : groupHomology.map (MonoidHom.id G) X.g 1 w ∈ LinearMap.range
        (groupHomology.mapShortComplex₃ hX (i := 1) (j := 0) rfl).f.hom := ⟨w, rfl⟩
    rw [hrk] at hm
    have hd : groupHomology.δ hX 1 0 rfl (groupHomology.map (MonoidHom.id G) X.g 1 w) = 0 := hm
    refine Subtype.ext ?_
    rw [H1toHm1_coe, hd]
    simp

/-- **The three term sequence is exact at the Tate group in degree minus one.** -/
theorem exact_H1toHm1_Hm1 :
    Function.Exact (H1toHm1 hX) (Hm1map X.f.hom.hom (hom_equivariant X.f)) := by
  have hrk := (groupHomology.mapShortComplex₁_exact hX (i := 1) (j := 0)
    rfl).moduleCat_range_eq_ker
  intro w
  constructor
  · intro hw
    have hc : Coinvariants.map X.X₁.ρ X.X₂.ρ X.f.hom.hom (hom_equivariant X.f)
        (w : Coinvariants X.X₁.ρ) = 0 := congrArg Subtype.val hw
    obtain ⟨u, hu⟩ : ∃ u, (groupHomology.H0Iso X.X₁).hom u = (w : Coinvariants X.X₁.ρ) :=
      ⟨(groupHomology.H0Iso X.X₁).inv (w : Coinvariants X.X₁.ρ), Iso.inv_hom_id_apply _ _⟩
    have h0 : groupHomology.map (MonoidHom.id G) X.f 0 u = 0 := by
      refine (groupHomology.H0Iso X.X₂).toLinearEquiv.injective ?_
      rw [map_zero]
      have h := map_homology_H0Iso_hom X.f u
      rw [hu, hc] at h
      exact h
    obtain ⟨t, ht⟩ : u ∈ LinearMap.range
        (groupHomology.mapShortComplex₁ hX (i := 1) (j := 0) rfl).f.hom := by
      rw [hrk]
      exact h0
    refine ⟨t, Subtype.ext ?_⟩
    have ht' : groupHomology.δ hX 1 0 rfl t = u := ht
    rw [H1toHm1_coe, ht']
    exact hu
  · rintro ⟨t, rfl⟩
    have hm : groupHomology.δ hX 1 0 rfl t ∈ LinearMap.range
        (groupHomology.mapShortComplex₁ hX (i := 1) (j := 0) rfl).f.hom := ⟨t, rfl⟩
    rw [hrk] at hm
    have h0 : groupHomology.map (MonoidHom.id G) X.f 0 (groupHomology.δ hX 1 0 rfl t) = 0 := hm
    refine Subtype.ext ?_
    rw [Hm1map_coe, H1toHm1_coe, ← map_homology_H0Iso_hom X.f, h0]
    simp

end Junction

end

end InverseGalois.CFT.Tate
