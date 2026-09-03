/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.DeltaNatural
import InverseGalois.CFT.TateCohomology.Shifting

/-!
# The shift and the coshift are functors, and the degree shift is natural

A map of representations induces a map of the functions on the group, by composing a function with
it.  That map carries the record of the translates of a vector to the record of the translates of
its image, so it descends to the shifts; and it commutes with the summation, so it restricts to the
coshifts.  Both sequences defining the shift and the coshift are therefore functorial, with the map
of the functions on the group in the middle.

The identification of the complete cohomology of the shift in a degree with that of the
representation in the following degree is the connecting map of the first of those sequences, and
the identification of the complete cohomology of a representation with that of its coshift is the
connecting map of the second.  Since the connecting map commutes with a map of short exact
sequences, **both identifications commute with a map of representations.**  That is what a
dimension shifting argument needs in order to be carried along a diagram rather than applied to one
representation at a time.

## Main definitions

* `InverseGalois.CFT.Tate.indHom`, `InverseGalois.CFT.Tate.shiftHom`,
  `InverseGalois.CFT.Tate.coshiftHom`: the maps induced on the functions on the group, on the shift
  and on the coshift.

## Main results

* `InverseGalois.CFT.Tate.tateShiftEquiv_naturality`: **the complete cohomology of the shift in a
  degree is the complete cohomology of the representation in the following degree, naturally in the
  representation.**
* `InverseGalois.CFT.Tate.tateCoshiftEquiv_naturality`: **the complete cohomology of a
  representation in a degree is the complete cohomology of its coshift in the following degree,
  naturally in the representation.**

## Tags

Tate cohomology, dimension shifting, naturality, connecting homomorphism
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {A B C : Rep k G} (φ : A ⟶ B)

/-! ### The functions on the group -/

section Induced

omit [Finite G] in
theorem compLeft_equivariant (g : G) :
    LinearMap.compLeft φ.hom.hom G ∘ₗ inducedRep k G ↥A.V g
      = inducedRep k G ↥B.V g ∘ₗ LinearMap.compLeft φ.hom.hom G :=
  LinearMap.ext fun _ => rfl

/-- **A map of representations, composed with the functions on the group.** -/
def indHom : indObj A ⟶ indObj B :=
  mkHom (LinearMap.compLeft φ.hom.hom G) (compLeft_equivariant φ)

omit [Finite G] in
@[simp]
theorem indHom_hom (f : G → ↥A.V) (x : G) : (indHom φ).hom.hom f x = φ.hom.hom (f x) := rfl

end Induced

/-! ### The shift -/

section Shift

omit [Finite G] in
/-- The record of the translates of a vector is carried to the record of the translates of its
image. -/
theorem range_coindEmb_le_comap_compLeft :
    LinearMap.range (coindEmb A.ρ)
      ≤ (LinearMap.range (coindEmb B.ρ)).comap (LinearMap.compLeft φ.hom.hom G) := by
  rintro _ ⟨v, rfl⟩
  exact ⟨φ.hom.hom v, funext fun x => (LinearMap.congr_fun (hom_equivariant φ x) v).symm⟩

/-- The map of the shifts underlying a map of representations. -/
def shiftLinear : ↥(shiftObj A).V →ₗ[k] ↥(shiftObj B).V :=
  Submodule.mapQ _ _ (LinearMap.compLeft φ.hom.hom G) (range_coindEmb_le_comap_compLeft φ)

omit [Finite G] in
theorem shiftLinear_mkQ (f : G → ↥A.V) :
    shiftLinear φ ((LinearMap.range (coindEmb A.ρ)).mkQ f)
      = (LinearMap.range (coindEmb B.ρ)).mkQ (LinearMap.compLeft φ.hom.hom G f) := rfl

omit [Finite G] in
theorem shiftLinear_equivariant (g : G) :
    shiftLinear φ ∘ₗ (shiftObj A).ρ g = (shiftObj B).ρ g ∘ₗ shiftLinear φ := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ q
  rfl

/-- **A map of representations, on the shifts.** -/
def shiftHom : shiftObj A ⟶ shiftObj B :=
  mkHom (shiftLinear φ) (shiftLinear_equivariant φ)

omit [Finite G] in
theorem shiftHom_id : shiftHom (𝟙 A) = 𝟙 (shiftObj A) := by
  refine Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun q => ?_))
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ q
  rfl

omit [Finite G] in
theorem shiftHom_comp (ψ : B ⟶ C) : shiftHom φ ≫ shiftHom ψ = shiftHom (φ ≫ ψ) := by
  refine Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun q => ?_))
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ q
  rfl

/-- **The sequence defining the shift is functorial.** -/
def shiftSeqHom : shiftSeq A ⟶ shiftSeq B where
  τ₁ := φ
  τ₂ := indHom φ
  τ₃ := shiftHom φ
  comm₁₂ := by
    refine Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun v => funext fun x => ?_))
    exact (LinearMap.congr_fun (hom_equivariant φ x) v).symm
  comm₂₃ := rfl

/-- **The complete cohomology of the shift in a degree is the complete cohomology of the
representation in the following degree, naturally in the representation.** -/
theorem tateShiftEquiv_naturality (n : ℤ) (x : ↥(tateModule (shiftObj A) n)) :
    tateMap φ (n + 1) (tateShiftEquiv A n x) = tateShiftEquiv B n (tateMap (shiftHom φ) n x) :=
  tateδ_naturality_apply (shiftSeq_shortExact A) (shiftSeq_shortExact B) (shiftSeqHom φ) n x

end Shift

/-! ### The coshift -/

section Coshift

theorem augMap_compLeft (f : G → ↥A.V) :
    augMap B.ρ (LinearMap.compLeft φ.hom.hom G f) = φ.hom.hom (augMap A.ρ f) := by
  letI := Fintype.ofFinite G
  rw [augMap_apply, augMap_apply, map_sum]
  exact Finset.sum_congr rfl fun x _ => (LinearMap.congr_fun (hom_equivariant φ x⁻¹) (f x)).symm

/-- A function whose values sum to zero is carried to one whose values sum to zero. -/
theorem compLeft_mem_ker_augMap (f : G → ↥A.V) (hf : f ∈ LinearMap.ker (augMap A.ρ)) :
    LinearMap.compLeft φ.hom.hom G f ∈ LinearMap.ker (augMap B.ρ) := by
  refine LinearMap.mem_ker.mpr ?_
  rw [augMap_compLeft φ f, LinearMap.mem_ker.mp hf, map_zero]

/-- The map of the coshifts underlying a map of representations. -/
def coshiftLinear : ↥(coshiftObj A).V →ₗ[k] ↥(coshiftObj B).V :=
  (LinearMap.compLeft φ.hom.hom G).restrict (compLeft_mem_ker_augMap φ)

theorem coshiftLinear_coe (z : ↥(coshiftObj A).V) :
    (coshiftLinear φ z).1 = LinearMap.compLeft φ.hom.hom G z.1 := rfl

theorem coshiftLinear_equivariant (g : G) :
    coshiftLinear φ ∘ₗ (coshiftObj A).ρ g = (coshiftObj B).ρ g ∘ₗ coshiftLinear φ :=
  LinearMap.ext fun _ => Subtype.ext rfl

/-- **A map of representations, on the coshifts.** -/
def coshiftHom : coshiftObj A ⟶ coshiftObj B :=
  mkHom (coshiftLinear φ) (coshiftLinear_equivariant φ)

theorem coshiftHom_id : coshiftHom (𝟙 A) = 𝟙 (coshiftObj A) :=
  Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl))

theorem coshiftHom_comp (ψ : B ⟶ C) : coshiftHom φ ≫ coshiftHom ψ = coshiftHom (φ ≫ ψ) :=
  Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl))

/-- **The sequence defining the coshift is functorial.** -/
def coshiftSeqHom : coshiftSeq A ⟶ coshiftSeq B where
  τ₁ := coshiftHom φ
  τ₂ := indHom φ
  τ₃ := φ
  comm₁₂ := rfl
  comm₂₃ := by
    refine Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun f => ?_))
    exact augMap_compLeft φ f

/-- **The complete cohomology of a representation in a degree is the complete cohomology of its
coshift in the following degree, naturally in the representation.** -/
theorem tateCoshiftEquiv_naturality (n : ℤ) (x : ↥(tateModule A n)) :
    tateMap (coshiftHom φ) (n + 1) (tateCoshiftEquiv A n x)
      = tateCoshiftEquiv B n (tateMap φ n x) :=
  tateδ_naturality_apply (coshiftSeq_shortExact A) (coshiftSeq_shortExact B) (coshiftSeqHom φ) n x

end Coshift

end

end InverseGalois.CFT.Tate
