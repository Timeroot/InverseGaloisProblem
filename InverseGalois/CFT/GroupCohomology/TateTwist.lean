/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.Duality

/-!
# Twisting a representation by a character

A character of a group with values in the units of the coefficient field makes the field itself
into a one dimensional representation, and multiplying the action of an arbitrary representation
by that character produces the *twist* of the representation.  Twisting is compatible with the two
constructions that build new representations out of old ones by conjugation: the linear maps into
the one dimensional representation of a character are the dual representation twisted by the
character, and the dual of a twist is the dual twisted by the inverse character.  Together with the
evaluation isomorphism onto the double dual these identities say that for a finite dimensional
representation the dual of the linear maps into the representation of a character is the twist by
the inverse character — the shape in which a Tate twist appears.

Combining this with the duality between the first homology of the contragredient representation and
the first cohomology, the first homology of a twist surjects onto the dual of any subspace of the
first cohomology of the linear maps into the character.

## Main definitions

* `InverseGalois.CFT.charRepresentation` and `InverseGalois.CFT.charRep`: the one dimensional
  representation attached to a character.
* `InverseGalois.CFT.twistRepresentation` and `InverseGalois.CFT.twistRep`: a representation
  twisted by a character.
* `InverseGalois.CFT.homRep`: the representation on the linear maps between two representations.
* `InverseGalois.CFT.dualHomCharIso`: the dual of the linear maps into the representation of a
  character, identified with the twist by the inverse character.

## Main results

* `InverseGalois.CFT.linHom_charRepresentation` and
  `InverseGalois.CFT.dual_twistRepresentation`: the two compatibilities of twisting with
  conjugation.
* `InverseGalois.CFT.h1TwistEquiv`: **the first homology of the twist by the inverse character is
  the dual of the first cohomology of the linear maps into the character.**
* `InverseGalois.CFT.exists_h1Twist_surjective`: the first homology of the twist by the inverse
  character surjects onto the dual of any subspace of that first cohomology.

## Tags

representation, character, twist, Tate twist, group cohomology, group homology, duality
-/

universe u

namespace InverseGalois.CFT

open Module (Dual)

/-! ### Characters and twists -/

section Twist

variable {k G V : Type u} [Field k] [Group G] [AddCommGroup V] [Module k V]

variable (k) in
/-- The one dimensional representation attached to a character of the group. -/
def charRepresentation (χ : G →* kˣ) : Representation k G k where
  toFun g := (χ g : k) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [Module.End.mul_apply, mul_smul, mul_comm]

@[simp]
theorem charRepresentation_apply (χ : G →* kˣ) (g : G) (x : k) :
    charRepresentation k χ g x = (χ g : k) * x := by
  simp [charRepresentation, smul_eq_mul]

/-- A representation twisted by a character: the action of a group element is multiplied by the
value of the character at that element. -/
def twistRepresentation (ρ : Representation k G V) (χ : G →* kˣ) : Representation k G V where
  toFun g := (χ g : k) • ρ g
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [Module.End.mul_apply, ← mul_smul, mul_comm]

@[simp]
theorem twistRepresentation_apply (ρ : Representation k G V) (χ : G →* kˣ) (g : G) (x : V) :
    twistRepresentation ρ χ g x = (χ g : k) • ρ g x := rfl

/-- **The linear maps into the representation of a character are the dual twisted by the
character.** -/
theorem linHom_charRepresentation (ρ : Representation k G V) (χ : G →* kˣ) :
    Representation.linHom ρ (charRepresentation k χ)
      = twistRepresentation (Representation.dual ρ) χ := by
  ext g f a
  simp [Module.Dual.transpose_apply]

/-- **The dual of a twist is the dual twisted by the inverse character.** -/
theorem dual_twistRepresentation (ρ : Representation k G V) (χ : G →* kˣ) :
    Representation.dual (twistRepresentation ρ χ)
      = twistRepresentation (Representation.dual ρ) χ⁻¹ := by
  ext g f a
  simp [Module.Dual.transpose_apply]

/-- The evaluation isomorphism intertwines a representation with its double dual. -/
theorem dual_dual_evalEquiv [FiniteDimensional k V] (ρ : Representation k G V) (g : G) (x : V) :
    Representation.dual (Representation.dual ρ) g (Module.evalEquiv k V x)
      = Module.evalEquiv k V (ρ g x) := by
  ext φ
  simp [Module.Dual.transpose_apply]

end Twist

/-! ### The twist of a representation -/

section Rep

variable {k G : Type u} [Field k] [Group G] (A : Rep k G) (χ : G →* kˣ)

/-- The one dimensional representation attached to a character, as an object of `Rep`. -/
noncomputable abbrev charRep : Rep k G := Rep.of (charRepresentation k χ)

/-- A representation twisted by a character, as an object of `Rep`. -/
noncomputable abbrev twistRep : Rep k G := Rep.of (twistRepresentation A.ρ χ)

/-- The representation on the linear maps between two representations, with the group acting by
conjugation. -/
noncomputable abbrev homRep (B : Rep k G) : Rep k G := Rep.of (Representation.linHom A.ρ B.ρ)

/-- **The dual of the linear maps into the representation of a character is the twist by the
inverse character.**  This is the shape in which a Tate twist appears: evaluation carries a finite
dimensional representation onto the double dual, the linear maps into the character are the dual
twisted by the character, and the dual of that twist is the double dual twisted by the inverse
character. -/
noncomputable def dualHomCharIso [FiniteDimensional k A] :
    twistRep A χ⁻¹ ≅ dualRep (homRep A (charRep χ)) :=
  Action.mkIso (Module.evalEquiv k A).toModuleIso fun g => by
    ext x f
    simp [ModuleCat.endRingEquiv, Module.Dual.transpose_apply, charRepresentation,
      twistRepresentation, smul_eq_mul]

end Rep

/-! ### Duality for the twist -/

section Duality

variable {k G : Type u} [Field k] [Group G] (A : Rep k G) (χ : G →* kˣ)
variable [Finite G] [FiniteDimensional k A]

/-- An isomorphism of representations induces an isomorphism on the first homology. -/
noncomputable def h1MapIso {A B : Rep k G} (e : A ≅ B) :
    groupHomology.H1 A ≅ groupHomology.H1 B where
  hom := groupHomology.map (MonoidHom.id G) e.hom 1
  inv := groupHomology.map (MonoidHom.id G) e.inv 1
  hom_inv_id := by rw [← groupHomology.map_id_comp, e.hom_inv_id, groupHomology.map_id]
  inv_hom_id := by rw [← groupHomology.map_id_comp, e.inv_hom_id, groupHomology.map_id]

/-- **The first homology of the twist by the inverse character is the dual of the first cohomology
of the linear maps into the character.** -/
noncomputable def h1TwistEquiv :
    groupHomology.H1 (twistRep A χ⁻¹)
      ≃ₗ[k] Dual k (groupCohomology.H1 (homRep A (charRep χ))) :=
  (h1MapIso (dualHomCharIso A χ)).toLinearEquiv.trans (h1DualEquiv _)

/-- The first homology of the twist by the inverse character surjects onto the dual of any subspace
of the first cohomology of the linear maps into the character. -/
theorem exists_h1Twist_surjective (S : Submodule k (groupCohomology.H1 (homRep A (charRep χ)))) :
    ∃ F : groupHomology.H1 (twistRep A χ⁻¹) →ₗ[k] Dual k ↥S, Function.Surjective F :=
  ⟨(S.subtype.dualMap : Dual k (groupCohomology.H1 (homRep A (charRep χ))) →ₗ[k] Dual k ↥S) ∘ₗ
      (h1TwistEquiv A χ : _ →ₗ[k] _),
    (LinearMap.dualMap_surjective_of_injective S.injective_subtype).comp
      (h1TwistEquiv A χ).surjective⟩

end Duality

end InverseGalois.CFT
