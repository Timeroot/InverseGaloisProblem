/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.DualityNatural
import InverseGalois.CFT.TateCohomology.NakayamaNatural
import InverseGalois.CFT.TateCohomology.Pontryagin

/-!
# The complete cohomology of a representation with finitely many vectors is a dual

The duality of complete cohomology reads the classes of one degree as characters of the classes of
the functionals in the complementary degree.  For a representation with finitely many vectors the
reading can be turned around: a finite abelian group is recovered from its characters, so the
evaluation of a representation in the functionals on its functionals is an isomorphism of
representations, and moving it through complete cohomology identifies **the classes of a
representation with the characters of the classes of its functionals**.

The identification is compatible with every map of representations, and, because the rational
circle satisfies the criterion of Baer, every character defined only on a submodule of the
complementary cohomology extends; so **every character of a submodule is the pairing against some
class**.  That surjectivity is the shape a duality argument needs when the submodule is cut out by
local conditions and one wants a global class inducing a prescribed functional on it.

## Main definitions

* `InverseGalois.CFT.Tate.doubleDualHom`: **the evaluation of a representation in the functionals
  on its functionals.**
* `InverseGalois.CFT.Tate.tateDualPairing`: **the classes of a representation with finitely many
  vectors, as the characters of the classes of its functionals in the complementary degree.**

## Main results

* `InverseGalois.CFT.Tate.doubleDualHom_naturality`: evaluation is compatible with every map of
  representations.
* `InverseGalois.CFT.Tate.tateDualPairing_naturality`: **the duality of complete cohomology is
  compatible with every map of representations.**
* `InverseGalois.CFT.Tate.exists_tateDualPairing_eq`: **every character of a submodule of the
  complete cohomology of the functionals is the pairing against a class of the complementary
  degree.**

## Tags

Tate cohomology, duality, double dual, character module, rational circle
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

noncomputable section

universe u

/-! ### Complete cohomology along an invertible map -/

section Bijective

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **A map of representations with a two-sided inverse induces a bijection on complete
cohomology.** -/
theorem bijective_tateMap_of_comp {A B : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ A)
    (h₁ : φ ≫ ψ = 𝟙 A) (h₂ : ψ ≫ φ = 𝟙 B) (n : ℤ) : Function.Bijective (tateMap φ n) := by
  refine ⟨fun x y h => ?_, fun y => ⟨tateMap ψ n y, ?_⟩⟩
  · have h' := congrArg (tateMap ψ n) h
    rwa [tateMap_comp_apply, tateMap_comp_apply, h₁, tateMap_id_apply, tateMap_id_apply] at h'
  · rw [tateMap_comp_apply, h₂, tateMap_id_apply]

end Bijective

/-! ### The functionals on the functionals -/

section DoubleDual

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (C : Type u)
  [AddCommGroup C] [Module k C]

/-- The evaluation of a representation in the functionals on its functionals. -/
def doubleDualLinear : ↥A.V →ₗ[k] (↥(coeffDualObj A C).V →ₗ[k] C) :=
  LinearMap.flip LinearMap.id

theorem doubleDualLinear_apply (v : ↥A.V) (f : ↥A.V →ₗ[k] C) :
    doubleDualLinear A C v f = f v := rfl

theorem doubleDualLinear_equivariant (g : G) :
    doubleDualLinear A C ∘ₗ A.ρ g = coeffDual (coeffDual A.ρ C) C g ∘ₗ doubleDualLinear A C := by
  refine LinearMap.ext fun v => LinearMap.ext fun (f : ↥A.V →ₗ[k] C) => ?_
  show f (A.ρ g v) = f (A.ρ g⁻¹⁻¹ v)
  rw [inv_inv]

/-- **The evaluation of a representation in the functionals on its functionals**, as a map of
representations. -/
def doubleDualHom : A ⟶ coeffDualObj (coeffDualObj A C) C :=
  mkHom (doubleDualLinear A C) (doubleDualLinear_equivariant A C)

theorem doubleDualHom_hom : (doubleDualHom A C).hom.hom = doubleDualLinear A C := rfl

end DoubleDual

section Natural

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} (φ : A ⟶ B)
  (C : Type u) [AddCommGroup C] [Module k C]

/-- **Evaluation is compatible with every map of representations.** -/
theorem doubleDualHom_naturality :
    φ ≫ doubleDualHom B C = doubleDualHom A C ≫ coeffDualHom (coeffDualHom φ C) C :=
  Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl))

end Natural

/-! ### The duality for a representation with finitely many vectors -/

section FiniteRep

variable {G : Type} [Group G] [Finite G] (A : Rep ℤ G) [Finite ↥A.V]

omit [Finite G] in
/-- **A representation with finitely many vectors is the functionals on its functionals.** -/
theorem bijective_doubleDualLinear :
    Function.Bijective (doubleDualLinear A (AddCircle (1 : ℚ))) :=
  bijective_evalDual ↥A.V

instance isIso_doubleDualHom : IsIso (doubleDualHom A (AddCircle (1 : ℚ))) := by
  haveI : IsIso (doubleDualHom A (AddCircle (1 : ℚ))).hom :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_doubleDualLinear A)
  infer_instance

theorem bijective_tateMap_doubleDualHom (n : ℤ) :
    Function.Bijective (tateMap (doubleDualHom A (AddCircle (1 : ℚ))) n) :=
  bijective_tateMap_of_comp _ (CategoryTheory.inv (doubleDualHom A (AddCircle (1 : ℚ))))
    (IsIso.hom_inv_id _) (IsIso.inv_hom_id _) n

/-- **The complete cohomology of a representation with finitely many vectors is the characters of
the complete cohomology of its functionals in the complementary degree.** -/
def tateDualPairing (n : ℤ) :
    ↥(tateModule A n) ≃ₗ[ℤ]
      (↥(tateModule (coeffDualObj A (AddCircle (1 : ℚ))) (-n - 1)) →ₗ[ℤ] AddCircle (1 : ℚ)) :=
  (LinearEquiv.ofBijective (tateMap (doubleDualHom A (AddCircle (1 : ℚ))) n).hom
      (bijective_tateMap_doubleDualHom A n)).trans
    (tateCharacterEquiv (coeffDualObj A (AddCircle (1 : ℚ))) n)

theorem tateDualPairing_apply (n : ℤ) (x : ↥(tateModule A n))
    (z : ↥(tateModule (coeffDualObj A (AddCircle (1 : ℚ))) (-n - 1))) :
    tateDualPairing A n x z
      = tateCharacterEquiv (coeffDualObj A (AddCircle (1 : ℚ))) n
        (tateMap (doubleDualHom A (AddCircle (1 : ℚ))) n x) z := rfl

end FiniteRep

section FiniteNatural

variable {G : Type} [Group G] [Finite G] {A B : Rep ℤ G} [Finite ↥A.V] [Finite ↥B.V]

/-- **The duality of complete cohomology is compatible with every map of representations.** -/
theorem tateDualPairing_naturality (φ : A ⟶ B) (n : ℤ) (x : ↥(tateModule A n))
    (z : ↥(tateModule (coeffDualObj B (AddCircle (1 : ℚ))) (-n - 1))) :
    tateDualPairing B n (tateMap φ n x) z
      = tateDualPairing A n x (tateMap (coeffDualHom φ (AddCircle (1 : ℚ))) (-n - 1) z) := by
  rw [tateDualPairing_apply, tateDualPairing_apply, tateMap_comp_apply,
    doubleDualHom_naturality φ, ← tateMap_comp_apply]
  exact tateCharacterEquiv_naturality n (coeffDualHom φ (AddCircle (1 : ℚ))) _ z

end FiniteNatural

/-! ### Realising a character of a submodule -/

section Realise

variable {G : Type} [Group G] [Finite G] (A : Rep ℤ G) [Finite ↥A.V]

/-- **Every character of a submodule of the complete cohomology of the functionals is realised by a
class of the complementary degree.** -/
theorem exists_tateDualPairing_eq (n : ℤ) {T : Type} [AddCommGroup T] [Module ℤ T]
    (ι : T →ₗ[ℤ] ↥(tateModule (coeffDualObj A (AddCircle (1 : ℚ))) (-n - 1)))
    (hι : Function.Injective ι) (χ : T →ₗ[ℤ] AddCircle (1 : ℚ)) :
    ∃ x : ↥(tateModule A n), ∀ t : T, tateDualPairing A n x (ι t) = χ t := by
  obtain ⟨χ', hχ'⟩ := baer_addCircle.extension_property ι hι χ
  refine ⟨(tateDualPairing A n).symm χ', fun t => ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun hχ' t

end Realise

end

end InverseGalois.CFT.Tate
