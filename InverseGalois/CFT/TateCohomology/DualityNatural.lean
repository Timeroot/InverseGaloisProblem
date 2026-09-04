/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.DualityDivisible
import InverseGalois.CFT.TateCohomology.ShiftNatural

/-!
# The duality of complete cohomology along a map of representations

A map of representations carries a functional on the target to a functional on the source, and that
reading is itself a map of representations, in the opposite direction.  Each of the three pieces the
duality of complete cohomology is assembled from respects it: the pairing of the two middle degrees,
the identification of the coshift of the functionals with the functionals on the shift, and the
identification of the shift of the functionals with the functionals on the coshift.  Since every
degree is reached from degree zero by a chain of the last two, **the duality is compatible with
every map of representations in every degree**: dualizing a class and restricting the resulting
functional along the map gives the same functional as moving the class along the dual map and then
dualizing.

That compatibility is what a duality statement about an image needs.  A class of the complete
cohomology lies in the image of a map exactly when every functional killing that image kills it, so
a question about the image of one map becomes, after dualizing, a question about the kernel of
another — but only once the two maps are known to correspond, which is exactly what is proved here.

## Main definitions

* `InverseGalois.CFT.Tate.coeffDualHom`: **the functionals with fixed coefficients, along a map of
  representations.**
* `InverseGalois.CFT.Tate.IsTateDualNatural`: the compatibility of a family of dualities, one for
  each representation, with the maps of representations.

## Main results

* `InverseGalois.CFT.Tate.tateDualZeroEquiv_naturality`: the pairing of the two middle degrees is
  compatible with a map of representations.
* `InverseGalois.CFT.Tate.coeffDualShiftIso_naturality`,
  `InverseGalois.CFT.Tate.coeffDualCoshiftIso_naturality`: the two identifications that move the
  degree of the functionals are compatible with a map of representations.
* `InverseGalois.CFT.Tate.tateDualEquivOfBaer_naturality`: **the duality of complete cohomology
  against coefficients satisfying the criterion of Baer is compatible with every map of
  representations, in every degree.**
* `InverseGalois.CFT.Tate.tateCharacterEquiv_naturality`: **the characters of the complete
  cohomology of a representation are compatible with every map of representations, in every
  degree.**

## Tags

Tate cohomology, duality, naturality, dual representation, character module
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

noncomputable section

universe u

/-! ### The functionals along a map of representations -/

section Hom

variable {k G : Type u} [CommRing k] [Group G] {A B D : Rep k G} (φ : A ⟶ B) (C : Type u)
  [AddCommGroup C] [Module k C]

/-- The map of the functionals underlying a map of representations. -/
def coeffDualLinear : (↥B.V →ₗ[k] C) →ₗ[k] (↥A.V →ₗ[k] C) :=
  LinearMap.lcomp k C φ.hom.hom

theorem coeffDualLinear_apply (f : ↥B.V →ₗ[k] C) (v : ↥A.V) :
    coeffDualLinear φ C f v = f (φ.hom.hom v) := rfl

theorem coeffDualLinear_equivariant (g : G) :
    coeffDualLinear φ C ∘ₗ coeffDual B.ρ C g = coeffDual A.ρ C g ∘ₗ coeffDualLinear φ C := by
  refine LinearMap.ext fun f => LinearMap.ext fun v => ?_
  show f (B.ρ g⁻¹ (φ.hom.hom v)) = f (φ.hom.hom (A.ρ g⁻¹ v))
  exact congrArg f (LinearMap.congr_fun (hom_equivariant φ g⁻¹) v).symm

/-- **The functionals with fixed coefficients, along a map of representations.**  A functional on
the target is read on the source by composing with the map, which reverses the direction. -/
def coeffDualHom : coeffDualObj B C ⟶ coeffDualObj A C :=
  mkHom (coeffDualLinear φ C) (coeffDualLinear_equivariant φ C)

theorem coeffDualHom_hom : (coeffDualHom φ C).hom.hom = coeffDualLinear φ C := rfl

/-- **The functionals on a representation along the identity are the functionals themselves.** -/
theorem coeffDualHom_id : coeffDualHom (𝟙 A) C = 𝟙 (coeffDualObj A C) :=
  Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl))

/-- **The functionals along a composite are the composite of the functionals**, in the opposite
order. -/
theorem coeffDualHom_comp (ψ : B ⟶ D) :
    coeffDualHom ψ C ≫ coeffDualHom φ C = coeffDualHom (φ ≫ ψ) C :=
  Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl))

end Hom

/-! ### The pairing of the two middle degrees -/

section Zero

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {A B : Rep k G} (φ : A ⟶ B)
  (C : Type u) [AddCommGroup C] [Module k C]

private theorem tateMap_comp_apply' {X Y Z : Rep k G} (α : X ⟶ Y) (β : Y ⟶ Z) (n : ℤ)
    (x : ↥(tateModule X n)) : tateMap β n (tateMap α n x) = tateMap (α ≫ β) n x := by
  rw [tateMap_comp]
  rfl

/-- **The pairing of the two middle degrees is compatible with a map of representations.**  Both
readings of a functional at a class of degree minus one evaluate the functional on the image of a
representative. -/
theorem tateDualZeroEquiv_naturality
    (h₁A : IsExtendableInto k C (LinearMap.range (normMap A.ρ)))
    (h₂A : IsExtendableInto k C (LinearMap.ker (normMap A.ρ)))
    (h₁B : IsExtendableInto k C (LinearMap.range (normMap B.ρ)))
    (h₂B : IsExtendableInto k C (LinearMap.ker (normMap B.ρ)))
    (x : ↥(tateModule (coeffDualObj B C) 0)) (z : ↥(tateModule A (-1))) :
    tateDualZeroEquiv A C h₁A h₂A (tateMap (coeffDualHom φ C) 0 x) z
      = tateDualZeroEquiv B C h₁B h₂B x (tateMap φ (-1) z) := by
  obtain ⟨f, rfl⟩ := H0mk_surjective (coeffDual B.ρ C) x
  obtain ⟨v, hv, rfl⟩ := exists_Hm1mk A.ρ z
  rfl

end Zero

/-! ### The two identifications that move the degree -/

section Shifts

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {A B : Rep k G} (φ : A ⟶ B)
  (C : Type u) [AddCommGroup C] [Module k C]

theorem tateCoeffDualShiftEquiv_apply (n : ℤ) (x : ↥(tateModule (coeffDualObj A C) n)) :
    tateCoeffDualShiftEquiv A C n x
      = tateMap (coeffDualShiftIso A C).hom (n + 1) (tateCoshiftEquiv (coeffDualObj A C) n x) :=
  rfl

theorem tateCoeffDualCoshiftEquiv_apply (h : IsExtendableInto k C (LinearMap.ker (augMap A.ρ)))
    (n : ℤ) (x : ↥(tateModule (coeffDualObj (coshiftObj A) C) n)) :
    tateCoeffDualCoshiftEquiv A C h n x
      = tateShiftEquiv (coeffDualObj A C) n (tateMap (coeffDualCoshiftIso A C h).inv n x) :=
  rfl

/-- **The identification of the coshift of the functionals with the functionals on the shift is
compatible with a map of representations.**  Both routes send a family of functionals of vanishing
sum and a function on the group to the sum of the values the members of the family take on the
images of the values of the function. -/
theorem coeffDualShiftIso_naturality :
    coshiftHom (coeffDualHom φ C) ≫ (coeffDualShiftIso A C).hom
      = (coeffDualShiftIso B C).hom ≫ coeffDualHom (shiftHom φ) C := by
  letI := Fintype.ofFinite G
  refine Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun ψ => LinearMap.ext fun q => ?_))
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb A.ρ)) q
  show indDualMap k G ↥A.V C (LinearMap.compLeft (coeffDualLinear φ C) G ψ.1) f
    = indDualMap k G ↥B.V C ψ.1 (LinearMap.compLeft φ.hom.hom G f)
  rw [indDualMap_apply, indDualMap_apply]
  exact Finset.sum_congr rfl fun x _ => rfl

/-- **The identification of the shift of the functionals with the functionals on the coshift is
compatible with a map of representations.**  Both routes send a family of functionals and a
function of vanishing sum to the sum of the values the members of the family take on the images of
the values of the function. -/
theorem coeffDualCoshiftIso_naturality
    (hA : IsExtendableInto k C (LinearMap.ker (augMap A.ρ)))
    (hB : IsExtendableInto k C (LinearMap.ker (augMap B.ρ))) :
    shiftHom (coeffDualHom φ C) ≫ (coeffDualCoshiftIso A C hA).hom
      = (coeffDualCoshiftIso B C hB).hom ≫ coeffDualHom (coshiftHom φ) C := by
  letI := Fintype.ofFinite G
  refine Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun q => LinearMap.ext fun z => ?_))
  obtain ⟨ψ, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb (coeffDual B.ρ C))) q
  show indDualMap k G ↥A.V C (LinearMap.compLeft (coeffDualLinear φ C) G ψ) z.1
    = indDualMap k G ↥B.V C ψ (LinearMap.compLeft φ.hom.hom G z.1)
  rw [indDualMap_apply, indDualMap_apply]
  exact Finset.sum_congr rfl fun x _ => rfl

theorem coeffDualCoshiftIso_inv_naturality
    (hA : IsExtendableInto k C (LinearMap.ker (augMap A.ρ)))
    (hB : IsExtendableInto k C (LinearMap.ker (augMap B.ρ))) :
    coeffDualHom (coshiftHom φ) C ≫ (coeffDualCoshiftIso A C hA).inv
      = (coeffDualCoshiftIso B C hB).inv ≫ shiftHom (coeffDualHom φ C) := by
  calc coeffDualHom (coshiftHom φ) C ≫ (coeffDualCoshiftIso A C hA).inv
      = (coeffDualCoshiftIso B C hB).inv ≫ ((coeffDualCoshiftIso B C hB).hom
          ≫ coeffDualHom (coshiftHom φ) C) ≫ (coeffDualCoshiftIso A C hA).inv := by
        rw [← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (coeffDualCoshiftIso B C hB).inv ≫ (shiftHom (coeffDualHom φ C)
          ≫ (coeffDualCoshiftIso A C hA).hom) ≫ (coeffDualCoshiftIso A C hA).inv := by
        rw [coeffDualCoshiftIso_naturality φ C hA hB]
    _ = (coeffDualCoshiftIso B C hB).inv ≫ shiftHom (coeffDualHom φ C) := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The passage from a degree of the functionals to the following degree of the functionals on
the shift is compatible with a map of representations.** -/
theorem tateCoeffDualShiftEquiv_naturality (n : ℤ) (x : ↥(tateModule (coeffDualObj B C) n)) :
    tateCoeffDualShiftEquiv A C n (tateMap (coeffDualHom φ C) n x)
      = tateMap (coeffDualHom (shiftHom φ) C) (n + 1) (tateCoeffDualShiftEquiv B C n x) := by
  rw [tateCoeffDualShiftEquiv_apply, tateCoeffDualShiftEquiv_apply,
    ← tateCoshiftEquiv_naturality (coeffDualHom φ C) n x, tateMap_comp_apply',
    tateMap_comp_apply', coeffDualShiftIso_naturality]

/-- **The passage from a degree of the functionals on the coshift to the following degree of the
functionals is compatible with a map of representations.** -/
theorem tateCoeffDualCoshiftEquiv_naturality
    (hA : IsExtendableInto k C (LinearMap.ker (augMap A.ρ)))
    (hB : IsExtendableInto k C (LinearMap.ker (augMap B.ρ))) (n : ℤ)
    (x : ↥(tateModule (coeffDualObj (coshiftObj B) C) n)) :
    tateCoeffDualCoshiftEquiv A C hA n (tateMap (coeffDualHom (coshiftHom φ) C) n x)
      = tateMap (coeffDualHom φ C) (n + 1) (tateCoeffDualCoshiftEquiv B C hB n x) := by
  rw [tateCoeffDualCoshiftEquiv_apply, tateCoeffDualCoshiftEquiv_apply, tateMap_comp_apply',
    coeffDualCoshiftIso_inv_naturality φ C hA hB, ← tateMap_comp_apply',
    ← tateShiftEquiv_naturality (coeffDualHom φ C) n]

end Shifts

/-! ### The comparison of degrees -/

section Congr

variable {G : Type} [Group G] [Finite G] {A B : Rep ℤ G} (φ : A ⟶ B)

theorem tateCoshiftEquivCongr_naturality {d m : ℤ} (h : d + 1 = m) (x : ↥(tateModule A d)) :
    tateMap (coshiftHom φ) m (tateCoshiftEquivCongr A h x)
      = tateCoshiftEquivCongr B h (tateMap φ d x) := by
  subst h
  exact tateCoshiftEquiv_naturality φ d x

theorem tateShiftEquivCongr_naturality {d m : ℤ} (h : d + 1 = m)
    (x : ↥(tateModule (shiftObj A) d)) :
    tateMap φ m (tateShiftEquivCongr A h x)
      = tateShiftEquivCongr B h (tateMap (shiftHom φ) d x) := by
  subst h
  exact tateShiftEquiv_naturality φ d x

theorem tateShiftEquivCongr_symm_naturality {d m : ℤ} (h : d + 1 = m)
    (z : ↥(tateModule A m)) :
    tateMap (shiftHom φ) d ((tateShiftEquivCongr A h).symm z)
      = (tateShiftEquivCongr B h).symm (tateMap φ m z) := by
  apply (tateShiftEquivCongr B h).injective
  rw [← tateShiftEquivCongr_naturality, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end Congr

/-! ### The recursion, carrying the compatibility along -/

section Recursion

variable {G : Type} [Group G] [Finite G]

/-- **The compatibility of a family of dualities, one for each representation, with the maps of
representations**: dualizing a class and evaluating the functional on the image of a class is the
same as moving the class along the dual map and dualizing there. -/
def IsTateDualNatural (C : Type) [AddCommGroup C] (n : ℤ)
    (e : ∀ A : Rep ℤ G, ↥(tateModule (coeffDualObj A C) n) ≃ₗ[ℤ]
      (↥(tateModule A (-n - 1)) →ₗ[ℤ] C)) : Prop :=
  ∀ {A B : Rep ℤ G} (φ : A ⟶ B) (x : ↥(tateModule (coeffDualObj B C) n))
    (z : ↥(tateModule A (-n - 1))),
    e A (tateMap (coeffDualHom φ C) n x) z = e B x (tateMap φ (-n - 1) z)

/-- Moving a compatible family of dualities to an equal degree keeps it compatible. -/
theorem IsTateDualNatural.degCongr {C : Type} [AddCommGroup C] {m n : ℤ} (h : m = n)
    {e : ∀ A : Rep ℤ G, ↥(tateModule (coeffDualObj A C) m) ≃ₗ[ℤ]
      (↥(tateModule A (-m - 1)) →ₗ[ℤ] C)} (he : IsTateDualNatural C m e) :
    IsTateDualNatural C n (fun A => dualDegCongr C A h (e A)) := by
  subst h
  intro A B φ x z
  exact he φ x z

/-- Raising the degree of a compatible family of dualities keeps it compatible. -/
theorem IsTateDualNatural.stepUp {C : Type} [AddCommGroup C] (hC : Module.Baer ℤ C) (n : ℤ)
    {e : ∀ A : Rep ℤ G, ↥(tateModule (coeffDualObj A C) n) ≃ₗ[ℤ]
      (↥(tateModule A (-n - 1)) →ₗ[ℤ] C)} (he : IsTateDualNatural C n e) :
    IsTateDualNatural C (n + 1) (fun A => dualStepUp C hC A n (e (coshiftObj A))) := by
  intro A B φ y z
  have h1 : (tateCoeffDualCoshiftEquiv A C (isExtendableInto_of_baer hC _) n).symm
      (tateMap (coeffDualHom φ C) (n + 1) y)
      = tateMap (coeffDualHom (coshiftHom φ) C) n
        ((tateCoeffDualCoshiftEquiv B C (isExtendableInto_of_baer hC _) n).symm y) := by
    apply (tateCoeffDualCoshiftEquiv A C (isExtendableInto_of_baer hC _) n).injective
    rw [LinearEquiv.apply_symm_apply, tateCoeffDualCoshiftEquiv_naturality φ C
      (isExtendableInto_of_baer hC _) (isExtendableInto_of_baer hC _),
      LinearEquiv.apply_symm_apply]
  show dualStepUp C hC A n (e (coshiftObj A)) (tateMap (coeffDualHom φ C) (n + 1) y) z
    = dualStepUp C hC B n (e (coshiftObj B)) y (tateMap φ (-(n + 1) - 1) z)
  rw [dualStepUp_apply, dualStepUp_apply, h1, he (coshiftHom φ),
    tateCoshiftEquivCongr_naturality]

/-- Lowering the degree of a compatible family of dualities keeps it compatible. -/
theorem IsTateDualNatural.stepDown {C : Type} [AddCommGroup C] (n : ℤ)
    {e : ∀ A : Rep ℤ G, ↥(tateModule (coeffDualObj A C) (n + 1)) ≃ₗ[ℤ]
      (↥(tateModule A (-(n + 1) - 1)) →ₗ[ℤ] C)} (he : IsTateDualNatural C (n + 1) e) :
    IsTateDualNatural C n (fun A => dualStepDown C A n (e (shiftObj A))) := by
  intro A B φ y z
  show dualStepDown C A n (e (shiftObj A)) (tateMap (coeffDualHom φ C) n y) z
    = dualStepDown C B n (e (shiftObj B)) y (tateMap φ (-n - 1) z)
  rw [dualStepDown_apply, dualStepDown_apply, tateCoeffDualShiftEquiv_naturality,
    he (shiftHom φ), tateShiftEquivCongr_symm_naturality]

/-- The duality in degree zero is compatible with the maps of representations. -/
theorem isTateDualNatural_dualBase {C : Type} [AddCommGroup C] (hC : Module.Baer ℤ C) :
    IsTateDualNatural (G := G) C 0 (dualBase C hC) := by
  intro A B φ x z
  exact tateDualZeroEquiv_naturality φ C (isExtendableInto_of_baer hC _)
    (isExtendableInto_of_baer hC _) (isExtendableInto_of_baer hC _)
    (isExtendableInto_of_baer hC _) x z

/-- The duality in a nonnegative degree is compatible with the maps of representations. -/
theorem isTateDualNatural_tateDualEquivNat (C : Type) [AddCommGroup C] (hC : Module.Baer ℤ C)
    (m : ℕ) : IsTateDualNatural (G := G) C (m : ℤ) (tateDualEquivNat C hC m) := by
  induction m with
  | zero =>
    exact IsTateDualNatural.degCongr (by norm_num) (isTateDualNatural_dualBase hC)
  | succ m ih =>
    exact IsTateDualNatural.degCongr (by push_cast; ring)
      (IsTateDualNatural.stepUp hC (m : ℤ) ih)

/-- The duality in a negative degree is compatible with the maps of representations. -/
theorem isTateDualNatural_tateDualEquivNeg (C : Type) [AddCommGroup C] (hC : Module.Baer ℤ C)
    (m : ℕ) : IsTateDualNatural (G := G) C (Int.negSucc m) (tateDualEquivNeg C hC m) := by
  induction m with
  | zero =>
    exact IsTateDualNatural.stepDown (Int.negSucc 0)
      (IsTateDualNatural.degCongr (by decide) (isTateDualNatural_tateDualEquivNat C hC 0))
  | succ m ih =>
    exact IsTateDualNatural.stepDown (Int.negSucc (m + 1))
      (IsTateDualNatural.degCongr
        (by rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring) ih)

/-- **The duality of complete cohomology against coefficients satisfying the criterion of Baer is
compatible with every map of representations, in every degree.**  Every degree is reached from
degree zero by the two shifts, and each of them respects a map of representations. -/
theorem tateDualEquivOfBaer_naturality (C : Type) [AddCommGroup C] (hC : Module.Baer ℤ C) :
    ∀ n : ℤ, IsTateDualNatural (G := G) C n (fun A => tateDualEquivOfBaer C hC A n)
  | .ofNat m => isTateDualNatural_tateDualEquivNat C hC m
  | .negSucc m => isTateDualNatural_tateDualEquivNeg C hC m

/-- **The duality of complete cohomology against coefficients satisfying the criterion of Baer is
compatible with every map of representations**, read on a class and a class of the complementary
degree. -/
theorem tateDualEquivOfBaer_naturality_apply (C : Type) [AddCommGroup C] (hC : Module.Baer ℤ C)
    (n : ℤ) {A B : Rep ℤ G} (φ : A ⟶ B) (x : ↥(tateModule (coeffDualObj B C) n))
    (z : ↥(tateModule A (-n - 1))) :
    tateDualEquivOfBaer C hC A n (tateMap (coeffDualHom φ C) n x) z
      = tateDualEquivOfBaer C hC B n x (tateMap φ (-n - 1) z) :=
  tateDualEquivOfBaer_naturality C hC n φ x z

/-- **The characters of the complete cohomology of a representation are compatible with every map
of representations, in every degree.** -/
theorem tateCharacterEquiv_naturality (n : ℤ) {A B : Rep ℤ G} (φ : A ⟶ B)
    (x : ↥(tateModule (coeffDualObj B (AddCircle (1 : ℚ))) n))
    (z : ↥(tateModule A (-n - 1))) :
    tateCharacterEquiv A n (tateMap (coeffDualHom φ (AddCircle (1 : ℚ))) n x) z
      = tateCharacterEquiv B n x (tateMap φ (-n - 1) z) :=
  tateDualEquivOfBaer_naturality_apply (AddCircle (1 : ℚ)) baer_addCircle n φ x z

end Recursion

end

end InverseGalois.CFT.Tate
