/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.DualityShift

/-!
# The duality of complete cohomology against divisible coefficients

The duality of complete cohomology asks of the coefficients only that they receive every functional
defined on a submodule.  For coefficients killed by a prime that is free because the submodule is a
direct summand; for divisible coefficients it is the criterion of Baer, and it costs no hypothesis
at all on the representation.

So a group of coefficients in which every element is divisible by every integer is dualizing for
every representation of a finite group: **the complete cohomology of the functionals into it, in
any degree, is the group of functionals on the complete cohomology of the representation in the
complementary degree.**  The circle of the rationals is such a group, and the functionals into it
are the characters, so the complete cohomology of a finite group is dual to that of the
contragredient in the complementary degree, with no hypothesis whatsoever.

## Main results

* `InverseGalois.CFT.Tate.isExtendableInto_of_baer`: coefficients satisfying the criterion of Baer
  receive every functional defined on a submodule.
* `InverseGalois.CFT.Tate.tateDualEquivOfBaer`: **the complete cohomology of the functionals with
  such coefficients, in any degree, is the group of functionals on the complete cohomology of the
  representation in the complementary degree.**
* `InverseGalois.CFT.Tate.tateCharacterEquiv`: **the characters of the complete cohomology of a
  representation in a degree are the complete cohomology of the characters of the representation in
  the complementary degree.**

## Tags

Tate cohomology, duality, divisible group, Baer criterion, character module
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

noncomputable section

/-! ### Extending a functional into divisible coefficients -/

section Extend

/-- **Coefficients satisfying the criterion of Baer receive every functional defined on a
submodule.**  The criterion is exactly the extension property along an injection, and the inclusion
of a submodule is one. -/
theorem isExtendableInto_of_baer {C : Type*} [AddCommGroup C] [instC : Module ℤ C]
    (hC : Module.Baer ℤ C) {X : Type*} [AddCommGroup X] {instX : Module ℤ X}
    (N : @Submodule ℤ X _ _ instX) : @IsExtendableInto ℤ _ C _ instC X _ instX N := by
  obtain rfl : instX = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  obtain rfl : instC = AddCommGroup.toIntModule C := Subsingleton.elim _ _
  intro φ
  obtain ⟨F, hF⟩ := hC.extension_property_addMonoidHom N.subtype.toAddMonoidHom
    (fun _ _ hab => Subtype.ext hab) φ.toAddMonoidHom
  exact ⟨F.toIntLinearMap, fun x => DFunLike.congr_fun hF x⟩

end Extend

/-! ### Every degree, for every representation -/

section Divisible

variable {G : Type} [Group G] [Finite G]

/-- **The complete cohomology of the functionals with coefficients satisfying the criterion of
Baer, in any degree, is the group of functionals on the complete cohomology of the representation
in the complementary degree.**  Both moves of the degree are available, since the extension a
functional needs is available for every submodule of every module. -/
theorem nonempty_tateDualEquivOfBaer (C : Type) [AddCommGroup C] (hC : Module.Baer ℤ C) (n : ℤ) :
    ∀ A : Rep ℤ G, Nonempty (↥(tateModule (coeffDualObj A C) n) ≃ₗ[ℤ]
      (↥(tateModule A (-n - 1)) →ₗ[ℤ] C)) := by
  induction n using Int.induction_on with
  | zero =>
    intro A
    rw [show (-(0 : ℤ) - 1) = -1 from by norm_num]
    exact ⟨tateDualZeroEquiv A C (isExtendableInto_of_baer hC _) (isExtendableInto_of_baer hC _)⟩
  | succ i ih =>
    intro A
    obtain ⟨e⟩ := ih (coshiftObj A)
    have hs := tateCoshiftEquiv A (-(i : ℤ) - 2)
    rw [show (-(i : ℤ) - 2 + 1) = -(i : ℤ) - 1 from by ring] at hs
    rw [show (-((i : ℤ) + 1) - 1) = -(i : ℤ) - 2 from by ring]
    refine ⟨(tateCoeffDualCoshiftEquiv A C ?_ (i : ℤ)).symm.trans
      (e.trans (LinearEquiv.arrowCongr hs.symm (LinearEquiv.refl ℤ C)))⟩
    exact isExtendableInto_of_baer hC _
  | pred i ih =>
    intro A
    obtain ⟨e⟩ := ih (shiftObj A)
    rw [show (-(-(i : ℤ)) - 1) = (i : ℤ) - 1 from by ring] at e
    have hs := tateShiftEquiv A ((i : ℤ) - 1)
    rw [show ((i : ℤ) - 1 + 1) = (i : ℤ) from by ring] at hs
    have hstep := tateCoeffDualShiftEquiv A C (-(i : ℤ) - 1)
    rw [show (-(i : ℤ) - 1 + 1) = -(i : ℤ) from by ring] at hstep
    rw [show (-(-(i : ℤ) - 1) - 1) = (i : ℤ) from by ring]
    exact ⟨hstep.trans (e.trans (LinearEquiv.arrowCongr hs (LinearEquiv.refl ℤ C)))⟩

/-- **The complete cohomology of the functionals with coefficients satisfying the criterion of
Baer, in any degree, is the group of functionals on the complete cohomology of the representation
in the complementary degree.** -/
def tateDualEquivOfBaer (C : Type) [AddCommGroup C] (hC : Module.Baer ℤ C) (n : ℤ) (A : Rep ℤ G) :
    ↥(tateModule (coeffDualObj A C) n) ≃ₗ[ℤ] (↥(tateModule A (-n - 1)) →ₗ[ℤ] C) :=
  (nonempty_tateDualEquivOfBaer C hC n A).some

end Divisible

/-! ### The characters -/

section Character

variable {G : Type} [Group G] [Finite G]

/-- **The circle of the rationals satisfies the criterion of Baer**, since every element of it is
divisible by every integer. -/
theorem baer_addCircle : Module.Baer ℤ (AddCircle (1 : ℚ)) :=
  Module.Baer.of_divisible (AddCircle (1 : ℚ))

/-- **The characters of the complete cohomology of a representation of a finite group in a degree
are the complete cohomology of the characters of the representation in the complementary degree.**
This is the duality of complete cohomology in the form that needs no hypothesis at all, neither on
the representation nor on the degree. -/
def tateCharacterEquiv (n : ℤ) (A : Rep ℤ G) :
    ↥(tateModule (coeffDualObj A (AddCircle (1 : ℚ))) n)
      ≃ₗ[ℤ] (↥(tateModule A (-n - 1)) →ₗ[ℤ] AddCircle (1 : ℚ)) :=
  tateDualEquivOfBaer (AddCircle (1 : ℚ)) baer_addCircle n A

end Character

end

end InverseGalois.CFT.Tate
