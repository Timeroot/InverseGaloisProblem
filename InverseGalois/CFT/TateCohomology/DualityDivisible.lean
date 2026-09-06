/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.DualityShift

/-!
# The duality of complete cohomology against divisible coefficients

The duality of complete cohomology asks of the coefficients only that they receive every functional
defined on a submodule.  For coefficients killed by a prime that is free, because the submodule is
a direct summand; for divisible coefficients it is the criterion of Baer, and it costs no
hypothesis at all on the representation.

So a group of coefficients in which every element is divisible by every integer is dualizing for
every representation of a finite group: **the complete cohomology of the functionals into it, in
any degree, is the group of functionals on the complete cohomology of the representation in the
complementary degree.**  The circle of the rationals is such a group, and the functionals into it
are the characters, so the complete cohomology of a finite group is dual to that of the
contragredient in the complementary degree, with no hypothesis whatsoever.

The isomorphism is built by recursion rather than asserted to exist: the two shifts move the degree
of the functionals up and down, the degree zero is the pairing of the two middle degrees, and every
other degree is reached from it by a chain of shifts.  What comes out is a definite map in each
degree, which is what a comparison with restriction or with a change of the representation will
later need.

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

/-! ### The three steps of the recursion -/

section Steps

variable {G : Type} [Group G] [Finite G]

/-- Moving the duality to an equal degree. -/
def dualDegCongr (C : Type) [AddCommGroup C] (A : Rep ℤ G) {m n : ℤ} (h : m = n)
    (e : ↥(tateModule (coeffDualObj A C) m) ≃ₗ[ℤ] (↥(tateModule A (-m - 1)) →ₗ[ℤ] C)) :
    ↥(tateModule (coeffDualObj A C) n) ≃ₗ[ℤ] (↥(tateModule A (-n - 1)) →ₗ[ℤ] C) := by
  subst h; exact e

theorem dualDegCongr_rfl (C : Type) [AddCommGroup C] (A : Rep ℤ G) {m : ℤ}
    (e : ↥(tateModule (coeffDualObj A C) m) ≃ₗ[ℤ] (↥(tateModule A (-m - 1)) →ₗ[ℤ] C)) :
    dualDegCongr C A (rfl : m = m) e = e := rfl

/-- The comparison of a degree with the next one over the coshift, read at a degree presented in
another way. -/
def tateCoshiftEquivCongr (A : Rep ℤ G) {d n : ℤ} (h : d + 1 = n) :
    ↥(tateModule A d) ≃ₗ[ℤ] ↥(tateModule (coshiftObj A) n) := by
  subst h; exact tateCoshiftEquiv A d

theorem tateCoshiftEquivCongr_rfl (A : Rep ℤ G) (d : ℤ) :
    tateCoshiftEquivCongr A (rfl : d + 1 = d + 1) = tateCoshiftEquiv A d := rfl

/-- The comparison of a degree over the shift with the next one, read at a degree presented in
another way. -/
def tateShiftEquivCongr (A : Rep ℤ G) {d n : ℤ} (h : d + 1 = n) :
    ↥(tateModule (shiftObj A) d) ≃ₗ[ℤ] ↥(tateModule A n) := by
  subst h; exact tateShiftEquiv A d

theorem tateShiftEquivCongr_rfl (A : Rep ℤ G) (d : ℤ) :
    tateShiftEquivCongr A (rfl : d + 1 = d + 1) = tateShiftEquiv A d := rfl

/-- The duality in degree zero, from the pairing of the two middle degrees. -/
def dualBase (C : Type) [AddCommGroup C] (hC : Module.Baer ℤ C) (A : Rep ℤ G) :
    ↥(tateModule (coeffDualObj A C) 0) ≃ₗ[ℤ] (↥(tateModule A (-(0 : ℤ) - 1)) →ₗ[ℤ] C) := by
  rw [show (-(0 : ℤ) - 1) = -1 from by norm_num]
  exact tateDualZeroEquiv A C (isExtendableInto_of_baer hC _) (isExtendableInto_of_baer hC _)

/-- The step that raises the degree of the functionals by one, at the cost of replacing the
representation by its coshift. -/
def dualStepUp (C : Type) [AddCommGroup C] (hC : Module.Baer ℤ C) (A : Rep ℤ G) (n : ℤ)
    (e : ↥(tateModule (coeffDualObj (coshiftObj A) C) n)
      ≃ₗ[ℤ] (↥(tateModule (coshiftObj A) (-n - 1)) →ₗ[ℤ] C)) :
    ↥(tateModule (coeffDualObj A C) (n + 1))
      ≃ₗ[ℤ] (↥(tateModule A (-(n + 1) - 1)) →ₗ[ℤ] C) :=
  ((tateCoeffDualCoshiftEquiv A C (isExtendableInto_of_baer hC _) n).symm.trans e).trans
    (LinearEquiv.arrowCongr
      (tateCoshiftEquivCongr A (show -(n + 1) - 1 + 1 = -n - 1 from by ring)).symm
      (LinearEquiv.refl ℤ C))

theorem dualStepUp_apply (C : Type) [AddCommGroup C] (hC : Module.Baer ℤ C) (A : Rep ℤ G) (n : ℤ)
    (e : ↥(tateModule (coeffDualObj (coshiftObj A) C) n)
      ≃ₗ[ℤ] (↥(tateModule (coshiftObj A) (-n - 1)) →ₗ[ℤ] C))
    (y : ↥(tateModule (coeffDualObj A C) (n + 1))) (z : ↥(tateModule A (-(n + 1) - 1))) :
    dualStepUp C hC A n e y z
      = e ((tateCoeffDualCoshiftEquiv A C (isExtendableInto_of_baer hC _) n).symm y)
        (tateCoshiftEquivCongr A (show -(n + 1) - 1 + 1 = -n - 1 from by ring) z) := rfl

/-- The step that lowers the degree of the functionals by one, at the cost of replacing the
representation by its shift. -/
def dualStepDown (C : Type) [AddCommGroup C] (A : Rep ℤ G) (n : ℤ)
    (e : ↥(tateModule (coeffDualObj (shiftObj A) C) (n + 1))
      ≃ₗ[ℤ] (↥(tateModule (shiftObj A) (-(n + 1) - 1)) →ₗ[ℤ] C)) :
    ↥(tateModule (coeffDualObj A C) n) ≃ₗ[ℤ] (↥(tateModule A (-n - 1)) →ₗ[ℤ] C) :=
  ((tateCoeffDualShiftEquiv A C n).trans e).trans
    (LinearEquiv.arrowCongr (tateShiftEquivCongr A (show -(n + 1) - 1 + 1 = -n - 1 from by ring))
      (LinearEquiv.refl ℤ C))

theorem dualStepDown_apply (C : Type) [AddCommGroup C] (A : Rep ℤ G) (n : ℤ)
    (e : ↥(tateModule (coeffDualObj (shiftObj A) C) (n + 1))
      ≃ₗ[ℤ] (↥(tateModule (shiftObj A) (-(n + 1) - 1)) →ₗ[ℤ] C))
    (y : ↥(tateModule (coeffDualObj A C) n)) (z : ↥(tateModule A (-n - 1))) :
    dualStepDown C A n e y z
      = e (tateCoeffDualShiftEquiv A C n y)
        ((tateShiftEquivCongr A (show -(n + 1) - 1 + 1 = -n - 1 from by ring)).symm z) := rfl

end Steps

/-! ### Every degree, for every representation -/

section Divisible

variable {G : Type} [Group G] [Finite G]

/-- The duality in a nonnegative degree, reached from degree zero by raising it one step at a
time. -/
def tateDualEquivNat (C : Type) [AddCommGroup C] (hC : Module.Baer ℤ C) :
    (m : ℕ) → (A : Rep ℤ G) → (↥(tateModule (coeffDualObj A C) (m : ℤ))
      ≃ₗ[ℤ] (↥(tateModule A (-(m : ℤ) - 1)) →ₗ[ℤ] C))
  | 0, A => dualDegCongr C A (m := (0 : ℤ)) (by norm_num) (dualBase C hC A)
  | (m + 1), A =>
      dualDegCongr C A (m := (m : ℤ) + 1) (by push_cast; ring)
        (dualStepUp C hC A (m : ℤ) (tateDualEquivNat C hC m (coshiftObj A)))

/-- The duality in a negative degree, reached from degree zero by lowering it one step at a
time. -/
def tateDualEquivNeg (C : Type) [AddCommGroup C] (hC : Module.Baer ℤ C) :
    (m : ℕ) → (A : Rep ℤ G) → (↥(tateModule (coeffDualObj A C) (Int.negSucc m))
      ≃ₗ[ℤ] (↥(tateModule A (-(Int.negSucc m) - 1)) →ₗ[ℤ] C))
  | 0, A =>
      dualStepDown C A (Int.negSucc 0)
        (dualDegCongr C (shiftObj A) (m := ((0 : ℕ) : ℤ)) (by decide)
          (tateDualEquivNat C hC 0 (shiftObj A)))
  | (m + 1), A =>
      dualStepDown C A (Int.negSucc (m + 1))
        (dualDegCongr C (shiftObj A) (m := Int.negSucc m)
          (by rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring)
          (tateDualEquivNeg C hC m (shiftObj A)))

/-- **The complete cohomology of the functionals with coefficients satisfying the criterion of
Baer, in any degree, is the group of functionals on the complete cohomology of the representation
in the complementary degree.**  Both moves of the degree are available, since the extension a
functional needs is available for every submodule of every module. -/
def tateDualEquivOfBaer (C : Type) [AddCommGroup C] (hC : Module.Baer ℤ C) (A : Rep ℤ G) :
    (n : ℤ) → (↥(tateModule (coeffDualObj A C) n) ≃ₗ[ℤ] (↥(tateModule A (-n - 1)) →ₗ[ℤ] C))
  | .ofNat m => tateDualEquivNat C hC m A
  | .negSucc m => tateDualEquivNeg C hC m A

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
def tateCharacterEquiv (A : Rep ℤ G) (n : ℤ) :
    ↥(tateModule (coeffDualObj A (AddCircle (1 : ℚ))) n)
      ≃ₗ[ℤ] (↥(tateModule A (-n - 1)) →ₗ[ℤ] AddCircle (1 : ℚ)) :=
  tateDualEquivOfBaer (AddCircle (1 : ℚ)) baer_addCircle A n

end Character

end

end InverseGalois.CFT.Tate
