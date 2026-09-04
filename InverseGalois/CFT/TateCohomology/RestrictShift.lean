/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Restrict

/-!
# Restriction and corestriction against the two identifications of degree

Restriction to a subgroup and corestriction from it are defined by recursion on the degree: in a
positive degree through the identification of the complete cohomology of the shift with that of the
representation one degree higher, and in a degree below minus one through the identification of the
complete cohomology of a representation with that of its coshift one degree higher.  Each recursion
is exactly the statement that the square formed by the two maps and the identification it uses
commutes, so in the range where a recursion is the definition nothing has to be proved.

What is recorded here is that statement, in the shape in which it is used: **restriction commutes
with the identification of the shift in every nonnegative degree, and with the identification of the
coshift in every degree below minus one**, and the same for corestriction.  The two remaining
degrees are the two in which the recursion has a base case instead of a step, and they are the only
place where the comparison of the two carries content.

## Main results

* `InverseGalois.CFT.Tate.tateRes_tateShiftEquiv`: **restriction commutes with the identification of
  the shift**, in a nonnegative degree.
* `InverseGalois.CFT.Tate.tateCor_tateShiftEquiv`: **corestriction commutes with the identification
  of the shift**, in a nonnegative degree.
* `InverseGalois.CFT.Tate.tateRes_tateCoshiftEquiv`: **restriction commutes with the identification
  of the coshift**, in a degree below minus one.
* `InverseGalois.CFT.Tate.tateCor_tateCoshiftEquiv`: **corestriction commutes with the
  identification of the coshift**, in a degree below minus one.

## Tags

Tate cohomology, restriction, corestriction, dimension shifting
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-! ### The shift, in a nonnegative degree -/

/-- **Restriction to a subgroup commutes with the identification of the complete cohomology of the
shift**, in a nonnegative degree. -/
theorem tateRes_tateShiftEquiv (H : Subgroup G) (A : Rep k G) (m : ℕ)
    (x : ↥(tateModule (shiftObj A) (Int.ofNat m))) :
    tateRes H A (Int.ofNat m + 1) (tateShiftEquiv A (Int.ofNat m) x)
      = resShiftEquiv H A (Int.ofNat m) (tateRes H (shiftObj A) (Int.ofNat m) x) := by
  show (resShiftEquiv H A (Int.ofNat m))
      (tateResNat H m (shiftObj A) ((tateShiftEquiv A (Int.ofNat m)).symm
        ((tateShiftEquiv A (Int.ofNat m)) x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- **Corestriction from a subgroup commutes with the identification of the complete cohomology of
the shift**, in a nonnegative degree. -/
theorem tateCor_tateShiftEquiv (H : Subgroup G) (A : Rep k G) (m : ℕ)
    (y : ↥(tateModule (resObj H (shiftObj A)) (Int.ofNat m))) :
    tateCor H A (Int.ofNat m + 1) (resShiftEquiv H A (Int.ofNat m) y)
      = tateShiftEquiv A (Int.ofNat m) (tateCor H (shiftObj A) (Int.ofNat m) y) := by
  show (tateShiftEquiv A (Int.ofNat m))
      (tateCorNat H m (shiftObj A) ((resShiftEquiv H A (Int.ofNat m)).symm
        ((resShiftEquiv H A (Int.ofNat m)) y))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-! ### The coshift, in a degree below minus one -/

/-- **Restriction to a subgroup commutes with the identification of the complete cohomology of the
coshift**, in a degree below minus one. -/
theorem tateRes_tateCoshiftEquiv (H : Subgroup G) (A : Rep k G) (m : ℕ)
    (x : ↥(tateModule A (Int.negSucc (m + 1)))) :
    tateRes H (coshiftObj A) (Int.negSucc (m + 1) + 1)
        (tateCoshiftEquiv A (Int.negSucc (m + 1)) x)
      = resCoshiftEquiv H A (Int.negSucc (m + 1)) (tateRes H A (Int.negSucc (m + 1)) x) := by
  show _ = resCoshiftEquiv H A (Int.negSucc (m + 1))
      ((resCoshiftEquiv H A (Int.negSucc (m + 1))).symm
        (tateResNegSucc H m (coshiftObj A) (tateCoshiftEquiv A (Int.negSucc (m + 1)) x)))
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- **Corestriction from a subgroup commutes with the identification of the complete cohomology of
the coshift**, in a degree below minus one. -/
theorem tateCor_tateCoshiftEquiv (H : Subgroup G) (A : Rep k G) (m : ℕ)
    (y : ↥(tateModule (resObj H A) (Int.negSucc (m + 1)))) :
    tateCor H (coshiftObj A) (Int.negSucc (m + 1) + 1)
        (resCoshiftEquiv H A (Int.negSucc (m + 1)) y)
      = tateCoshiftEquiv A (Int.negSucc (m + 1)) (tateCor H A (Int.negSucc (m + 1)) y) := by
  show _ = tateCoshiftEquiv A (Int.negSucc (m + 1))
      ((tateCoshiftEquiv A (Int.negSucc (m + 1))).symm
        (tateCorNegSucc H m (coshiftObj A) (resCoshiftEquiv H A (Int.negSucc (m + 1)) y)))
  rw [LinearEquiv.apply_symm_apply]
  rfl

end

end InverseGalois.CFT.Tate
