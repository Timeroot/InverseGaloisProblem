/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.RestrictOne

/-!
# Tate's theorem in its classical degree

Tate's theorem is usually stated about a class in degree two: if on every subgroup the complete
cohomology of a representation vanishes in degree one and in degree two consists exactly of the
multiples of the restricted class, only the multiples of the order of the subgroup annihilating it,
then the complete cohomology of the integers in a degree is that of the representation two degrees
higher.

The degree drops by one on passing to the shift.  A class in degree two of a representation is the
class of a cocycle of the shift, because the identification raising the degree is surjective and
every class in degree one is the class of a cocycle; and restriction commutes with the
identification raising the degree, by the very way restriction was defined.  The hypotheses in
degrees one and two on the representation are therefore the hypotheses in degrees zero and one on
the shift, and the theorem in the degree already established applies to the shift.

## Main definitions

* `InverseGalois.CFT.Tate.IsTateClassTwo`: the classical hypotheses of Tate's theorem on a
  subgroup, in degree two.
* `InverseGalois.CFT.Tate.tateTwoCocycle`: a cocycle of the shift whose class in degree one
  corresponds to a prescribed class in degree two.

## Main results

* `InverseGalois.CFT.Tate.tateRes_succ_shift`: **restriction commutes with the identification
  raising the degree.**
* `InverseGalois.CFT.Tate.isTateClass_shiftObj`: **the classical hypotheses in degree two are the
  hypotheses in degree one on the shift.**
* `InverseGalois.CFT.Tate.tateTheoremTwoEquiv`: **Tate's theorem**: the complete cohomology of the
  integers in a degree is that of the representation two degrees higher.

## Tags

Tate cohomology, Tate's theorem, fundamental class, dimension shifting
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### Every class in degree one is the class of a cocycle -/

section Surjective

variable {k G : Type u} [CommRing k] [Group G]

/-- **Every class in degree one is the class of a cocycle.** -/
theorem exists_H1π (A : Rep k G) (x : groupCohomology A 1) :
    ∃ b : groupCohomology.cocycles₁ A, groupCohomology.H1π A b = x :=
  groupCohomology.H1_induction_on x fun b => ⟨b, rfl⟩

end Surjective

/-! ### Restriction and the identification raising the degree -/

section Shift

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **Restriction commutes with the identification raising the degree.** -/
theorem tateRes_succ_shift (H : Subgroup G) (A : Rep k G) (m : ℕ)
    (x : tateModule (shiftObj A) (Int.ofNat m)) :
    tateRes H A (Int.ofNat m + 1) (tateShiftEquiv A (Int.ofNat m) x)
      = resShiftEquiv H A (Int.ofNat m) (tateRes H (shiftObj A) (Int.ofNat m) x) := by
  show resShiftEquiv H A (Int.ofNat m) (tateResNat H m (shiftObj A)
      ((tateShiftEquiv A (Int.ofNat m)).symm (tateShiftEquiv A (Int.ofNat m) x)))
    = resShiftEquiv H A (Int.ofNat m) (tateResNat H m (shiftObj A) x)
  rw [LinearEquiv.symm_apply_apply]

/-- **Restriction in degree two commutes with the identification raising the degree** from degree
one of the shift. -/
theorem tateRes_two_shift (H : Subgroup G) (A : Rep k G) (x : tateModule (shiftObj A) 1) :
    tateRes H A 2 (tateShiftEquiv A 1 x) = resShiftEquiv H A 1 (tateRes H (shiftObj A) 1 x) :=
  tateRes_succ_shift H A 1 x

end Shift

/-! ### The classical hypotheses -/

section DegreeTwo

variable {G : Type} [Group G] [Finite G]

/-- **The classical hypotheses of Tate's theorem on a subgroup**: the complete cohomology of the
representation vanishes in degree one, in degree two it consists of the multiples of the restricted
class, and only the multiples of the order of the subgroup annihilate that class. -/
structure IsTateClassTwo (H : Subgroup G) (A : Rep ℤ G) (α : tateModule A 2) : Prop where
  /-- The complete cohomology of the representation vanishes in degree one. -/
  isZero_one : Limits.IsZero (tateModule (resObj H A) 1)
  /-- Every class in degree two is a multiple of the restricted class. -/
  exists_zsmul : ∀ y : tateModule (resObj H A) 2, ∃ m : ℤ, y = m • tateRes H A 2 α
  /-- Only the multiples of the order of the subgroup annihilate the restricted class. -/
  dvd_of_zsmul_eq_zero : ∀ m : ℤ, m • tateRes H A 2 α = 0 → (Nat.card ↥H : ℤ) ∣ m

variable {H : Subgroup G} {A : Rep ℤ G} {b : groupCohomology.cocycles₁ (shiftObj A)}

/-- **The class of a cocycle of the shift, read on a subgroup, is the restriction of the
corresponding class in degree two.** -/
theorem resShiftEquiv_H1π_resCocycles₁ :
    resShiftEquiv H A 1
        (groupCohomology.H1π (resObj H (shiftObj A)) (resCocycles₁ H (shiftObj A) b))
      = tateRes H A 2 (tateShiftEquiv A 1 (groupCohomology.H1π (shiftObj A) b)) := by
  rw [tateRes_two_shift, tateRes_one_H1π]

/-- **The classical hypotheses in degree two are the hypotheses in degree one on the shift.** -/
theorem isTateClass_shiftObj
    (h : IsTateClassTwo H A (tateShiftEquiv A 1 (groupCohomology.H1π (shiftObj A) b))) :
    IsTateClass H (shiftObj A) b where
  isZero_zero := by
    refine isZero_of_forall_eq_zero fun x => ?_
    exact (resShiftEquiv H A 0).map_eq_zero_iff.1 (eq_zero_of_isZero h.isZero_one _)
  exists_zsmul y := by
    obtain ⟨m, hm⟩ := h.exists_zsmul (resShiftEquiv H A 1 y)
    refine ⟨m, (resShiftEquiv H A 1).injective ?_⟩
    rw [hm, map_zsmul, resShiftEquiv_H1π_resCocycles₁]
  dvd_of_zsmul_eq_zero m hm := by
    have hz : resShiftEquiv H A 1 (m • groupCohomology.H1π (resObj H (shiftObj A))
        (resCocycles₁ H (shiftObj A) b)) = 0 := by rw [hm, map_zero]
    rw [map_zsmul, resShiftEquiv_H1π_resCocycles₁] at hz
    exact h.dvd_of_zsmul_eq_zero m hz

end DegreeTwo

/-! ### Tate's theorem -/

section Theorem

variable {G : Type} [Group G] [Finite G]

/-- **A cocycle of the shift whose class in degree one corresponds to a prescribed class in degree
two.** -/
def tateTwoCocycle (A : Rep ℤ G) (α : tateModule A 2) :
    groupCohomology.cocycles₁ (shiftObj A) :=
  (exists_H1π (shiftObj A) ((tateShiftEquiv A 1).symm α)).choose

theorem tateTwoCocycle_spec (A : Rep ℤ G) (α : tateModule A 2) :
    tateShiftEquiv A 1 (groupCohomology.H1π (shiftObj A) (tateTwoCocycle A α)) = α := by
  rw [tateTwoCocycle, (exists_H1π (shiftObj A) ((tateShiftEquiv A 1).symm α)).choose_spec,
    LinearEquiv.apply_symm_apply]

/-- **Tate's theorem**: the complete cohomology of the integers in a degree is the complete
cohomology of the representation two degrees higher. -/
def tateTheoremTwoEquiv (A : Rep ℤ G) (α : tateModule A 2)
    (h : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsTateClassTwo (P : Subgroup G) A α) (n : ℤ) :
    tateModule (Rep.trivial ℤ G ℤ) n ≃ₗ[ℤ] tateModule A (n + 1 + 1) :=
  (tateTheoremEquiv (A := shiftObj A) (b := tateTwoCocycle A α)
    (fun p hp P => isTateClass_shiftObj (by
      rw [tateTwoCocycle_spec]
      exact h p hp P)) n).trans (tateShiftEquiv A (n + 1))

end Theorem

end

end InverseGalois.CFT.Tate
