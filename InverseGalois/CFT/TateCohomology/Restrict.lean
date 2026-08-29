/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Functorial
import InverseGalois.CFT.TateCohomology.Shifting
import InverseGalois.CFT.TateCohomology.Transfer

/-!
# Restriction and corestriction in every degree

A representation of a group is in particular a representation of any subgroup, and in the two
middle degrees the complete cohomology of the group maps to that of the subgroup and back again,
the composite being multiplication by the index.  Those two maps are transported to every other
degree by dimension shifting.

The device is available because the functions on the group, viewed as a representation of a
subgroup, are again the functions on the subgroup, now with values in the functions on the cosets:
a choice of coset representatives splits the group as the cosets times the subgroup.  The middle
term of each of the two shifting sequences therefore still has no complete cohomology after
restriction, so its connecting map is still bijective and can be used to move a degree.  Since the
two identifications used on either side are the connecting maps of one and the same sequence, the
composite of corestriction after restriction stays multiplication by the index all the way up and
all the way down.

## Main definitions

* `InverseGalois.CFT.Tate.resObj`: a representation of a group read as a representation of a
  subgroup.
* `InverseGalois.CFT.Tate.tateRes`, `InverseGalois.CFT.Tate.tateCor`: restriction to a subgroup
  and corestriction from it, in an arbitrary integer degree.

## Main results

* `InverseGalois.CFT.Tate.indRestrictIso`: **the functions on the group, read on a subgroup, are
  the functions on the subgroup with values in the functions on the cosets.**
* `InverseGalois.CFT.Tate.isZero_tateModule_resObj_indObj`: **the functions on the group still have
  no complete cohomology after restriction to a subgroup.**
* `InverseGalois.CFT.Tate.tateCor_tateRes`: **corestriction after restriction is multiplication by
  the index**, in every integer degree.

## Tags

Tate cohomology, restriction, corestriction, dimension shifting, index of a subgroup
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-! ### Restricting a representation to a subgroup -/

/-- **A representation of a group read as a representation of a subgroup.** -/
def resObj (H : Subgroup G) (A : Rep k G) : Rep k ↥H := (Action.res _ H.subtype).obj A

omit [Finite G] in
@[simp]
theorem resObj_ρ (H : Subgroup G) (A : Rep k G) : (resObj H A).ρ = restrictRep H A.ρ := rfl

/-- **A short exact sequence of representations of a group read on a subgroup.** -/
def resSeq (H : Subgroup G) (X : ShortComplex (Rep k G)) : ShortComplex (Rep k ↥H) :=
  X.map (Action.res _ H.subtype)

omit [Finite G] in
theorem resSeq_shortExact {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (H : Subgroup G) :
    (resSeq H X).ShortExact := by
  refine shortExact_of_linearMap ?_ ?_ ?_
  · exact shortExact_injective (X := X) hX
  · exact shortExact_surjective (X := X) hX
  · intro x hx
    have hmem : x ∈ LinearMap.range X.f.hom.hom := by
      rw [shortExact_range_eq_ker hX]
      exact hx
    exact LinearMap.mem_range.1 hmem

/-! ### The functions on the group, read on a subgroup -/

/-- **Splitting the group as the cosets times a subgroup** identifies the functions on the group
with the functions on the subgroup taking values in the functions on the cosets. -/
def indRestrictEquiv (H : Subgroup G) (M : Type u) [AddCommGroup M] [Module k M] :
    (G → M) ≃ₗ[k] (↥H → (G ⧸ H) → M) where
  toFun f h c := f (cosetLeftEquiv H (c, h))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun φ x := φ ((cosetLeftEquiv H).symm x).2 ((cosetLeftEquiv H).symm x).1
  left_inv f := by
    funext x
    show f (cosetLeftEquiv H (((cosetLeftEquiv H).symm x).1, ((cosetLeftEquiv H).symm x).2)) = f x
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv φ := by
    funext h c
    show φ ((cosetLeftEquiv H).symm (cosetLeftEquiv H (c, h))).2
      ((cosetLeftEquiv H).symm (cosetLeftEquiv H (c, h))).1 = φ h c
    rw [Equiv.symm_apply_apply]

omit [Finite G] in
theorem indRestrictEquiv_equivariant (H : Subgroup G) (M : Type u) [AddCommGroup M] [Module k M]
    (h₀ : ↥H) :
    (indRestrictEquiv H M).toLinearMap ∘ₗ restrictRep H (inducedRep k G M) h₀
      = inducedRep k ↥H ((G ⧸ H) → M) h₀ ∘ₗ (indRestrictEquiv H M).toLinearMap :=
  LinearMap.ext fun f => funext fun _ => funext fun _ => congrArg f (mul_assoc _ _ _)

/-- **The functions on the group, read on a subgroup, are the functions on the subgroup with values
in the functions on the cosets.** -/
def indRestrictIso (H : Subgroup G) (A : Rep k G) :
    resObj H (indObj A) ≅ Rep.of (inducedRep k ↥H ((G ⧸ H) → ↥A.V)) :=
  Action.mkIso (indRestrictEquiv (k := k) H ↥A.V).toModuleIso fun h₀ => by
    refine ModuleCat.hom_ext (LinearMap.ext fun f => ?_)
    exact LinearMap.congr_fun (indRestrictEquiv_equivariant (k := k) H ↥A.V h₀) f

/-- **The functions on the group still have no complete cohomology after restriction to a
subgroup.** -/
theorem isZero_tateModule_resObj_indObj (H : Subgroup G) (A : Rep k G) (n : ℤ) :
    Limits.IsZero (tateModule (resObj H (indObj A)) n) :=
  isZero_tateModule_of_iso (indRestrictIso H A) n (isZero_tateModule_inducedRep n)

/-! ### The two identifications after restriction -/

/-- **The complete cohomology of the shift, read on a subgroup, in a degree is the complete
cohomology of the representation, read on the subgroup, in the following degree.** -/
def resShiftEquiv (H : Subgroup G) (A : Rep k G) (n : ℤ) :
    tateModule (resObj H (shiftObj A)) n ≃ₗ[k] tateModule (resObj H A) (n + 1) :=
  LinearEquiv.ofBijective (tateδ (resSeq_shortExact (shiftSeq_shortExact A) H) n).hom
    (bijective_tateδ _ n (isZero_tateModule_resObj_indObj H A n)
      (isZero_tateModule_resObj_indObj H A (n + 1)))

/-- **The complete cohomology of a representation, read on a subgroup, in a degree is the complete
cohomology of its coshift, read on the subgroup, in the following degree.** -/
def resCoshiftEquiv (H : Subgroup G) (A : Rep k G) (n : ℤ) :
    tateModule (resObj H A) n ≃ₗ[k] tateModule (resObj H (coshiftObj A)) (n + 1) :=
  LinearEquiv.ofBijective (tateδ (resSeq_shortExact (coshiftSeq_shortExact A) H) n).hom
    (bijective_tateδ _ n (isZero_tateModule_resObj_indObj H A n)
      (isZero_tateModule_resObj_indObj H A (n + 1)))

/-! ### Restriction -/

/-- **Restriction to a subgroup in a nonnegative degree.** -/
def tateResNat (H : Subgroup G) : (m : ℕ) → (A : Rep k G) →
    tateModule A (Int.ofNat m) →ₗ[k] tateModule (resObj H A) (Int.ofNat m)
  | 0, A => res0 H A.ρ
  | m + 1, A => (resShiftEquiv H A (Int.ofNat m)).toLinearMap ∘ₗ
      tateResNat H m (shiftObj A) ∘ₗ (tateShiftEquiv A (Int.ofNat m)).symm.toLinearMap

/-- **Restriction to a subgroup in a negative degree.** -/
def tateResNegSucc (H : Subgroup G) : (m : ℕ) → (A : Rep k G) →
    tateModule A (Int.negSucc m) →ₗ[k] tateModule (resObj H A) (Int.negSucc m)
  | 0, A => resm1 H A.ρ
  | m + 1, A => (resCoshiftEquiv H A (Int.negSucc (m + 1))).symm.toLinearMap ∘ₗ
      tateResNegSucc H m (coshiftObj A) ∘ₗ
        (tateCoshiftEquiv A (Int.negSucc (m + 1))).toLinearMap

/-- **Restriction to a subgroup in an arbitrary integer degree.** -/
def tateRes (H : Subgroup G) (A : Rep k G) : (n : ℤ) →
    tateModule A n →ₗ[k] tateModule (resObj H A) n
  | .ofNat m => tateResNat H m A
  | .negSucc m => tateResNegSucc H m A

/-! ### Corestriction -/

/-- **Corestriction from a subgroup in a nonnegative degree.** -/
def tateCorNat (H : Subgroup G) : (m : ℕ) → (A : Rep k G) →
    tateModule (resObj H A) (Int.ofNat m) →ₗ[k] tateModule A (Int.ofNat m)
  | 0, A => cor0 H A.ρ
  | m + 1, A => (tateShiftEquiv A (Int.ofNat m)).toLinearMap ∘ₗ
      tateCorNat H m (shiftObj A) ∘ₗ (resShiftEquiv H A (Int.ofNat m)).symm.toLinearMap

/-- **Corestriction from a subgroup in a negative degree.** -/
def tateCorNegSucc (H : Subgroup G) : (m : ℕ) → (A : Rep k G) →
    tateModule (resObj H A) (Int.negSucc m) →ₗ[k] tateModule A (Int.negSucc m)
  | 0, A => corm1 H A.ρ
  | m + 1, A => (tateCoshiftEquiv A (Int.negSucc (m + 1))).symm.toLinearMap ∘ₗ
      tateCorNegSucc H m (coshiftObj A) ∘ₗ
        (resCoshiftEquiv H A (Int.negSucc (m + 1))).toLinearMap

/-- **Corestriction from a subgroup in an arbitrary integer degree.** -/
def tateCor (H : Subgroup G) (A : Rep k G) : (n : ℤ) →
    tateModule (resObj H A) n →ₗ[k] tateModule A n
  | .ofNat m => tateCorNat H m A
  | .negSucc m => tateCorNegSucc H m A

/-! ### The composite -/

theorem tateCorNat_tateResNat (H : Subgroup G) :
    ∀ (m : ℕ) (A : Rep k G) (x : tateModule A (Int.ofNat m)),
      tateCorNat H m A (tateResNat H m A x) = H.index • x := by
  intro m
  induction m with
  | zero => exact fun A x => cor0_res0 H A.ρ x
  | succ m ih =>
    intro A x
    show (tateShiftEquiv A (Int.ofNat m))
        (tateCorNat H m (shiftObj A) ((resShiftEquiv H A (Int.ofNat m)).symm
          ((resShiftEquiv H A (Int.ofNat m))
            (tateResNat H m (shiftObj A)
              ((tateShiftEquiv A (Int.ofNat m)).symm x))))) = H.index • x
    rw [LinearEquiv.symm_apply_apply, ih, map_nsmul, LinearEquiv.apply_symm_apply]

theorem tateCorNegSucc_tateResNegSucc (H : Subgroup G) :
    ∀ (m : ℕ) (A : Rep k G) (x : tateModule A (Int.negSucc m)),
      tateCorNegSucc H m A (tateResNegSucc H m A x) = H.index • x := by
  intro m
  induction m with
  | zero => exact fun A x => corm1_resm1 H A.ρ x
  | succ m ih =>
    intro A x
    show (tateCoshiftEquiv A (Int.negSucc (m + 1))).symm
        (tateCorNegSucc H m (coshiftObj A) ((resCoshiftEquiv H A (Int.negSucc (m + 1)))
          ((resCoshiftEquiv H A (Int.negSucc (m + 1))).symm
            (tateResNegSucc H m (coshiftObj A)
              ((tateCoshiftEquiv A (Int.negSucc (m + 1))) x))))) = H.index • x
    rw [LinearEquiv.apply_symm_apply, ih, map_nsmul, LinearEquiv.symm_apply_apply]

/-- **Corestriction after restriction is multiplication by the index of the subgroup**, in every
integer degree. -/
theorem tateCor_tateRes (H : Subgroup G) (A : Rep k G) (n : ℤ) (x : tateModule A n) :
    tateCor H A n (tateRes H A n x) = H.index • x := by
  match n with
  | .ofNat m => exact tateCorNat_tateResNat H m A x
  | .negSucc m => exact tateCorNegSucc_tateResNegSucc H m A x

end

end InverseGalois.CFT.Tate
