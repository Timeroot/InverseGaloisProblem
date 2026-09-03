/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TateNakayamaError
import InverseGalois.CFT.TateCohomology.TensorPTorsionShift
import InverseGalois.CFT.TateCohomology.TorsionNakayama

/-!
# The failure of Tate and Nakayama at a prime, read on the vectors killed by that prime

The comparison of Tate and Nakayama is a map whatever the coefficients are, and what measures its
failure is the complete cohomology of the extension attached to the fundamental class, tensored
with the coefficients, in two neighbouring degrees.  For coefficients killed by a prime that
measure is computed here, and what it comes out to is a statement about the representation one
starts from.

The extension attached to the fundamental class is cohomologically trivial on every Sylow subgroup,
so tensoring it with coefficients killed by a prime leaves, in a degree, exactly the complete
cohomology of the vectors it kills tensored with the same coefficients two degrees higher.  Those
vectors are the vectors of the shift killed by the prime, because the base ring has no torsion at
the prime; and the sequence defining the shift stays short exact on the vectors killed by the prime
and stays short exact after tensoring, because its middle term is killed by the prime, so one more
degree is gained.

Altogether **the extension attached to the fundamental class, tensored with coefficients killed by
a prime, has in a degree the complete cohomology of the vectors of the representation killed by the
prime, tensored with the same coefficients, three degrees higher** -- and hence **the comparison of
Tate and Nakayama is bijective as soon as those groups vanish in the two degrees that matter.**
Nothing is lost when they do not vanish: the long exact sequence of the tensored extension names
what is killed and what is missed, so the comparison sits inside a four term exact sequence with
those groups at both ends.  For the idele class group of a number field the vectors killed by the
prime are the roots of unity in the completions, so both ends are purely local.

## Main definitions

* `InverseGalois.CFT.Tate.tensorShiftNsmulTorsionEquiv`: the tensored form of the shift on the
  vectors killed by a prime.
* `InverseGalois.CFT.Tate.cocycleTensorPTorsionEquiv`: the complete cohomology of the tensored
  extension, as that of the vectors killed by the prime three degrees higher.
* `InverseGalois.CFT.Tate.tateNakayamaPTorsionErrorLeft`,
  `InverseGalois.CFT.Tate.tateNakayamaPTorsionErrorRight`: the two maps surrounding the comparison
  of Tate and Nakayama in the long exact sequence, with the vectors killed by the prime at both
  ends.
* `InverseGalois.CFT.Tate.tateNakayamaTwoEquivOfPTorsion`: the comparison of Tate and Nakayama for
  coefficients killed by a prime, as an isomorphism.

## Main results

* `InverseGalois.CFT.Tate.exact_tateNakayamaPTorsionErrorLeft`,
  `InverseGalois.CFT.Tate.exact_tateNakayamaPTorsionErrorRight`: **the four term exact sequence
  measuring the failure of Tate and Nakayama at a prime**, with the vectors of the representation
  killed by the prime, tensored with the coefficients, at both ends and in no other degrees.

* `InverseGalois.CFT.Tate.isZero_tateModule_tensorObj_cocycleObj_of_nsmulTorsion`: **the tensored
  extension has no complete cohomology in a degree in which the vectors killed by the prime,
  tensored with the coefficients, have none three degrees higher.**
* `InverseGalois.CFT.Tate.bijective_tateNakayamaTwoMap_of_nsmulTorsion`: **the comparison of Tate
  and Nakayama with coefficients killed by a prime is bijective as soon as the vectors of the
  representation killed by the prime, tensored with the coefficients, have no complete cohomology
  in the two relevant degrees.**

## Tags

Tate-Nakayama, Tate cohomology, torsion, dimension shifting, fundamental class, tensor product
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

noncomputable section

/-! ### The shift on the vectors killed by a prime, after tensoring -/

section Shift

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (A W : Rep ℤ G)

omit [Finite G] in
/-- **The sequence defining the shift, taken on the vectors killed by a prime, stays short exact
after tensoring with any coefficients**, because its middle term is killed by the prime. -/
theorem tensorNsmulTorsionShiftSeq_shortExact :
    (tensorSeq W (nsmulTorsionSeqOf p (shiftSeq A))).ShortExact :=
  tensorSeq_shortExact_of_nsmul (nsmulTorsion_shiftSeq_shortExact A p) W
    (nsmul_nsmulTorsion_eq_zero (indObj A) p)

omit [Fact p.Prime] in
/-- **The vectors killed by a prime in the functions on the group have no complete cohomology after
tensoring with any coefficients.** -/
theorem isZero_tateModule_tensorObj_nsmulTorsion_indObj (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj (nsmulTorsion (indObj A) p) W) n) :=
  isZero_tateModule_of_iso (tensorIsoLeft W (indNsmulTorsionIso A p)).symm n
    (isZero_tateModule_tensorObj_inducedRep ↥(nsmulTorsion A p).V W n)

/-- **The complete cohomology of the vectors killed by a prime in the shift, tensored with any
coefficients, is that of the vectors killed by the prime in the representation, tensored with the
same coefficients, one degree higher.** -/
def tensorShiftNsmulTorsionEquiv (n : ℤ) :
    ↥(tateModule (tensorObj (nsmulTorsion (shiftObj A) p) W) n)
      ≃ₗ[ℤ] ↥(tateModule (tensorObj (nsmulTorsion A p) W) (n + 1)) :=
  LinearEquiv.ofBijective (tateδ (tensorNsmulTorsionShiftSeq_shortExact (p := p) A W) n).hom
    (bijective_tateδ (tensorNsmulTorsionShiftSeq_shortExact (p := p) A W) n
      (isZero_tateModule_tensorObj_nsmulTorsion_indObj A W n)
      (isZero_tateModule_tensorObj_nsmulTorsion_indObj A W (n + 1)))

end Shift

/-! ### The error term of Tate and Nakayama at a prime -/

section Error

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (A : Rep ℤ G)
  (α : tateModule A 2) (W : Rep ℤ G) (hW : ∀ w : ↥W.V, p • w = 0)
  (hT : ∀ q : ℕ, q.Prime → ∀ P : Sylow q G, IsTateClassTwo (P : Subgroup G) A α)

include hW hT

/-- **The extension attached to the fundamental class, tensored with coefficients killed by a
prime, has in a degree the complete cohomology of the vectors of the representation killed by the
prime, tensored with the same coefficients, three degrees higher.** -/
def cocycleTensorPTorsionEquiv (n : ℤ) :
    ↥(tateModule (tensorObj (cocycleObj (shiftObj A) (tateTwoCocycle A α)) W) n)
      ≃ₗ[ℤ] ↥(tateModule (tensorObj (nsmulTorsion A p) W) (n + 1 + 1 + 1)) :=
  (tensorPTorsionShiftFreeEquiv (cocycleObj (shiftObj A) (tateTwoCocycle A α)) W hW
      (fun P => isZero_tateModule_resObj_cocycleObj_shiftObj A α hT p (Fact.out : p.Prime) P)
      n).trans
    ((tateMapIso (tensorIsoLeft W
          (cocycleNsmulTorsionIso (shiftObj A) (tateTwoCocycle A α) p
            (eq_zero_of_nsmul_eq_zero_int (p := p))).symm) (n + 1 + 1)).toLinearEquiv.trans
      (tensorShiftNsmulTorsionEquiv (p := p) A W (n + 1 + 1)))

/-- **The complete cohomology of the tensored extension in the form it takes in the long exact
sequence**, as that of the vectors of the representation killed by the prime, tensored with the
coefficients, three degrees higher. -/
def cocycleTensorObjPTorsionEquiv (n : ℤ) :
    ↥(tateModule (cocycleTensorObj (shiftObj A) (tateTwoCocycle A α) W) n)
      ≃ₗ[ℤ] ↥(tateModule (tensorObj (nsmulTorsion A p) W) (n + 1 + 1 + 1)) :=
  (tateMapIso (cocycleTensorIso (shiftObj A) W (tateTwoCocycle A α)) n).toLinearEquiv.symm.trans
    (cocycleTensorPTorsionEquiv A α W hW hT n)

/-- **The map entering the comparison of Tate and Nakayama at a prime**: the vectors of the
representation killed by the prime, tensored with the coefficients, three degrees above the lower
of the two degrees, mapping to the coefficients in that degree. -/
def tateNakayamaPTorsionErrorLeft (n : ℤ) :
    ↥(tateModule (tensorObj (nsmulTorsion A p) W) (n + 1 + 1 + 1)) →ₗ[ℤ] ↥(tateModule W n) :=
  (tateMap (cocycleTensorSeq (shiftObj A) (tateTwoCocycle A α) W).g n).hom ∘ₗ
    (cocycleTensorObjPTorsionEquiv A α W hW hT n).symm.toLinearMap

/-- **The map leaving the comparison of Tate and Nakayama at a prime**: the tensor product with the
representation two degrees above the lower of the two degrees, mapping to the vectors killed by the
prime, tensored with the coefficients, four degrees above it. -/
def tateNakayamaPTorsionErrorRight (n : ℤ) :
    ↥(tateModule (tensorObj A W) (n + 1 + 1)) →ₗ[ℤ]
      ↥(tateModule (tensorObj (nsmulTorsion A p) W) (n + 1 + 1 + 1 + 1)) :=
  (cocycleTensorObjPTorsionEquiv A α W hW hT (n + 1)).toLinearMap ∘ₗ
    tateNakayamaTwoNextMap A α W n

/-- **The kernel of the comparison of Tate and Nakayama at a prime is the image of the vectors of
the representation killed by the prime**, tensored with the coefficients, three degrees above the
lower of the two degrees. -/
theorem range_tateNakayamaPTorsionErrorLeft (n : ℤ) :
    LinearMap.range (tateNakayamaPTorsionErrorLeft A α W hW hT n)
      = LinearMap.ker (tateNakayamaTwoMap A α W n) := by
  rw [ker_tateNakayamaTwoMap]
  show LinearMap.range ((tateMap (cocycleTensorSeq (shiftObj A) (tateTwoCocycle A α) W).g n).hom ∘ₗ
    (cocycleTensorObjPTorsionEquiv A α W hW hT n).symm.toLinearMap) = _
  rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

/-- **The image of the comparison of Tate and Nakayama at a prime is the kernel of the map into the
vectors of the representation killed by the prime**, tensored with the coefficients, four degrees
above the lower of the two degrees. -/
theorem ker_tateNakayamaPTorsionErrorRight (n : ℤ) :
    LinearMap.ker (tateNakayamaPTorsionErrorRight A α W hW hT n)
      = LinearMap.range (tateNakayamaTwoMap A α W n) := by
  rw [← ker_tateNakayamaTwoNextMap A α W n]
  show LinearMap.ker ((cocycleTensorObjPTorsionEquiv A α W hW hT (n + 1)).toLinearMap ∘ₗ
    tateNakayamaTwoNextMap A α W n) = _
  exact LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot_of_injective
      (cocycleTensorObjPTorsionEquiv A α W hW hT (n + 1)).injective)

/-- **The comparison of Tate and Nakayama at a prime is exact at the coefficients**: what it kills
comes from the vectors of the representation killed by the prime, tensored with the coefficients,
three degrees above. -/
theorem exact_tateNakayamaPTorsionErrorLeft (n : ℤ) :
    Function.Exact (tateNakayamaPTorsionErrorLeft A α W hW hT n) (tateNakayamaTwoMap A α W n) :=
  LinearMap.exact_iff.2 (range_tateNakayamaPTorsionErrorLeft A α W hW hT n).symm

/-- **The comparison of Tate and Nakayama at a prime is exact at the tensor product**: what dies in
the vectors of the representation killed by the prime, tensored with the coefficients, four degrees
above, comes from the coefficients. -/
theorem exact_tateNakayamaPTorsionErrorRight (n : ℤ) :
    Function.Exact (tateNakayamaTwoMap A α W n) (tateNakayamaPTorsionErrorRight A α W hW hT n) :=
  LinearMap.exact_iff.2 (ker_tateNakayamaPTorsionErrorRight A α W hW hT n)

/-- **The tensored extension has no complete cohomology in a degree in which the vectors of the
representation killed by the prime, tensored with the coefficients, have none three degrees
higher.** -/
theorem isZero_tateModule_tensorObj_cocycleObj_of_nsmulTorsion (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (nsmulTorsion A p) W) (n + 1 + 1 + 1))) :
    Limits.IsZero
      (tateModule (tensorObj (cocycleObj (shiftObj A) (tateTwoCocycle A α)) W) n) :=
  isZero_of_forall_eq_zero fun x =>
    (cocycleTensorPTorsionEquiv A α W hW hT n).injective
      (by rw [map_zero]; exact eq_zero_of_isZero h _)

/-- **The comparison of Tate and Nakayama with coefficients killed by a prime is injective** as
soon as the vectors of the representation killed by the prime, tensored with the coefficients, have
no complete cohomology three degrees above the lower of the two degrees. -/
theorem injective_tateNakayamaTwoMap_of_nsmulTorsion (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (nsmulTorsion A p) W) (n + 1 + 1 + 1))) :
    Function.Injective (tateNakayamaTwoMap A α W n) :=
  injective_tateNakayamaMap A (tateTwoCocycle A α) W n
    (isZero_tateModule_tensorObj_cocycleObj_of_nsmulTorsion A α W hW hT n h)

/-- **The comparison of Tate and Nakayama with coefficients killed by a prime is surjective** as
soon as the vectors of the representation killed by the prime, tensored with the coefficients, have
no complete cohomology four degrees above the lower of the two degrees. -/
theorem surjective_tateNakayamaTwoMap_of_nsmulTorsion (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (nsmulTorsion A p) W) (n + 1 + 1 + 1 + 1))) :
    Function.Surjective (tateNakayamaTwoMap A α W n) :=
  surjective_tateNakayamaMap A (tateTwoCocycle A α) W n
    (isZero_tateModule_tensorObj_cocycleObj_of_nsmulTorsion A α W hW hT (n + 1) h)

/-- **The comparison of Tate and Nakayama with coefficients killed by a prime is bijective** as
soon as the vectors of the representation killed by the prime, tensored with the coefficients, have
no complete cohomology in the two relevant degrees. -/
theorem bijective_tateNakayamaTwoMap_of_nsmulTorsion (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (nsmulTorsion A p) W) (n + 1 + 1 + 1)))
    (h' : Limits.IsZero (tateModule (tensorObj (nsmulTorsion A p) W) (n + 1 + 1 + 1 + 1))) :
    Function.Bijective (tateNakayamaTwoMap A α W n) :=
  ⟨injective_tateNakayamaTwoMap_of_nsmulTorsion A α W hW hT n h,
    surjective_tateNakayamaTwoMap_of_nsmulTorsion A α W hW hT n h'⟩

/-- **The complete cohomology of coefficients killed by a prime in a degree is the complete
cohomology of their tensor product with the representation two degrees higher**, as soon as the
vectors of the representation killed by the prime, tensored with the coefficients, have no complete
cohomology in the two relevant degrees. -/
def tateNakayamaTwoEquivOfPTorsion (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (nsmulTorsion A p) W) (n + 1 + 1 + 1)))
    (h' : Limits.IsZero (tateModule (tensorObj (nsmulTorsion A p) W) (n + 1 + 1 + 1 + 1))) :
    ↥(tateModule W n) ≃ₗ[ℤ] ↥(tateModule (tensorObj A W) (n + 1 + 1)) :=
  LinearEquiv.ofBijective (tateNakayamaTwoMap A α W n)
    (bijective_tateNakayamaTwoMap_of_nsmulTorsion A α W hW hT n h h')

end Error

end

end InverseGalois.CFT.Tate
