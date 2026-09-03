/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TateNakayama

/-!
# The theorem of Tate and Nakayama and the term that measures its failure

The comparison of the complete cohomology of a representation in a degree with the complete
cohomology of its tensor product with the coefficients two degrees higher is a map, and it exists
whatever the coefficients are: it is the connecting map of the extension attached to a class in
degree two, tensored with the coefficients, followed by the two identifications of the shift.  What
needs a hypothesis is only that the map be bijective.

The long exact sequence says exactly what the failure is.  The image of the connecting map is the
kernel of the map induced by the inclusion of the tensor product into the tensored extension, and
its kernel is the image of the map induced by the projection of the tensored extension onto the
coefficients; so the map is injective as soon as the tensored extension has no complete cohomology
in the lower of the two degrees, and surjective as soon as it has none in the higher one.  Only two
degrees are involved, and the extension enters only through its tensor product with the
coefficients.

For coefficients flat over the integers the tensored extension is acyclic and nothing is left of
the error; for coefficients with torsion the two groups are the whole content, and they are the
groups a duality theorem computes.

## Main definitions

* `InverseGalois.CFT.Tate.tateNakayamaShiftMap`: the connecting map of the tensored extension, with
  no hypothesis on the coefficients.
* `InverseGalois.CFT.Tate.tateNakayamaMap`: the comparison in the two degrees, with no hypothesis
  on the coefficients.
* `InverseGalois.CFT.Tate.tateNakayamaNextMap`, `InverseGalois.CFT.Tate.tateNakayamaTwoNextMap`: the
  map leaving the comparison in the long exact sequence.
* `InverseGalois.CFT.Tate.tateNakayamaEquivOfTwo`,
  `InverseGalois.CFT.Tate.tateNakayamaTwoEquivOfTwo`: the comparison as an isomorphism, from the
  vanishing of the tensored extension in the two degrees that matter.

## Main results

* `InverseGalois.CFT.Tate.range_tateNakayamaShiftMap`,
  `InverseGalois.CFT.Tate.ker_tateNakayamaShiftMap`: **the image and the kernel of the comparison
  are the two neighbouring maps of the long exact sequence of the tensored extension.**
* `InverseGalois.CFT.Tate.ker_tateNakayamaMap`,
  `InverseGalois.CFT.Tate.ker_tateNakayamaNextMap`: **the kernel of the comparison is the image of
  the map coming out of the tensored extension, and the image of the comparison is the kernel of
  the map going into it** — the four term exact sequence with the tensored extension at both ends.
* `InverseGalois.CFT.Tate.injective_tateNakayamaMap`,
  `InverseGalois.CFT.Tate.surjective_tateNakayamaMap`: **the comparison is injective, respectively
  surjective, as soon as the tensored extension has no complete cohomology in the lower,
  respectively the higher, of the two degrees.**
* `InverseGalois.CFT.Tate.coe_tateNakayamaEquiv`, `InverseGalois.CFT.Tate.coe_tateNakayamaTwoEquiv`:
  the isomorphism built from the vanishing in every degree is this map.

## Tags

Tate cohomology, Tate–Nakayama, tensor product, fundamental class, dimension shifting
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### The connecting map of the tensored extension -/

section Nakayama

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  (A : Rep k G) (b : groupCohomology.cocycles₁ (shiftObj A)) (M : Rep k G)

/-- **The tensored extension has no complete cohomology in a degree** as soon as the extension
itself keeps none in that degree after tensoring. -/
theorem isZero_tateModule_cocycleTensorObj' (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) n)) :
    Limits.IsZero (tateModule (cocycleTensorObj (shiftObj A) b M) n) :=
  isZero_tateModule_of_iso (cocycleTensorIso (shiftObj A) M b).symm n h

/-- **The connecting map of the tensored extension**, with no hypothesis on the coefficients: the
complete cohomology of a representation in a degree maps to the complete cohomology of the shift
tensored with it in the following degree. -/
def tateNakayamaShiftMap (n : ℤ) :
    tateModule M n ⟶ tateModule (tensorObj (shiftObj A) M) (n + 1) :=
  tateδ (cocycleTensorSeq_shortExact (shiftObj A) b M) n

/-- **The image of the connecting map of the tensored extension** is the kernel of the map induced
by the inclusion of the tensor product into it. -/
theorem range_tateNakayamaShiftMap (n : ℤ) :
    LinearMap.range (tateNakayamaShiftMap A b M n).hom
      = LinearMap.ker (tateMap (cocycleTensorSeq (shiftObj A) b M).f (n + 1)).hom := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  exact (tateExact_δ_map (cocycleTensorSeq_shortExact (shiftObj A) b M) n x).symm

/-- **The kernel of the connecting map of the tensored extension** is the image of the map induced
by its projection onto the coefficients. -/
theorem ker_tateNakayamaShiftMap (n : ℤ) :
    LinearMap.ker (tateNakayamaShiftMap A b M n).hom
      = LinearMap.range (tateMap (cocycleTensorSeq (shiftObj A) b M).g n).hom := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  exact tateExact_map_δ (cocycleTensorSeq_shortExact (shiftObj A) b M) n x

/-- **The connecting map of the tensored extension is injective** as soon as the extension keeps no
complete cohomology in that degree after tensoring. -/
theorem injective_tateNakayamaShiftMap (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) n)) :
    Function.Injective (tateNakayamaShiftMap A b M n) :=
  injective_tateδ (cocycleTensorSeq_shortExact (shiftObj A) b M) n
    (isZero_tateModule_cocycleTensorObj' A b M n h)

/-- **The connecting map of the tensored extension is surjective** as soon as the extension keeps
no complete cohomology in the following degree after tensoring. -/
theorem surjective_tateNakayamaShiftMap (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) (n + 1))) :
    Function.Surjective (tateNakayamaShiftMap A b M n) :=
  surjective_tateδ (cocycleTensorSeq_shortExact (shiftObj A) b M) n
    (isZero_tateModule_cocycleTensorObj' A b M (n + 1) h)

/-! ### The comparison in two degrees -/

/-- **The comparison of Tate and Nakayama**, with no hypothesis on the coefficients: the complete
cohomology of a representation in a degree maps to the complete cohomology of its tensor product
with the coefficients two degrees higher. -/
def tateNakayamaMap (n : ℤ) : tateModule M n →ₗ[k] tateModule (tensorObj A M) (n + 1 + 1) :=
  (tateShiftEquiv (tensorObj A M) (n + 1)).toLinearMap ∘ₗ
    (tateMap (shiftTensorIso A M).hom (n + 1)).hom ∘ₗ (tateNakayamaShiftMap A b M n).hom

/-- **The two identifications that follow the connecting map**: the shift of a tensor product is
the tensor product of the shift, and the complete cohomology of a shift in a degree is the complete
cohomology of the representation one degree higher. -/
def tateNakayamaIso (n : ℤ) :
    tateModule (tensorObj (shiftObj A) M) (n + 1) ≃ₗ[k] tateModule (tensorObj A M) (n + 1 + 1) :=
  (tateMapIso (shiftTensorIso A M) (n + 1)).toLinearEquiv.trans
    (tateShiftEquiv (tensorObj A M) (n + 1))

/-- The comparison of Tate and Nakayama is the connecting map followed by the two
identifications. -/
theorem tateNakayamaMap_apply (n : ℤ) (x : tateModule M n) :
    tateNakayamaMap A b M n x = tateNakayamaIso A M n ((tateNakayamaShiftMap A b M n).hom x) := rfl

/-- **The kernel of the comparison of Tate and Nakayama** is the image of the map induced by the
projection of the tensored extension onto the coefficients. -/
theorem ker_tateNakayamaMap (n : ℤ) :
    LinearMap.ker (tateNakayamaMap A b M n)
      = LinearMap.range (tateMap (cocycleTensorSeq (shiftObj A) b M).g n).hom := by
  rw [← ker_tateNakayamaShiftMap A b M n]
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, tateNakayamaMap_apply,
    LinearEquiv.map_eq_zero_iff]

/-- **The map leaving the comparison of Tate and Nakayama** in the long exact sequence: the map
induced by the inclusion of the tensor product into the tensored extension, read through the two
identifications. -/
def tateNakayamaNextMap (n : ℤ) :
    tateModule (tensorObj A M) (n + 1 + 1) →ₗ[k]
      tateModule (cocycleTensorObj (shiftObj A) b M) (n + 1) :=
  (tateMap (cocycleTensorSeq (shiftObj A) b M).f (n + 1)).hom ∘ₗ
    (tateNakayamaIso A M n).symm.toLinearMap

/-- **The image of the comparison of Tate and Nakayama is the kernel of the map leaving it**, so the
two together are a four term exact sequence with the tensored extension at both ends. -/
theorem ker_tateNakayamaNextMap (n : ℤ) :
    LinearMap.ker (tateNakayamaNextMap A b M n) = LinearMap.range (tateNakayamaMap A b M n) := by
  ext y
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hy
    have hmem : (tateNakayamaIso A M n).symm y
        ∈ LinearMap.range (tateNakayamaShiftMap A b M n).hom := by
      rw [range_tateNakayamaShiftMap]
      exact LinearMap.mem_ker.2 hy
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, by rw [tateNakayamaMap_apply, hx, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨x, rfl⟩
    show (tateMap (cocycleTensorSeq (shiftObj A) b M).f (n + 1)).hom
      ((tateNakayamaIso A M n).symm (tateNakayamaMap A b M n x)) = 0
    rw [tateNakayamaMap_apply, LinearEquiv.symm_apply_apply]
    exact LinearMap.mem_ker.1
      (by rw [← range_tateNakayamaShiftMap]; exact ⟨x, rfl⟩)

/-- The isomorphism built from the vanishing of the tensored extension in every degree is the
comparison map. -/
theorem coe_tateNakayamaEquiv
    (h : ∀ m : ℤ, Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) m))
    (n : ℤ) : ⇑(tateNakayamaEquiv A b M h n) = tateNakayamaMap A b M n := rfl

/-- **The comparison of Tate and Nakayama is injective** as soon as the extension keeps no complete
cohomology in the lower of the two degrees after tensoring. -/
theorem injective_tateNakayamaMap (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) n)) :
    Function.Injective (tateNakayamaMap A b M n) :=
  ((tateShiftEquiv (tensorObj A M) (n + 1)).injective.comp
    (tateMapIso (shiftTensorIso A M) (n + 1)).toLinearEquiv.injective).comp
      (injective_tateNakayamaShiftMap A b M n h)

/-- **The comparison of Tate and Nakayama is surjective** as soon as the extension keeps no complete
cohomology in the higher of the two degrees after tensoring. -/
theorem surjective_tateNakayamaMap (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) (n + 1))) :
    Function.Surjective (tateNakayamaMap A b M n) :=
  ((tateShiftEquiv (tensorObj A M) (n + 1)).surjective.comp
    (tateMapIso (shiftTensorIso A M) (n + 1)).toLinearEquiv.surjective).comp
      (surjective_tateNakayamaShiftMap A b M n h)

/-- **The comparison of Tate and Nakayama is bijective** as soon as the extension keeps no complete
cohomology in the two degrees that matter after tensoring. -/
theorem bijective_tateNakayamaMap (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) n))
    (h' : Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) (n + 1))) :
    Function.Bijective (tateNakayamaMap A b M n) :=
  ⟨injective_tateNakayamaMap A b M n h, surjective_tateNakayamaMap A b M n h'⟩

/-- **The complete cohomology of a representation in a degree is the complete cohomology of its
tensor product with the coefficients two degrees higher**, as soon as the extension attached to the
cocycle keeps no complete cohomology in the two degrees that matter after tensoring. -/
def tateNakayamaEquivOfTwo (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) n))
    (h' : Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) (n + 1))) :
    tateModule M n ≃ₗ[k] tateModule (tensorObj A M) (n + 1 + 1) :=
  LinearEquiv.ofBijective (tateNakayamaMap A b M n) (bijective_tateNakayamaMap A b M n h h')

end Nakayama

/-! ### A class in degree two -/

section DegreeTwo

variable {G : Type} [Group G] [Finite G] (A : Rep ℤ G) (α : tateModule A 2) (M : Rep ℤ G)

/-- **The comparison of Tate and Nakayama for the cocycle attached to a prescribed class in degree
two**, with no hypothesis on the coefficients. -/
def tateNakayamaTwoMap (n : ℤ) : tateModule M n →ₗ[ℤ] tateModule (tensorObj A M) (n + 1 + 1) :=
  tateNakayamaMap A (tateTwoCocycle A α) M n

/-- **The kernel of the comparison** for the cocycle attached to a prescribed class in degree two is
the image of the map induced by the projection of the tensored extension onto the coefficients. -/
theorem ker_tateNakayamaTwoMap (n : ℤ) :
    LinearMap.ker (tateNakayamaTwoMap A α M n)
      = LinearMap.range
        (tateMap (cocycleTensorSeq (shiftObj A) (tateTwoCocycle A α) M).g n).hom :=
  ker_tateNakayamaMap A (tateTwoCocycle A α) M n

/-- **The map leaving the comparison** for the cocycle attached to a prescribed class in degree
two. -/
def tateNakayamaTwoNextMap (n : ℤ) :
    tateModule (tensorObj A M) (n + 1 + 1) →ₗ[ℤ]
      tateModule (cocycleTensorObj (shiftObj A) (tateTwoCocycle A α) M) (n + 1) :=
  tateNakayamaNextMap A (tateTwoCocycle A α) M n

/-- **The image of the comparison is the kernel of the map leaving it**, for the cocycle attached to
a prescribed class in degree two. -/
theorem ker_tateNakayamaTwoNextMap (n : ℤ) :
    LinearMap.ker (tateNakayamaTwoNextMap A α M n)
      = LinearMap.range (tateNakayamaTwoMap A α M n) :=
  ker_tateNakayamaNextMap A (tateTwoCocycle A α) M n

/-- The isomorphism built from the vanishing of the tensored extension in every degree is the
comparison map. -/
theorem coe_tateNakayamaTwoEquiv
    (h : ∀ m : ℤ, Limits.IsZero
      (tateModule (tensorObj (cocycleObj (shiftObj A) (tateTwoCocycle A α)) M) m))
    (n : ℤ) : ⇑(tateNakayamaTwoEquiv A α M h n) = tateNakayamaTwoMap A α M n := rfl

/-- **The comparison is bijective** as soon as the extension attached to the class keeps no complete
cohomology in the two degrees that matter after tensoring. -/
theorem bijective_tateNakayamaTwoMap (n : ℤ)
    (h : Limits.IsZero
      (tateModule (tensorObj (cocycleObj (shiftObj A) (tateTwoCocycle A α)) M) n))
    (h' : Limits.IsZero
      (tateModule (tensorObj (cocycleObj (shiftObj A) (tateTwoCocycle A α)) M) (n + 1))) :
    Function.Bijective (tateNakayamaTwoMap A α M n) :=
  bijective_tateNakayamaMap A (tateTwoCocycle A α) M n h h'

/-- **The complete cohomology of a representation in a degree is the complete cohomology of its
tensor product with the coefficients two degrees higher**, for the cocycle attached to a prescribed
class in degree two, from the vanishing of the tensored extension in the two degrees that matter. -/
def tateNakayamaTwoEquivOfTwo (n : ℤ)
    (h : Limits.IsZero
      (tateModule (tensorObj (cocycleObj (shiftObj A) (tateTwoCocycle A α)) M) n))
    (h' : Limits.IsZero
      (tateModule (tensorObj (cocycleObj (shiftObj A) (tateTwoCocycle A α)) M) (n + 1))) :
    tateModule M n ≃ₗ[ℤ] tateModule (tensorObj A M) (n + 1 + 1) :=
  tateNakayamaEquivOfTwo A (tateTwoCocycle A α) M n h h'

end DegreeTwo

end

end InverseGalois.CFT.Tate
