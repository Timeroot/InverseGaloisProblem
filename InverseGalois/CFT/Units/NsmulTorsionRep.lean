/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.TorsionRep
import InverseGalois.CFT.TateCohomology.TensorFunctor
import InverseGalois.CFT.TateCohomology.TorsionShift
import InverseGalois.CFT.Units.IdeleRep

/-!
# The vectors killed by a number, read on a family and read on a representation

A group acting on an abelian group by automorphisms gives a representation over the integers, and
the elements killed by a fixed number form a subgroup stable under that action.  There are two ways
in the development to name the resulting representation: as the kernel of multiplication by the
number inside the representation, and as the representation attached to the induced action on the
elements killed by the number.  They are the same, and this file says so.

The two descriptions differ only in whether the number is read as a natural number or as an
integer, and multiplying by a natural number is multiplying by the corresponding integer; so the
underlying subgroups have the same elements and the action is the same on both.  The identification
transports the vanishing of complete cohomology in either direction, which is what lets the local
computation of the roots of unity in the completions be read against the general machinery for the
elements of a representation killed by a prime.

## Main definitions

* `InverseGalois.CFT.nsmulTorsionRepEquiv`: the two descriptions have the same elements.
* `InverseGalois.CFT.nsmulTorsionRepIso`: the two descriptions are the same representation.
* `InverseGalois.CFT.tateTensorNsmulTorsionRepEquiv`: the two descriptions have the same complete
  cohomology after tensoring with any coefficients.

## Main results

* `InverseGalois.CFT.isZero_tateModule_tensorObj_nsmulTorsion_repOfAddAut`: **the kernel of
  multiplication by a number in the representation attached to an action, tensored with any
  coefficients, has no complete cohomology in a degree in which the elements killed by that number
  do not.**

## Tags

torsion, representation, Tate cohomology, tensor product
-/

namespace InverseGalois.CFT

open CategoryTheory Tate

noncomputable section

variable {G A : Type} [Group G] [AddCommGroup A] (φ : G →* AddAut A) (m : ℕ)

/-- **The elements of the representation attached to an action which are killed by a natural number
are exactly the elements killed by the corresponding integer.** -/
theorem mem_ker_nsmulLinear_iff_mem_torsionBy (a : A) :
    a ∈ LinearMap.ker (nsmulLinear ℤ m ↥(repOfAddAut φ).V)
      ↔ a ∈ AddSubgroup.torsionBy A (m : ℤ) := by
  rw [LinearMap.mem_ker, mem_torsionBy, natCast_zsmul]
  exact Iff.rfl

/-- **The kernel of multiplication by a natural number in the representation attached to an action
has the same elements as the elements killed by that number.** -/
def nsmulTorsionRepEquiv :
    ↥(nsmulTorsion (repOfAddAut φ) m).V ≃+ ↥(torsionRep φ (m : ℤ)).V where
  toFun v := ⟨v.1, (mem_ker_nsmulLinear_iff_mem_torsionBy φ m v.1).1 v.2⟩
  invFun a := ⟨a.1, (mem_ker_nsmulLinear_iff_mem_torsionBy φ m a.1).2 a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **The kernel of multiplication by a natural number in the representation attached to an action
is the representation on the elements killed by that number.** -/
def nsmulTorsionRepIso : nsmulTorsion (repOfAddAut φ) m ≅ torsionRep φ (m : ℤ) :=
  Action.mkIso (nsmulTorsionRepEquiv φ m).toIntLinearEquiv.toModuleIso fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl)

variable [Finite G]

/-- **The complete cohomology of the kernel of multiplication by a number in the representation
attached to an action, tensored with any coefficients, is that of the elements killed by that
number, tensored with the same coefficients.** -/
def tateTensorNsmulTorsionRepEquiv (W : Rep ℤ G) (n : ℤ) :
    ↥(tateModule (tensorObj (nsmulTorsion (repOfAddAut φ) m) W) n) ≃ₗ[ℤ]
      ↥(tateModule (tensorObj (torsionRep φ (m : ℤ)) W) n) :=
  (tateMapIso (tensorIsoLeft W (nsmulTorsionRepIso φ m)) n).toLinearEquiv

/-- **The kernel of multiplication by a number in the representation attached to an action,
tensored with any coefficients, has no complete cohomology in a degree in which the elements killed
by that number, tensored with the same coefficients, have none.** -/
theorem isZero_tateModule_tensorObj_nsmulTorsion_repOfAddAut (W : Rep ℤ G) (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (torsionRep φ (m : ℤ)) W) n)) :
    Limits.IsZero (tateModule (tensorObj (nsmulTorsion (repOfAddAut φ) m) W) n) :=
  isZero_tateModule_of_iso (tensorIsoLeft W (nsmulTorsionRepIso φ m)) n h

end

end InverseGalois.CFT
