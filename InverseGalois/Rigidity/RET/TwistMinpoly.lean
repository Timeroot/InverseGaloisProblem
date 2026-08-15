/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Twist

/-!
# Equations and primitive elements in a changed coordinate

A change of coordinate on the line does not move the points of a cover, only the way the base acts
on them; so an element of the cover generates it in one coordinate exactly when it generates it in
the other, and its equation in the new coordinate is its old equation read through the change.
This file records those two transports, which is all that is needed to run the local theory of a
cover at a point of the twisted coordinate.

Generation is transported through the degree: an element generates a finite extension exactly when
the degree of its equation is the degree of the extension, and both quantities are unchanged by the
coordinate change.

## Main results

* `Rigidity.RET.Twist.minpoly_ofBase` — the equation in the new coordinate is the old equation read
  through the coordinate change.
* `Rigidity.RET.Twist.adjoin_ofBase_eq_top` — a primitive element stays primitive.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-! ### Generation and the degree of the equation -/

/-- **An element generates a finite extension exactly when the degree of its equation is the degree
of the extension.** -/
theorem adjoin_eq_top_iff_natDegree {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {x : E} (hx : IsIntegral F x) :
    IntermediateField.adjoin F {x} = ⊤ ↔ (minpoly F x).natDegree = Module.finrank F E := by
  constructor
  · intro h
    rw [← IntermediateField.adjoin.finrank hx, h, IntermediateField.finrank_top']
  · intro h
    refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
    rw [IntermediateField.adjoin.finrank hx, IntermediateField.finrank_top', h]

namespace Twist

variable {M : Type} [Field M] {φ : RatFunc k ≃+* RatFunc k}

/-- The element of the twist underlying an element of the field: the twist has the same elements as
the field it twists. -/
def ofBase (φ : RatFunc k ≃+* RatFunc k) (M : Type) [Field M] : M ≃+* Twist φ M :=
  RingEquiv.refl M

@[simp] theorem toBase_ofBase (x : M) : toBase (ofBase φ M x) = x := rfl

variable [Algebra (RatFunc k) M]

/-- Scalars act on the twist through the coordinate change. -/
theorem algebraMap_comp_symm :
    (algebraMap (RatFunc k) (Twist φ M)).comp (φ.symm : RatFunc k →+* RatFunc k)
      = ((ofBase φ M : M ≃+* Twist φ M) : M →+* Twist φ M).comp (algebraMap (RatFunc k) M) :=
  RingHom.ext fun f => algebraMap_symm f

/-- **The equation of an element in the new coordinate** is its equation in the old one, read
through the coordinate change. -/
theorem minpoly_ofBase [FiniteDimensional (RatFunc k) M] (x : M) :
    minpoly (RatFunc k) (ofBase φ M x)
      = (minpoly (RatFunc k) x).map (φ.symm : RatFunc k →+* RatFunc k) :=
  (minpoly.map_eq_of_equiv_equiv (f := (φ.symm : RatFunc k ≃+* RatFunc k))
    (g := (ofBase φ M : M ≃+* Twist φ M)) algebraMap_comp_symm x).symm

/-- The twist has the same degree over the base as the original. -/
theorem finrank_eq [FiniteDimensional (RatFunc k) M] :
    Module.finrank (RatFunc k) (Twist φ M) = Module.finrank (RatFunc k) M :=
  congrArg Cardinal.toNat (rank_eq φ M)

/-- **A primitive element stays primitive in the new coordinate.** -/
theorem adjoin_ofBase_eq_top [FiniteDimensional (RatFunc k) M] {x : M}
    (hgen : IntermediateField.adjoin (RatFunc k) {x} = ⊤) :
    IntermediateField.adjoin (RatFunc k) {ofBase φ M x} = ⊤ := by
  have hx : IsIntegral (RatFunc k) x := Algebra.IsIntegral.isIntegral x
  have hx' : IsIntegral (RatFunc k) (ofBase φ M x) := Algebra.IsIntegral.isIntegral _
  refine (adjoin_eq_top_iff_natDegree hx').2 ?_
  rw [minpoly_ofBase, Polynomial.natDegree_map, finrank_eq]
  exact (adjoin_eq_top_iff_natDegree hx).1 hgen

end Twist

end Rigidity.RET

end
