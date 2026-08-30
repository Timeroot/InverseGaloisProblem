/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Graded

/-!
# The complete cohomology of the integers in degree minus two

Below degree minus one the complete cohomology of a finite group is its homology with the degree
shifted by one, so in degree minus two it is the first homology group.  For the trivial integral
representation the first homology group is the abelianization of the group, written additively:
a one cycle of a trivial representation is a formal integral combination of group elements, the
boundaries are the relations making the assignment multiplicative, and the resulting quotient is
the largest commutative quotient of the group.

This is the group side of the reciprocity law.  The complete cohomology of the idele class group in
degree zero is the classes of the base modulo the norms, and Tate's theorem identifies it with the
complete cohomology of the trivial integral representation two degrees lower; the identification
below turns that anonymous module into the abelianization of the Galois group.

## Main definitions

* `InverseGalois.CFT.Tate.tateNegTwoTrivialEquiv`: **the complete cohomology of the trivial
  integral representation in degree minus two is the abelianization of the group.**

## Tags

Tate cohomology, group homology, abelianization, reciprocity
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [Finite G]

/-- Below degree minus one the complete cohomology is the homology with the degree shifted by
one, so in degree minus two it is the first homology group. -/
theorem tateModule_neg_two (A : Rep k G) : tateModule A (-2) = groupHomology A 1 := rfl

variable (G) in
/-- **The complete cohomology of the trivial integral representation in degree minus two is the
abelianization of the group**, written additively.  The first homology group of a trivial
representation is the tensor product of the abelianization with the coefficients, and the
coefficients here are the integers. -/
def tateNegTwoTrivialEquiv :
    tateModule (Rep.trivial ℤ G ℤ) (-2) ≃ₗ[ℤ] Additive (Abelianization G) :=
  (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)).toIntLinearEquiv.trans
    (TensorProduct.rid ℤ (Additive (Abelianization G)))

end

end InverseGalois.CFT.Tate
