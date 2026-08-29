/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CyclicTate
import InverseGalois.CFT.Kummer.CyclicIndex
import InverseGalois.CFT.Units.IdeleClassIndex
import InverseGalois.CFT.Units.IdeleRep

/-!
# The second cohomology of the idele class group of a cyclic extension

For a cyclic extension of number fields the zeroth Tate group of the idele class group, taken for
the automorphism by which a generator of the Galois group acts, is the quotient of the ideles of the
base field by the principal ideles together with the norms, and the index of that subgroup is the
degree of the extension.  The second cohomology of a finite cyclic group is the same subquotient,
so the second cohomology of the idele class group of a cyclic extension has exactly as many
elements as the Galois group.

This is the count in degree two which, next to the vanishing in degree one, is the arithmetic
content of the axioms of a class formation; for a cyclic extension both are now unconditional.

## Main results

* `InverseGalois.CFT.card_H2_ideleClassRep_of_generator`: **the second cohomology of the idele
  class group of a cyclic extension has as many elements as the Galois group.**
* `InverseGalois.CFT.card_H2_ideleClassRep_cyclic`: the same statement, for a Galois group assumed
  cyclic rather than given a generator.
* `InverseGalois.CFT.finite_H2_ideleClassRep_cyclic`: the second cohomology of the idele class
  group of a cyclic extension is finite.

## Tags

number field, idele class group, group cohomology, cyclic extension, class formation
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open groupCohomology

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **The second cohomology of the idele class group of a cyclic extension has as many elements as
the Galois group.**  The second cohomology of a finite cyclic group is the zeroth Tate group of the
automorphism by which a generator acts, that Tate group is the quotient of the ideles of the base
field by the principal ideles together with the norms, and the index of that subgroup is the
degree. -/
theorem card_H2_ideleClassRep_of_generator {σ : Gal(K/k)}
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) :
    Nat.card ↥(H2 (ideleClassRep k K)) = Nat.card Gal(K/k) := by
  haveI : Fintype Gal(K/k) := Fintype.ofFinite _
  haveI : IsCyclic Gal(K/k) := ⟨⟨σ, hgen⟩⟩
  have hbridge := card_H2_eq_card_tateH0 (A := ideleClassRep k K) (g := σ)
    (σ := ideleClassAut (k := k) σ) hgen (fun _ => rfl)
  have hindex : Nat.card (tateH0 (ideleClassAut (k := k) σ) (Nat.card Gal(K/k)))
      = Nat.card Gal(K/k) := by
    rw [card_tateH0_ideleClassAut hgen rfl, index_ideleDiag_sup_ideleNorm_eq_card]
  exact hbridge.trans hindex

/-- **The second cohomology of the idele class group of a cyclic extension has as many elements as
the Galois group.** -/
theorem card_H2_ideleClassRep_cyclic [IsCyclic Gal(K/k)] :
    Nat.card ↥(H2 (ideleClassRep k K)) = Nat.card Gal(K/k) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(K/k))
  exact card_H2_ideleClassRep_of_generator hσ

/-- The second cohomology of the idele class group of a cyclic extension is finite. -/
theorem finite_H2_ideleClassRep_cyclic [IsCyclic Gal(K/k)] :
    Finite ↥(H2 (ideleClassRep k K)) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_H2_ideleClassRep_cyclic]
    exact Nat.card_pos.ne')

end InverseGalois.CFT
