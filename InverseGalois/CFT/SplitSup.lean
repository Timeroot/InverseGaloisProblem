/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.SplitCompositum
import InverseGalois.CFT.Scholz.CompositumTransport

/-!
# Splitting completely in a compositum

A rational prime splitting completely in two number fields splits completely in their compositum.
Inside an ambient Galois number field presented as the compositum of two normal subextensions this
is immediate from the decomposition group: restriction to one factor is injective on the
decomposition group of a prime once the other factor is totally split, and the decomposition group
of a totally split factor is trivial, so the decomposition group upstairs is trivial as well and
its order, the ramification index times the residue degree, is one.

The general statement follows by transporting the two fields into their compositum, where they
generate the whole field.

## Main results

* `InverseGalois.CFT.splitsCompletely_of_sup_eq_top`: a prime splitting completely in two normal
  subextensions generating a Galois number field splits completely in that field.
* `InverseGalois.CFT.splitsCompletely_sup`: **a prime splitting completely in two number fields
  splits completely in their compositum.**

## Tags

number field, splitting completely, compositum, decomposition group
-/

open NumberField InverseGalois.NumberTheory Pointwise

namespace InverseGalois.CFT

/-- **A prime splitting completely in two normal subextensions generating the whole field splits
completely in that field.**  The decomposition group of a prime upstairs injects into the
decomposition group of the prime below it in the first factor, which is trivial, and the order of
the decomposition group is the ramification index times the residue degree. -/
theorem splitsCompletely_of_sup_eq_top {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N]
    (A B : IntermediateField ℚ N) [Normal ℚ ↥A] [Normal ℚ ↥B] (hAB : A ⊔ B = ⊤) {p : ℕ}
    (hp : p.Prime) (hA : SplitsCompletely ↥A p) (hB : SplitsCompletely ↥B p) :
    SplitsCompletely N p := by
  haveI : NumberField ↥A := ⟨⟩
  haveI : IsGalois ℚ ↥A := ⟨⟩
  rintro P ⟨hP1, hP2⟩
  haveI := hP1
  haveI := hP2
  haveI : (P.under (𝓞 ↥A)).LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨by rw [Ideal.under_under]; exact hP2.over⟩
  have hle := card_stabilizer_le_of_splitsCompletely A B hAB hp P hB
  rw [stabilizer_eq_bot_of_splitsCompletely ↥A hp (P.under (𝓞 ↥A)) hA] at hle
  have hcard := card_stabilizer_eq_mul N hp P
  have h1 : Nat.card (MulAction.stabilizer Gal(N/ℚ) P) = 1 :=
    le_antisymm (by simpa using hle) Nat.card_pos
  rw [h1] at hcard
  exact ⟨Nat.dvd_one.mp ⟨_, hcard⟩, Nat.dvd_one.mp ⟨_, by rw [mul_comm]; exact hcard⟩⟩

/-- **A prime splitting completely in two number fields splits completely in their compositum.**
The two fields are carried into their compositum, where they generate the whole field. -/
theorem splitsCompletely_sup {L : Type*} [Field L] [CharZero L] (A B : IntermediateField ℚ L)
    [NumberField ↥A] [NumberField ↥B] [Normal ℚ ↥A] [Normal ℚ ↥B] {p : ℕ}
    (hp : p.Prime) (hA : SplitsCompletely ↥A p) (hB : SplitsCompletely ↥B p) :
    SplitsCompletely ↥(A ⊔ B) p := by
  haveI : IsGalois ℚ ↥(A ⊔ B) := ⟨⟩
  have hAle : A ≤ A ⊔ B := le_sup_left
  have hBle : B ≤ A ⊔ B := le_sup_right
  haveI : Normal ℚ ↥(IntermediateField.restrict hAle) :=
    Normal.of_algEquiv (IntermediateField.restrict_algEquiv hAle)
  haveI : Normal ℚ ↥(IntermediateField.restrict hBle) :=
    Normal.of_algEquiv (IntermediateField.restrict_algEquiv hBle)
  have htop : IntermediateField.restrict hAle ⊔ IntermediateField.restrict hBle = ⊤ := by
    rw [← (IntermediateField.lift_injective (A ⊔ B)).eq_iff, IntermediateField.lift_top,
      IntermediateField.lift_sup, IntermediateField.lift_restrict, IntermediateField.lift_restrict]
  refine splitsCompletely_of_sup_eq_top _ _ htop hp ?_ ?_
  · exact splitsCompletely_of_algEquiv (IntermediateField.restrict_algEquiv hAle).symm hp hA
  · exact splitsCompletely_of_algEquiv (IntermediateField.restrict_algEquiv hBle).symm hp hB

end InverseGalois.CFT
