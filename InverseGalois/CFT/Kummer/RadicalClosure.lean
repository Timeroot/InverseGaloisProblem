/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Enlarging a finite extension until it contains prescribed radicals

Inside an algebraic closure of a field, a finite extension can always be enlarged to a finite
*normal* extension containing an `n`-th root of each of finitely many prescribed elements: adjoin
the roots, which exist because the ambient field is algebraically closed and are algebraic over the
base because the ambient field is algebraic over it, and then pass to the normal closure, which is
again finite.

This is the move that turns a coboundary condition in the multiplicative group of a number field
into a condition with values in the roots of unity.  Hilbert's theorem 90 presents a locally trivial
class by an element whose conjugates differ from it by `n`-th powers; over a field containing an
`n`-th root of that element the cocycle becomes a cocycle of `n`-th roots of unity, and the field
provided here is where that happens.

## Main results

* `InverseGalois.CFT.exists_normal_intermediateField_forall_pow_eq`: **a finite extension inside an
  algebraic closure is contained in a finite normal extension containing an `n`-th root of each of
  finitely many prescribed elements.**
* `InverseGalois.CFT.exists_isGalois_intermediateField_forall_pow_eq`: in characteristic zero the
  enlargement is Galois.
* `InverseGalois.CFT.exists_numberField_intermediateField_forall_pow_eq`: the same statement for
  number fields inside a fixed algebraic closure of the rationals.

## Tags

normal closure, radical extension, Kummer theory, algebraic closure, number field
-/

namespace InverseGalois.CFT

section Radical

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **A finite extension inside an algebraic closure is contained in a finite normal extension
containing an `n`-th root of each of finitely many prescribed elements.**  The roots exist in the
algebraic closure and are algebraic over the base, so adjoining them keeps the extension finite;
the normal closure of the result is still finite. -/
theorem exists_normal_intermediateField_forall_pow_eq {ι : Type*} [Finite ι]
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] (β : ι → Ω) {n : ℕ} (hn : n ≠ 0) :
    ∃ M : IntermediateField k Ω, K ≤ M ∧ FiniteDimensional k ↥M ∧ Normal k ↥M ∧
      ∀ i, ∃ α ∈ M, α ^ n = β i := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  choose α hα using fun i => IsAlgClosed.exists_pow_nat_eq (β i) (Nat.pos_of_ne_zero hn)
  haveI : ∀ i, FiniteDimensional k ↥(IntermediateField.adjoin k {α i}) := fun i =>
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (α i))
  set L : IntermediateField k Ω := K ⊔ ⨆ i, IntermediateField.adjoin k {α i} with hL
  haveI : FiniteDimensional k ↥L := inferInstance
  have hmem : ∀ i, α i ∈ L := fun i =>
    (le_sup_right.trans' (le_iSup (fun i => IntermediateField.adjoin k {α i}) i) :
      IntermediateField.adjoin k {α i} ≤ L) (IntermediateField.subset_adjoin k {α i} rfl)
  refine ⟨IntermediateField.normalClosure k L Ω,
    le_trans le_sup_left (IntermediateField.le_normalClosure L),
    inferInstance, inferInstance, fun i => ⟨α i, IntermediateField.le_normalClosure L (hmem i),
      hα i⟩⟩

/-- **In characteristic zero the enlargement containing the prescribed radicals is Galois.** -/
theorem exists_isGalois_intermediateField_forall_pow_eq [CharZero k] {ι : Type*} [Finite ι]
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] (β : ι → Ω) {n : ℕ} (hn : n ≠ 0) :
    ∃ M : IntermediateField k Ω, K ≤ M ∧ FiniteDimensional k ↥M ∧ IsGalois k ↥M ∧
      ∀ i, ∃ α ∈ M, α ^ n = β i := by
  obtain ⟨M, hKM, hfin, hnor, hroot⟩ :=
    exists_normal_intermediateField_forall_pow_eq K β hn
  exact ⟨M, hKM, hfin, { __ := hnor }, hroot⟩

end Radical

section NumberFieldCase

/-- **A number field inside a fixed algebraic closure of the rationals is contained in a number
field, Galois over the rationals, which contains an `n`-th root of each of finitely many prescribed
elements.** -/
theorem exists_numberField_intermediateField_forall_pow_eq {ι : Type*} [Finite ι]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥K]
    (β : ι → AlgebraicClosure ℚ) {n : ℕ} (hn : n ≠ 0) :
    ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), K ≤ M ∧ NumberField ↥M ∧ IsGalois ℚ ↥M ∧
      ∀ i, ∃ α ∈ M, α ^ n = β i := by
  haveI : FiniteDimensional ℚ ↥K := NumberField.to_finiteDimensional
  obtain ⟨M, hKM, hfin, hgal, hroot⟩ :=
    exists_isGalois_intermediateField_forall_pow_eq K β hn
  exact ⟨M, hKM, { to_charZero := inferInstance, to_finiteDimensional := hfin }, hgal, hroot⟩

end NumberFieldCase

end InverseGalois.CFT
