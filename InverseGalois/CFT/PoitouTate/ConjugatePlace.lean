/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.RecursionStep
import InverseGalois.CFT.Units.IdeleNormTower

/-!
# The conjugates of a completely split place

A place of a Galois extension of number fields whose decomposition group is trivial lies above a
place of every intermediate field whose decomposition group is again trivial, and the same is true
of all its conjugates.  Both statements are needed to run a recursion that adds one completely
split place at a time and prescribes local data at all of its conjugates: the prescription is
indexed by the places of the intermediate field, while the splitting condition is read at the top.

The proof of the first statement compares two places of the top field above the same place of the
intermediate field.  An automorphism of the intermediate field fixing the place below lifts to the
top field, and the lift moves the given place to another place above the same one; an automorphism
over the intermediate field carries it back, and the composite fixes the given place, hence is
trivial.  The lift is therefore inverse to an automorphism over the intermediate field, so it
restricts to the identity.

## Main results

* `InverseGalois.CFT.stabilizer_primeUnder_eq_bot`: **a place with trivial decomposition group over
  the base lies above a place of an intermediate field with trivial decomposition group.**
* `InverseGalois.CFT.exists_primeUnder_eq_smul_stabilizer_eq_bot`: **every conjugate of the place
  below a completely split place is again the place below a completely split place.**

## Tags

number field, place, decomposition group, completely split, conjugate, tower
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### A completely split place along a tower -/

section Tower

variable {k K L : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Field L]
  [NumberField L] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
  [IsGalois k K] [IsGalois K L] [IsGalois k L]

omit [NumberField k] in
/-- **A place with trivial decomposition group over the base lies above a place of an intermediate
field with trivial decomposition group.**  An automorphism of the intermediate field fixing the
place below lifts to the top field, and its lift is inverse to an automorphism over the
intermediate field, hence restricts to the identity. -/
theorem stabilizer_primeUnder_eq_bot {V : HeightOneSpectrum (𝓞 L)}
    (h : stabilizer Gal(L/k) V = ⊥) : stabilizer Gal(K/k) (primeUnder (𝓞 K) V) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => ?_
  obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (E := L) τ
  have h1 : primeUnder (𝓞 K) (τ' • V) = primeUnder (𝓞 K) V := by
    rw [primeUnder_smul K τ' V]
    exact hτ
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_primeUnder_eq (A := 𝓞 K) (G := Gal(L/K)) h1
  have h2 : (ρ.restrictScalars k * τ') • V = V := by
    rw [mul_smul, smul_restrictScalars_place k ρ (τ' • V)]
    exact hρ
  have h3 : ρ.restrictScalars k * τ' = 1 := (Subgroup.eq_bot_iff_forall _).1 h _ h2
  rw [eq_inv_of_mul_eq_one_right h3, _root_.map_inv, restrictNormalHom_restrictScalars k K ρ,
    inv_one]

omit [NumberField k] [NumberField K] [IsGalois K L] in
/-- **Every conjugate of the place below a completely split place is again the place below a
completely split place.**  A lift of the automorphism moves the place upstairs, and conjugation
carries the trivial decomposition group to a trivial one. -/
theorem exists_primeUnder_eq_smul_stabilizer_eq_bot {V : HeightOneSpectrum (𝓞 L)}
    (h : stabilizer Gal(L/k) V = ⊥) (τ : Gal(K/k)) :
    ∃ W : HeightOneSpectrum (𝓞 L), primeUnder (𝓞 K) W = τ • primeUnder (𝓞 K) V ∧
      stabilizer Gal(L/k) W = ⊥ := by
  obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (E := L) τ
  refine ⟨τ' • V, primeUnder_smul K τ' V, ?_⟩
  rw [stabilizer_smul_eq_stabilizer_map_conj, h, Subgroup.map_bot]

end Tower

end InverseGalois.CFT
