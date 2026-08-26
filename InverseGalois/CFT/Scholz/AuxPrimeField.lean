/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.CyclotomicCompositum
import InverseGalois.CFT.Cyclotomic.Splitting
import InverseGalois.CFT.NilpotentCompositum
import InverseGalois.CFT.Scholz.CompositumTransport
import InverseGalois.CFT.Scholz.ResidueSpan

/-!
# The constraint field of the auxiliary primes

The auxiliary primes of the Scholz–Reichardt residue correction are chosen to split completely in a
constraint field, and the field is chosen so that splitting completely there is exactly the list of
conditions the construction needs.  Adjoining to the field being corrected the roots of unity of
order `ℓ ^ k` produces such a field: its Galois group is nilpotent, being a subgroup of the product
of an `ℓ`-group with an abelian group, it contains the `ℓ`-th roots of unity, and a prime other than
`ℓ` splitting completely in it is congruent to one modulo `ℓ ^ k` and splits completely in the field
being corrected.

Feeding that field to the linear algebra of the power residue vectors gives the statement the
construction actually uses: for a field with `ℓ`-group Galois group, a finite set of primes and a
prescribed vector of power residue symbols, there is a modulus built out of primes of the prescribed
level splitting completely in the field, together with a character of the units modulo that modulus
realising the vector.

## Main results

* `InverseGalois.CFT.exists_modulus_of_isPGroup`: **every prescribed vector of power residue symbols
  is realised by a character of the units modulo a product of primes of level `k` splitting
  completely in a given extension with `ℓ`-group Galois group.**

## Tags

auxiliary prime, power residue symbol, cyclotomic field, nilpotent group, Scholz–Reichardt
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {ℓ : ℕ}

/-- A rational prime splitting completely in a subfield of an ambient field splits completely in
every smaller subfield. -/
theorem splitsCompletely_of_le {L : Type*} [Field L] [CharZero L] {A B : IntermediateField ℚ L}
    (h : A ≤ B) [NumberField ↥A] [NumberField ↥B] {p : ℕ} (hp : p.Prime)
    (hs : SplitsCompletely ↥B p) : SplitsCompletely ↥A p := by
  haveI : NumberField ↥(IntermediateField.restrict h) := ⟨⟩
  exact splitsCompletely_of_ringEquiv (IntermediateField.restrict_algEquiv h).toRingEquiv hp
    (splitsCompletely_intermediateField (IntermediateField.restrict h) hp hs)

variable (B : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥B] [IsGalois ℚ ↥B]

/-- The constraint field of the auxiliary primes: the field being corrected, enlarged by the roots
of unity of order `ℓ ^ k`. -/
noncomputable def auxConstraintField (ℓ k : ℕ) [NeZero (ℓ ^ k)] :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  B ⊔ cycSubfield (ℓ ^ k)

variable {B}

section

variable {k : ℕ} [NeZero (ℓ ^ k)]

instance finiteDimensional_auxConstraintField :
    FiniteDimensional ℚ ↥(auxConstraintField B ℓ k) := by
  unfold auxConstraintField
  infer_instance

instance numberField_auxConstraintField : NumberField ↥(auxConstraintField B ℓ k) := ⟨⟩

instance isGalois_auxConstraintField : IsGalois ℚ ↥(auxConstraintField B ℓ k) := by
  unfold auxConstraintField
  infer_instance

/-- The Galois group of the constraint field is nilpotent: it embeds into the product of an
`ℓ`-group with the abelian Galois group of a cyclotomic field. -/
theorem isNilpotent_auxConstraintField [Fact ℓ.Prime] (hpg : IsPGroup ℓ Gal(↥B/ℚ)) :
    Group.IsNilpotent Gal(↥(auxConstraintField B ℓ k)/ℚ) := by
  have hcyc : Group.IsNilpotent Gal(↥(cycSubfield (ℓ ^ k))/ℚ) :=
    nilpotent_of_mulEquiv
      (IsCyclotomicExtension.Rat.galEquivZMod (ℓ ^ k) ↥(cycSubfield (ℓ ^ k))).symm
  exact isNilpotent_sup B (cycSubfield (ℓ ^ k)) hpg.isNilpotent hcyc

omit [NumberField ↥B] [IsGalois ℚ ↥B] in
/-- The constraint field contains the roots of unity of order `ℓ`. -/
theorem isPrimitiveRoot_mem_auxConstraintField (hk : k ≠ 0) :
    ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ ℓ ∧ ζ ∈ auxConstraintField B ℓ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine ⟨cycRoot (ℓ ^ (j + 1)) ^ ℓ ^ j, ?_, ?_⟩
  · exact IsPrimitiveRoot.pow (NeZero.pos (ℓ ^ (j + 1))) (cycRoot_spec (ℓ ^ (j + 1)))
      (pow_succ ℓ j)
  · refine pow_mem ?_ _
    exact (le_sup_right : cycSubfield (ℓ ^ (j + 1)) ≤ auxConstraintField B ℓ (j + 1))
      (IntermediateField.subset_adjoin ℚ _ rfl)

omit [IsGalois ℚ ↥B] in
/-- A prime other than `ℓ` splitting completely in the constraint field is congruent to one modulo
`ℓ ^ k`. -/
theorem modEq_of_splitsCompletely_auxConstraintField (hℓ : ℓ.Prime) {q : ℕ} (hq : q.Prime)
    (hqℓ : q ≠ ℓ) (hs : SplitsCompletely ↥(auxConstraintField B ℓ k) q) : q ≡ 1 [MOD ℓ ^ k] := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hnd : ¬ q ∣ ℓ ^ k := fun h =>
    hqℓ ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp (hq.dvd_of_dvd_pow h))
  exact modEq_of_splitsCompletely (ℓ ^ k) ↥(cycSubfield (ℓ ^ k)) q hnd
    (splitsCompletely_of_le
      (le_sup_right : cycSubfield (ℓ ^ k) ≤ auxConstraintField B ℓ k) hq hs)

end

/-- **Every prescribed vector of power residue symbols is realised by a character of the units
modulo a product of primes of level `k` splitting completely in a given extension with `ℓ`-group
Galois group.**  Adjoining the roots of unity of order `ℓ ^ k` to that extension produces a
nilpotent extension containing the `ℓ`-th roots of unity, in which a prime other than `ℓ` splits
completely exactly when it is congruent to one modulo `ℓ ^ k` and splits completely in the given
extension. -/
theorem exists_modulus_of_isPGroup [Fact ℓ.Prime] (hodd : Odd ℓ) {k : ℕ} (hk : k ≠ 0)
    (hpg : IsPGroup ℓ Gal(↥B/ℚ)) {S : Finset ℕ} (hSprime : ∀ p ∈ S, p.Prime)
    (t : {p // p ∈ S} → ZMod ℓ) :
    ∃ (Q : ℕ) (κ : (ZMod Q)ˣ →* Multiplicative (ZMod ℓ)), Q ≠ 0 ∧
      (∀ r : ℕ, r.Prime → r ∣ Q →
        r ∉ S ∧ r ≠ ℓ ∧ r ≡ 1 [MOD ℓ ^ k] ∧ SplitsCompletely ↥B r) ∧
      ∀ (p : ℕ) (hp : p ∈ S), powerResidueSymbol κ p = t ⟨p, hp⟩ := by
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero (ℓ ^ k) := ⟨pow_ne_zero k hℓ.ne_zero⟩
  obtain ⟨ζ, hζ, hζA⟩ := isPrimitiveRoot_mem_auxConstraintField (B := B) (ℓ := ℓ) (k := k) hk
  have hdvd : ∀ q : ℕ, q.Prime → q ≠ ℓ →
      SplitsCompletely ↥(auxConstraintField B ℓ k) q → ℓ ∣ q - 1 := by
    intro q hq hqℓ hs
    have hmod := modEq_of_splitsCompletely_auxConstraintField (B := B) hℓ hq hqℓ hs
    exact dvd_trans (dvd_pow_self ℓ hk) ((Nat.modEq_iff_dvd' hq.one_le).mp hmod.symm)
  obtain ⟨Q, κ, hQ0, hQr, hQκ⟩ :=
    exists_modulus_powerResidueSymbol (A := auxConstraintField B ℓ k) hodd
      (isNilpotent_auxConstraintField hpg) hζ hζA hSprime hdvd t
  refine ⟨Q, κ, hQ0, fun r hr hrQ => ?_, hQκ⟩
  obtain ⟨hrS, hrℓ, hrA⟩ := hQr r hr hrQ
  exact ⟨hrS, hrℓ, modEq_of_splitsCompletely_auxConstraintField (B := B) hℓ hr hrℓ hrA,
    splitsCompletely_of_le (le_sup_left : B ≤ auxConstraintField B ℓ k) hr hrA⟩

end InverseGalois.CFT
