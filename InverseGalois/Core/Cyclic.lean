/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Core.Basic

/-!
# Cyclic Groups are Inverse Galois Groups

We show that every finite cyclic group is an inverse Galois group over `ℚ`.

## Strategy

1. The Galois group of the `n`-th cyclotomic extension `ℚ(ζₙ)/ℚ` is `(ℤ/nℤ)ˣ`, by
   `IsCyclotomicExtension.autEquivPow` together with the irreducibility of the cyclotomic
   polynomial over `ℚ`.
2. The inverse Galois property is closed under quotients (`IsInverseGalois.of_surjective`).
3. Every finite cyclic group is (isomorphic to) a quotient of `(ℤ/mℤ)ˣ` for a suitable `m`
   (a consequence of Dirichlet's theorem on primes in arithmetic progressions).

## Main results

* `IsInverseGalois.units_zmod`: `(ℤ/nℤ)ˣ` is an inverse Galois group for all `n ≥ 1`.
* `IsInverseGalois.of_isCyclic`: Every finite cyclic group is an inverse Galois group.
-/

open Polynomial IntermediateField IsCyclotomicExtension

noncomputable section

/-- `(ℤ/nℤ)ˣ` is an inverse Galois group, realized by the `n`-th cyclotomic field `ℚ(ζₙ)`. -/
theorem IsInverseGalois.units_zmod (n : ℕ) [NeZero n] : IsInverseGalois (ZMod n)ˣ := by
  let L := CyclotomicField n ℚ
  have : IsCyclotomicExtension {n} ℚ L := CyclotomicField.isCyclotomicExtension n ℚ
  have hirr : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat (NeZero.pos n)
  exact ⟨L, inferInstance, inferInstance, inferInstance, isGalois {n} ℚ L, ⟨autEquivPow L hirr⟩⟩

/-
**Consequence of Dirichlet's theorem on primes in arithmetic progressions.**
For every `n ≥ 1`, there exists `m ≥ 1` and a surjective group homomorphism `(ℤ/mℤ)ˣ →* ℤ/nℤ`.

This follows from Dirichlet's theorem: there exists a prime `p ≡ 1 (mod n)`, so that
`(ℤ/pℤ)ˣ ≅ ℤ/(p-1)ℤ` surjects onto `ℤ/nℤ` since `n ∣ (p-1)`.
-/
theorem ZMod.exists_units_surjection (n : ℕ) [NeZero n] :
    ∃ (m : ℕ) (_ : NeZero m) (f : (ZMod m)ˣ →* Multiplicative (ZMod n)),
      Function.Surjective f := by
  -- By Dirichlet's theorem, there exists a prime `p` such that `p ≡ 1 (mod n)`.
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ≡ 1 [MOD n] ∧ n < p :=
    Exists.imp (by tauto) (Nat.exists_prime_gt_modEq_one n (NeZero.ne n))
  -- Since `p` is prime, `(ZMod p)ˣ` is cyclic and has cardinality `p-1`, hence `zmodCyclicMulEquiv` gives an equivalence with `Multiplicative (ZMod (p-1))`.
  let e : (ZMod p)ˣ ≃* Multiplicative (ZMod (p - 1)) := by
    have := Fact.mk hp.1
    have h_card : Nat.card (ZMod p)ˣ = p - 1 := by simp [Nat.totient_prime hp.1]
    rw [← h_card]
    exact (zmodCyclicMulEquiv inferInstance).symm
  -- Since `n ∣ p - 1`, reduction modulo `n` gives the required quotient map.
  have h_div : n ∣ p - 1 := by
    rw [← Int.natCast_dvd_natCast]
    simpa [Nat.cast_sub hp.1.pos] using hp.2.1.symm.dvd
  let f : Multiplicative (ZMod (p - 1)) →* Multiplicative (ZMod n) :=
    (ZMod.castHom h_div (ZMod n)).toAddMonoidHom.toMultiplicative
  have hf : Function.Surjective f := ZMod.castHom_surjective h_div
  exact ⟨p, ⟨hp.1.ne_zero⟩, f.comp e.toMonoidHom, hf.comp e.surjective⟩

/-- Every finite cyclic group is an inverse Galois group over `ℚ`. -/
theorem IsInverseGalois.multiplicative_zmod (n : ℕ) [NeZero n] :
    IsInverseGalois (Multiplicative (ZMod n)) := by
  obtain ⟨m, hm, f, hf⟩ := ZMod.exists_units_surjection n
  exact (IsInverseGalois.units_zmod m).of_surjective f hf

/-- Every finite cyclic group is an inverse Galois group over `ℚ`. -/
theorem IsInverseGalois.of_isCyclic (G : Type*) [Group G] [Finite G] [IsCyclic G] :
    IsInverseGalois G := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  exact (IsInverseGalois.multiplicative_zmod (Nat.card G)).of_mulEquiv
    (zmodCyclicMulEquiv inferInstance)

end