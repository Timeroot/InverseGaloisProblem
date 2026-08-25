/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNLocalPower
import InverseGalois.CFT.Local.PrimeResidue

/-!
# The local condition at a ramified place with prime residue field

The Albert-Brauer-Hasse-Noether theorem leaves, for a two-cocycle with values in the roots of unity
of the base field, one condition at each ramified finite place: there each value must be, in the
completion, a power with exponent the order of the decomposition group of an element that group
fixes.  When the residue field at the place is the prime field, that condition is a congruence in
the multiplicative group of the prime field, and it holds as soon as the residue characteristic is
congruent to one modulo the product of the order of the cocycle and the order of the decomposition
group.

This is exactly the arithmetic that the Scholz-Reichardt construction arranges: the places that
ramify are chosen with residue characteristic congruent to one modulo a large power of the prime,
and they split completely in the base, so their residue fields are prime fields.

## Main results

* `InverseGalois.CFT.exists_pow_eq_adicUnitHom_of_mul_dvd`: **at a finite place with prime residue
  field, a root of unity of the base field is, in the completion, a power with exponent the order
  of the decomposition group of a unit that group fixes**, as soon as the residue characteristic is
  congruent to one modulo the product of the two orders.
* `InverseGalois.CFT.exists_isMulCoboundary_of_odd_of_forall_ramified_primeResidue`: **a two-cocycle
  with values in the roots of unity of the base field and killed by an odd integer is a coboundary,
  as soon as every ramified place has cyclic decomposition group, prime residue field and residue
  characteristic congruent to one modulo the product of the two orders.**

## Tags

number field, Albert-Brauer-Hasse-Noether, decomposition group, prime residue field, coboundary
-/

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

omit [NumberField k] in
/-- **At a finite place with prime residue field, a root of unity of the base field is, in the
completion, a power with exponent the order of the decomposition group of a unit that group
fixes**, as soon as the residue characteristic is congruent to one modulo the product of the order
of the root of unity and the order of the decomposition group.  The decomposition group acts
through valuation preserving automorphisms of the completion, which fix every root of unity of
order prime to the residue characteristic. -/
theorem exists_pow_eq_adicUnitHom_of_mul_dvd (v : HeightOneSpectrum (𝓞 K)) {p e : ℕ}
    (h : HasResidueChar (v.adicCompletion K) p e)
    (hres : ∀ x : v.adicCompletion K, Valued.v x ≤ 1 →
      ∃ b : ℤ, Valued.v (x - (b : v.adicCompletion K)) < 1)
    {n : ℕ} (hnd : n * Nat.card ↥(stabilizer Gal(K/k) v) ∣ p - 1) (z : kˣ) (hz : z ^ n = 1) :
    ∃ y : (v.adicCompletion K)ˣ,
      (∀ σ : ↥(stabilizer Gal(K/k) v), σ • (y : v.adicCompletion K) = y) ∧
        y ^ Nat.card ↥(stabilizer Gal(K/k) v)
          = adicUnitHom v (Units.map (algebraMap k K : k →* K) z) := by
  have hζ : (adicUnitHom v (Units.map (algebraMap k K : k →* K) z)) ^ n = 1 := by
    rw [← map_pow, ← map_pow, hz, map_one, map_one]
  obtain ⟨y, hy, hfix⟩ := exists_pow_eq_and_map_eq_self_of_mul_dvd h hres hnd hζ
  refine ⟨y, fun σ => ?_, hy⟩
  rw [stabilizer_smul_adicCompletion_def]
  exact hfix (adicCompletionAut v σ.1 (mem_stabilizer_iff.mp σ.2))
    (valued_adicCompletionAut v σ.1 (mem_stabilizer_iff.mp σ.2))

variable [IsGalois k K]

/-- **A two-cocycle with values in the roots of unity of the base field and killed by an odd
integer is a coboundary, as soon as every ramified place has cyclic decomposition group, prime
residue field and residue characteristic congruent to one modulo the product of the order of the
cocycle and the order of that group.** -/
theorem exists_isMulCoboundary_of_odd_of_forall_ramified_primeResidue {n : ℕ} (hn : Odd n)
    {a : Gal(K/k) → Gal(K/k) → kˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal →
      IsCyclic ↥(stabilizer Gal(K/k) v) ∧ ∃ p e : ℕ,
        HasResidueChar (v.adicCompletion K) p e ∧
          (∀ x : v.adicCompletion K, Valued.v x ≤ 1 →
            ∃ b : ℤ, Valued.v (x - (b : v.adicCompletion K)) < 1) ∧
          n * Nat.card ↥(stabilizer Gal(K/k) v) ∣ p - 1) :
    ∃ b : Gal(K/k) → Kˣ, ∀ x y : Gal(K/k),
      x • b y / b (x * y) * b x = Units.map (algebraMap k K : k →* K) (a x y) := by
  refine exists_isMulCoboundary_of_odd_of_forall_exists_pow hn hpow ha fun v hv => ?_
  obtain ⟨hcyc, p, e, h, hres, hnd⟩ := hram v hv
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(stabilizer Gal(K/k) v))
  exact ⟨g, hg, fun z hz => exists_pow_eq_adicUnitHom_of_mul_dvd v h hres hnd z hz⟩

end InverseGalois.CFT
