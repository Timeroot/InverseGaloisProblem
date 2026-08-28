/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNSqrtNegOne
import InverseGalois.CFT.Units.ABHNRamified
import InverseGalois.CFT.Units.ABHNLocalNorm

/-!
# The local conditions of the Albert-Brauer-Hasse-Noether theorem over a field containing a square
root of minus one

Over a Galois extension of the rational numbers containing a square root of minus one, the
Albert-Brauer-Hasse-Noether theorem holds with no condition at the archimedean places at all.  This
file restates the forms in which the ramified finite places are discharged — the values of the
cocycle are local norms for a cyclic decomposition group, they are local powers with exponent the
order of such a group, and the residue characteristic is congruent to one modulo the product of the
two orders — for that base.

For an odd exponent both forms are already available with no hypothesis at infinity, oddness itself
supplying it.  What is new here is the even case: no parity condition on the exponent is imposed,
only the presence of a square root of minus one in the extension.

## Main results

* `InverseGalois.CFT.exists_isMulCoboundary_of_sq_eq_neg_one_of_forall_exists_norm`: **over a
  Galois extension of the rational numbers containing a square root of minus one, a two-cocycle
  with values in the units of the rational numbers is a coboundary as soon as at every ramified
  finite place its values are local norms for a cyclic decomposition group.**
* `InverseGalois.CFT.exists_isMulCoboundary_of_sq_eq_neg_one_of_forall_exists_pow`: the same
  conclusion from the stronger hypothesis that the values are local powers with exponent the order
  of a cyclic decomposition group.
* `InverseGalois.CFT.exists_isMulCoboundary_of_sq_eq_neg_one_of_forall_ramified_primeResidue`: the
  same conclusion from a congruence on the residue characteristic at every ramified finite place
  with prime residue field.

## Tags

number field, Albert-Brauer-Hasse-Noether, decomposition group, coboundary, square root of minus one
-/

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

variable {K : Type} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K]

/-- **Over a Galois extension of the rational numbers containing a square root of minus one, a
two-cocycle with values in the units of the rational numbers is a coboundary as soon as at every
ramified finite place its values are local norms for a cyclic decomposition group.**  No condition
is imposed at the archimedean places, and none on the parity of the exponent which kills the
cocycle. -/
theorem exists_isMulCoboundary_of_sq_eq_neg_one_of_forall_exists_norm {ι : K} (hι : ι ^ 2 = -1)
    {n : ℕ} (hn : n ≠ 0) {a : Gal(K/ℚ) → Gal(K/ℚ) → ℚˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/ℚ), a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal →
      ∃ g : ↥(stabilizer Gal(K/ℚ) v), (∀ x : ↥(stabilizer Gal(K/ℚ) v), x ∈ Subgroup.zpowers g) ∧
        ∀ z : ℚˣ, z ^ n = 1 → ∃ y : (v.adicCompletion K)ˣ,
          ∏ᶠ σ : ↥(stabilizer Gal(K/ℚ) v), σ • (y : v.adicCompletion K)
            = ((adicUnitHom v (Units.map (algebraMap ℚ K : ℚ →* K) z) : (v.adicCompletion K)ˣ) :
                v.adicCompletion K)) :
    ∃ b : Gal(K/ℚ) → Kˣ, ∀ x y : Gal(K/ℚ),
      x • b y / b (x * y) * b x = Units.map (algebraMap ℚ K : ℚ →* K) (a x y) := by
  refine exists_isMulCoboundary_of_sq_eq_neg_one hι hn hpow ha fun v hv => ?_
  obtain ⟨g, hg, hnorm⟩ := hram v hv
  exact exists_sub_add_eq_adicUnits_of_exists_norm (k := ℚ) v hg hpow ha hnorm

/-- **Over a Galois extension of the rational numbers containing a square root of minus one, a
two-cocycle with values in the units of the rational numbers is a coboundary as soon as at every
ramified finite place its values are local powers with exponent the order of a cyclic decomposition
group.**  No condition is imposed at the archimedean places, and none on the parity of the exponent
which kills the cocycle. -/
theorem exists_isMulCoboundary_of_sq_eq_neg_one_of_forall_exists_pow {ι : K} (hι : ι ^ 2 = -1)
    {n : ℕ} (hn : n ≠ 0) {a : Gal(K/ℚ) → Gal(K/ℚ) → ℚˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/ℚ), a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal →
      ∃ g : ↥(stabilizer Gal(K/ℚ) v), (∀ x : ↥(stabilizer Gal(K/ℚ) v), x ∈ Subgroup.zpowers g) ∧
        ∀ z : ℚˣ, z ^ n = 1 → ∃ y : (v.adicCompletion K)ˣ,
          (∀ σ : ↥(stabilizer Gal(K/ℚ) v), σ • (y : v.adicCompletion K) = y) ∧
            y ^ Nat.card ↥(stabilizer Gal(K/ℚ) v)
              = adicUnitHom v (Units.map (algebraMap ℚ K : ℚ →* K) z)) :
    ∃ b : Gal(K/ℚ) → Kˣ, ∀ x y : Gal(K/ℚ),
      x • b y / b (x * y) * b x = Units.map (algebraMap ℚ K : ℚ →* K) (a x y) := by
  refine exists_isMulCoboundary_of_sq_eq_neg_one hι hn hpow ha fun v hv => ?_
  obtain ⟨g, hg, hroot⟩ := hram v hv
  exact exists_sub_add_eq_adicUnits_of_exists_pow (k := ℚ) v hg hpow ha hroot

/-- **Over a Galois extension of the rational numbers containing a square root of minus one, a
two-cocycle with values in the units of the rational numbers is a coboundary as soon as every
ramified finite place has cyclic decomposition group, prime residue field and residue
characteristic congruent to one modulo the product of the order of the cocycle and the order of
that group.** -/
theorem exists_isMulCoboundary_of_sq_eq_neg_one_of_forall_ramified_primeResidue {ι : K}
    (hι : ι ^ 2 = -1) {n : ℕ} (hn : n ≠ 0) {a : Gal(K/ℚ) → Gal(K/ℚ) → ℚˣ}
    (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/ℚ), a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal →
      IsCyclic ↥(stabilizer Gal(K/ℚ) v) ∧ ∃ p e : ℕ,
        HasResidueChar (v.adicCompletion K) p e ∧
          (∀ x : v.adicCompletion K, Valued.v x ≤ 1 →
            ∃ b : ℤ, Valued.v (x - (b : v.adicCompletion K)) < 1) ∧
          n * Nat.card ↥(stabilizer Gal(K/ℚ) v) ∣ p - 1) :
    ∃ b : Gal(K/ℚ) → Kˣ, ∀ x y : Gal(K/ℚ),
      x • b y / b (x * y) * b x = Units.map (algebraMap ℚ K : ℚ →* K) (a x y) := by
  refine exists_isMulCoboundary_of_sq_eq_neg_one_of_forall_exists_pow hι hn hpow ha fun v hv => ?_
  obtain ⟨hcyc, p, e, h, hres, hnd⟩ := hram v hv
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(stabilizer Gal(K/ℚ) v))
  exact ⟨g, hg, fun z hz => exists_pow_eq_adicUnitHom_of_mul_dvd (k := ℚ) v h hres hnd z hz⟩

end InverseGalois.CFT
