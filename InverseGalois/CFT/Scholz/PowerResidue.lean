/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The power residue character of a prime congruent to one

Modulo a prime `q` congruent to one modulo `ℓ` the `ℓ`-th powers form a subgroup of index `ℓ` in
the units, so the quotient carries a surjection onto a cyclic group of order `ℓ`.  Since the unit
group is cyclic of order `q - 1`, that surjection is nothing but reduction of the discrete
logarithm modulo `ℓ`, and a unit lies in its kernel exactly when its `(q - 1) / ℓ`-th power is one,
the usual power residue criterion.

The resulting homomorphism is the bookkeeping device of the residue-degree correction of the
Scholz–Reichardt construction: it turns the multiplicative question "is this integer an `ℓ`-th
power modulo `q`" into an `𝔽_ℓ`-linear one.

## Main results

* `InverseGalois.CFT.exists_powerResidueHom`: **the units modulo a prime congruent to one modulo
  `ℓ` carry a surjection onto a cyclic group of order `ℓ` whose kernel is the set of `ℓ`-th power
  residues.**

## Tags

power residue, cyclic group, discrete logarithm, finite field
-/

namespace InverseGalois.CFT

variable {ℓ q : ℕ}

/-- Divisibility of a discrete logarithm by `ℓ` read through the two descriptions of the kernel. -/
theorem nsmul_eq_zero_iff_castHom_eq_zero {n k : ℕ} [NeZero n] (hn : n = ℓ * k) (hk : k ≠ 0)
    (hdvd : ℓ ∣ n) (b : ZMod n) :
    k • b = 0 ↔ ZMod.castHom hdvd (ZMod ℓ) b = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, b = (m : ZMod n) :=
    ⟨b.val, by rw [ZMod.natCast_val, ZMod.cast_id]⟩
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, map_natCast,
    ZMod.natCast_eq_zero_iff, hn, mul_comm ℓ k]
  exact mul_dvd_mul_iff_left hk

/-- **The units modulo a prime congruent to one modulo `ℓ` surject onto a cyclic group of order
`ℓ` with the `ℓ`-th power residues as kernel.**  The unit group is cyclic of order `q - 1`, so it
is the additive group of `ZMod (q - 1)` in multiplicative dress, and the surjection is reduction
modulo `ℓ`; a discrete logarithm is divisible by `ℓ` exactly when the `(q - 1) / ℓ`-th power of the
unit is one. -/
theorem exists_powerResidueHom (hℓ : ℓ.Prime) (hq : q.Prime) (hdvd : ℓ ∣ q - 1) :
    ∃ κ : (ZMod q)ˣ →* Multiplicative (ZMod ℓ), Function.Surjective κ ∧
      ∀ x : (ZMod q)ˣ, κ x = 1 ↔ (x : ZMod q) ^ ((q - 1) / ℓ) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hle : ℓ ≤ q - 1 := Nat.le_of_dvd (by omega) hdvd
  set k : ℕ := (q - 1) / ℓ with hkdef
  have hq1 : q - 1 = ℓ * k := (Nat.mul_div_cancel' hdvd).symm
  have hk : k ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hq1
    omega
  have hcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hq]
  haveI : NeZero (Nat.card (ZMod q)ˣ) := ⟨by rw [hcard]; omega⟩
  have hdvd' : ℓ ∣ Nat.card (ZMod q)ˣ := hcard ▸ hdvd
  set E : Multiplicative (ZMod (Nat.card (ZMod q)ˣ)) ≃* (ZMod q)ˣ :=
    zmodCyclicMulEquiv inferInstance with hE
  refine ⟨((ZMod.castHom hdvd' (ZMod ℓ)).toAddMonoidHom.toMultiplicative).comp
    E.symm.toMonoidHom, ?_, ?_⟩
  · intro y
    obtain ⟨b, hb⟩ := ZMod.castHom_surjective (m := ℓ) hdvd' (Multiplicative.toAdd y)
    exact ⟨E (Multiplicative.ofAdd b), by simp [hb]⟩
  · intro x
    have hu : (x : ZMod q) ^ k = 1 ↔ x ^ k = 1 := by
      rw [← Units.val_pow_eq_pow_val, Units.val_eq_one]
    have hv : x ^ k = 1 ↔ k • (Multiplicative.toAdd (E.symm x)) = 0 := by
      rw [← map_eq_one_iff E.symm E.symm.injective, map_pow, ← toAdd_eq_zero, toAdd_pow]
    rw [hu, hv,
      nsmul_eq_zero_iff_castHom_eq_zero (hcard.trans hq1) hk hdvd']
    simp [ofAdd_eq_one]

end InverseGalois.CFT
