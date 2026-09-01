/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclotomicFrobenius
import InverseGalois.CFT.Local.ResiduePrimitiveRoot

/-!
# A primitive root generates the Galois group of a cyclotomic field of prime conductor

The Galois group of the cyclotomic field of prime conductor is the group of units of the residues
modulo that prime, so the automorphism raising the roots of unity to the power of a primitive root
has the order of the whole group and generates it.  Every automorphism is then a natural power of
that one, and the exponent is visible on the residues: reading the identity in the group of units
turns it into a congruence between the naming numbers.

That congruence is what connects the two places of the reciprocity computation.  The automorphism
raising the roots of unity to the power of a rational prime away from the conductor is the power of
the chosen generator by an exponent, and that same exponent expresses the rational prime as a power
of the primitive root modulo the conductor — which is the exponent the power residue symbol at the
ramified place measures.

## Main results

* `InverseGalois.CFT.forall_mem_zpowers_cyclotomicPowerAut`: **the automorphism raising the roots
  of unity to the power of a primitive root generates the Galois group.**
* `InverseGalois.CFT.exists_pow_eq_cyclotomicPowerAut`: every automorphism naming a number prime to
  the conductor is a natural power of that generator.
* `InverseGalois.CFT.natCast_zmod_eq_pow_of_cyclotomicPowerAut_eq_pow`: **the exponent expressing
  one such automorphism as a power of another expresses the first number as a power of the second
  modulo the conductor.**
* `InverseGalois.CFT.dvd_sub_pow_of_cyclotomicPowerAut_eq_pow`: the same congruence as a
  divisibility of integers.

## Tags

cyclotomic field, primitive root, Galois group, generator, discrete logarithm, reciprocity
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open NumberField

/-! ### The generator named by a primitive root -/

section Generator

variable (q : ℕ) [NeZero q] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {q} ℚ K]

/-- **The automorphism raising the roots of unity to the power of a primitive root generates the
Galois group** of a cyclotomic field of prime conductor.  The Galois group is the group of units of
the residues modulo the conductor, and the unit named by a primitive root has the order of that
group. -/
theorem forall_mem_zpowers_cyclotomicPowerAut (hq : q.Prime) {b : ℕ} (hb : Nat.Coprime b q)
    (hbord : ∀ k : ℕ, q ∣ b ^ k - 1 → (q - 1) ∣ k) (x : Gal(K/ℚ)) :
    x ∈ Subgroup.zpowers (cyclotomicPowerAut q K hb) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {q} ℚ K
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hb
    exact hq.one_lt.ne' hb
  have hcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units q]
  have hord : orderOf (ZMod.unitOfCoprime b hb) = q - 1 := by
    refine Nat.dvd_antisymm ?_ (hbord _ ?_)
    · rw [← hcard]
      exact orderOf_dvd_natCard _
    · have hpow := congrArg Units.val (pow_orderOf_eq_one (ZMod.unitOfCoprime b hb))
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at hpow
      have hk1 : 1 ≤ b ^ orderOf (ZMod.unitOfCoprime b hb) :=
        Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hb0)
      refine (ZMod.natCast_eq_zero_iff _ q).mp ?_
      rw [Nat.cast_sub hk1, Nat.cast_pow, Nat.cast_one, sub_eq_zero]
      exact hpow
  have hinj := orderOf_injective (IsCyclotomicExtension.Rat.galEquivZMod q K).toMonoidHom
    (IsCyclotomicExtension.Rat.galEquivZMod q K).injective (cyclotomicPowerAut q K hb)
  rw [cyclotomicPowerAut] at hinj
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hinj
  have hgcard : Nat.card Gal(K/ℚ) = q - 1 := by
    rw [Nat.card_congr (IsCyclotomicExtension.Rat.galEquivZMod q K).toEquiv, hcard]
  have htop : Subgroup.zpowers (cyclotomicPowerAut q K hb) = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, cyclotomicPowerAut, ← hinj, hord, hgcard]
  rw [htop]
  exact Subgroup.mem_top x

/-- **Every automorphism naming a number prime to the conductor is a natural power of a
generator.** -/
theorem exists_pow_eq_cyclotomicPowerAut {b : ℕ} (hb : Nat.Coprime b q)
    (hgen : ∀ x : Gal(K/ℚ), x ∈ Subgroup.zpowers (cyclotomicPowerAut q K hb)) {p : ℕ}
    (hp : Nat.Coprime p q) :
    ∃ c : ℕ, cyclotomicPowerAut q K hp = cyclotomicPowerAut q K hb ^ c := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {q} ℚ K
  obtain ⟨c, hc⟩ := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_iff_mem_zpowers.mpr (hgen (cyclotomicPowerAut q K hp)))
  exact ⟨c, hc.symm⟩

/-- **The exponent expressing one power automorphism as a power of another expresses the first
number as a power of the second modulo the conductor**, because the Galois group is the group of
units of the residues. -/
theorem natCast_zmod_eq_pow_of_cyclotomicPowerAut_eq_pow {b p : ℕ} (hb : Nat.Coprime b q)
    (hp : Nat.Coprime p q) {c : ℕ}
    (h : cyclotomicPowerAut q K hp = cyclotomicPowerAut q K hb ^ c) :
    ((p : ℕ) : ZMod q) = ((b : ℕ) : ZMod q) ^ c := by
  have hmap := congrArg (IsCyclotomicExtension.Rat.galEquivZMod q K) h
  rw [cyclotomicPowerAut, cyclotomicPowerAut, MulEquiv.apply_symm_apply, map_pow,
    MulEquiv.apply_symm_apply] at hmap
  have hval := congrArg Units.val hmap
  rwa [ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime] at hval

/-- **The congruence between the two naming numbers, as a divisibility of integers.** -/
theorem dvd_sub_pow_of_cyclotomicPowerAut_eq_pow {b p : ℕ} (hb : Nat.Coprime b q)
    (hp : Nat.Coprime p q) {c : ℕ}
    (h : cyclotomicPowerAut q K hp = cyclotomicPowerAut q K hb ^ c) :
    (q : ℤ) ∣ ((p : ℕ) : ℤ) - ((b ^ c : ℕ) : ℤ) := by
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp ?_
  push_cast
  rw [sub_eq_zero]
  exact natCast_zmod_eq_pow_of_cyclotomicPowerAut_eq_pow q K hb hp h

end Generator

end InverseGalois.CFT
