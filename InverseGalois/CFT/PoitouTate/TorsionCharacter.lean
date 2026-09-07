/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.RelativeTorsion

/-!
# Characters with values in the roots of unity of a prime order

The elements of the rationals modulo the integers killed by a prime `n` form a cyclic group of
order `n`: they are the multiples of the reciprocal of `n`, and the integers modulo `n` are a
field, so any one of them other than the identity generates all of them.

Two characters of a group with values in that cyclic group are therefore proportional as soon as
the first is trivial wherever the second is.  This is what makes a prescription of local
conditions insensitive to the ambiguity in a Frobenius automorphism: a Frobenius automorphism is
only ever pinned down up to an invertible power, and raising a character to an invertible power
does not change where it is trivial.

## Main results

* `InverseGalois.CFT.mem_zpowers_of_pow_eq_one`: **the elements killed by a prime are the powers
  of any one of them other than the identity.**
* `InverseGalois.CFT.exists_zpow_eq_of_forall_eq_one`: **two characters killed by a prime, the
  first trivial wherever the second is, are proportional.**
* `InverseGalois.CFT.not_dvd_of_zpow_eq_ne_one`: the exponent of proportionality is prime to the
  order as soon as one of the powers taken is non-trivial.

## Tags

character, root of unity, cyclic group, Frobenius, class field theory
-/

namespace InverseGalois.CFT

/-! ### The torsion of the rationals modulo the integers is cyclic -/

section Torsion

variable {n : ℕ} [NeZero n]

/-- An element of the rationals modulo the integers killed by `n`, read multiplicatively, is a
multiple of the reciprocal of `n`. -/
theorem exists_zmodQModZ_eq_of_pow_eq_one {x : Multiplicative QModZ} (hx : x ^ n = 1) :
    ∃ c : ZMod n, Multiplicative.ofAdd (zmodQModZ n c) = x := by
  obtain ⟨c, hc⟩ := (mem_nsmulTorsionQModZ_iff_exists n).1
    (show Multiplicative.toAdd x ∈ nsmulTorsionQModZ n from (pow_eq_one_iff_nsmul_toAdd x n).1 hx)
  exact ⟨c, by rw [hc]; rfl⟩

/-- **The elements of the rationals modulo the integers killed by a prime are the powers of any
one of them other than the identity.**  They are the multiples of the reciprocal of the prime, and
the integers modulo a prime are a field, in which every element other than zero is invertible. -/
theorem mem_zpowers_of_pow_eq_one (hn : n.Prime) {t x : Multiplicative QModZ} (ht : t ^ n = 1)
    (ht1 : t ≠ 1) (hx : x ^ n = 1) : x ∈ Subgroup.zpowers t := by
  haveI : Fact n.Prime := ⟨hn⟩
  obtain ⟨c, hc⟩ := exists_zmodQModZ_eq_of_pow_eq_one ht
  obtain ⟨d, hd⟩ := exists_zmodQModZ_eq_of_pow_eq_one hx
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ht1 (by rw [← hc, map_zero]; rfl)
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (d * c⁻¹)
  have hkc : k • c = d := by
    rw [zsmul_eq_mul, hk, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← hc, ← hd, ← ofAdd_zsmul, ← map_zsmul, hkc]⟩

end Torsion

/-! ### Proportionality of two characters -/

section Character

variable {n : ℕ} [NeZero n] {G : Type*} [Group G]

/-- **Two characters of a group with values in the elements of the rationals modulo the integers
killed by a prime, the first trivial wherever the second is, are proportional.**  If the second is
trivial then so is the first; otherwise the second takes a value other than the identity, whose
powers are all the values in sight, and the exponent matching the two characters there matches
them everywhere, because the quotient of the first by that power of the second is a character
trivial on the kernel of the second and at the chosen point, hence everywhere. -/
theorem exists_zpow_eq_of_forall_eq_one (hn : n.Prime) (f g : G →* Multiplicative QModZ)
    (hf : ∀ x, f x ^ n = 1) (hg : ∀ x, g x ^ n = 1) (hker : ∀ x, g x = 1 → f x = 1) :
    ∃ j : ℤ, ∀ x, f x = g x ^ j := by
  by_cases hg1 : ∀ x, g x = 1
  · exact ⟨0, fun x => by rw [hg1 x, one_zpow]; exact hker x (hg1 x)⟩
  push_neg at hg1
  obtain ⟨x₀, hx₀⟩ := hg1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_pow_eq_one hn (hg x₀) hx₀ (hf x₀))
  refine ⟨j, fun x => ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_pow_eq_one hn (hg x₀) hx₀ (hg x))
  have hgx : g (x * (x₀ ^ m)⁻¹) = 1 := by
    rw [_root_.map_mul, _root_.map_inv, map_zpow, hm, mul_inv_cancel]
  have hfx := hker _ hgx
  rw [_root_.map_mul, _root_.map_inv, mul_inv_eq_one] at hfx
  rw [hfx, map_zpow, ← hj, ← hm, ← zpow_mul, ← zpow_mul, mul_comm]

omit [NeZero n] in
/-- The exponent matching two characters is prime to the order as soon as one of the powers taken
is non-trivial, since a power of the order kills every value. -/
theorem not_dvd_of_zpow_eq_ne_one {g : G →* Multiplicative QModZ} (hg : ∀ x, g x ^ n = 1) {j : ℤ}
    {x : G} (hx : g x ^ j ≠ 1) : ¬ (n : ℤ) ∣ j := by
  rintro ⟨m, rfl⟩
  exact hx (by rw [zpow_mul, zpow_natCast, hg x, one_zpow])

end Character

end InverseGalois.CFT
