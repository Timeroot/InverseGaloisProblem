/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.Corestriction

/-!
# Detecting vanishing of cohomology on subgroups of prime-power index complement

The cohomology of a finite group in positive degree is annihilated by the order of the group.
Restriction to a subgroup, followed by corestriction, is multiplication by the index, so a class
whose restriction to a subgroup vanishes is annihilated by that index.

Combining the two, a class that restricts to zero on a subgroup of index prime to `p`, for every
prime `p` dividing the order of the group, is annihilated by numbers whose greatest common divisor
keeps dropping, and hence is zero.  In practice the subgroups used are the Sylow subgroups.

## Main results

* `InverseGalois.CFT.gcd_nsmul_eq_zero`: an element annihilated by two natural numbers is
  annihilated by their greatest common divisor.
* `InverseGalois.CFT.eq_zero_of_forall_prime_res`: **a positive-degree cohomology class of a finite
  group vanishes as soon as, for every prime dividing the order of the group, it restricts to zero
  on some subgroup of index prime to that prime.**

## Tags

group cohomology, restriction, corestriction, Sylow subgroup, torsion
-/

universe u

open CategoryTheory groupCohomology

namespace InverseGalois.CFT

section Gcd

/-- An element of an abelian group annihilated by two natural numbers is annihilated by their
greatest common divisor. -/
theorem gcd_nsmul_eq_zero {M : Type*} [AddCommGroup M] {a b : ℕ} {x : M}
    (ha : a • x = 0) (hb : b • x = 0) : Nat.gcd a b • x = 0 := by
  have key : ((Nat.gcd a b : ℕ) : ℤ) • x = 0 := by
    rw [Nat.gcd_eq_gcd_ab, add_zsmul, mul_comm (a : ℤ), mul_comm (b : ℤ), mul_zsmul, mul_zsmul,
      natCast_zsmul, natCast_zsmul, ha, hb, smul_zero, smul_zero, add_zero]
  rwa [natCast_zsmul] at key

end Gcd

section Reduction

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G)

/-- **A positive-degree cohomology class of a finite group vanishes as soon as, for every prime
dividing the order of the group, it restricts to zero on some subgroup whose index is prime to that
prime.**  Taking the Sylow subgroups gives the usual reduction of the vanishing of cohomology to the
vanishing on the Sylow subgroups. -/
theorem eq_zero_of_forall_prime_res {n : ℕ} (x : groupCohomology A (n + 1))
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card G →
      ∃ S : Subgroup G, ¬ p ∣ S.index ∧ res S A (n + 1) x = 0) : x = 0 := by
  suffices H : ∀ m : ℕ, m ∣ Nat.card G → m • x = 0 → x = 0 from
    H (Nat.card G) dvd_rfl (natCard_nsmul_eq_zero A n x)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hmdvd hm
    rcases eq_or_ne m 1 with rfl | hm1
    · simpa using hm
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by
      rintro rfl
      exact absurd (Nat.eq_zero_of_zero_dvd hmdvd) Nat.card_pos.ne')
    have hp : Nat.Prime m.minFac := Nat.minFac_prime hm1
    obtain ⟨S, hSp, hSres⟩ := h m.minFac hp ((Nat.minFac_dvd m).trans hmdvd)
    have hidx : S.index • x = 0 := index_nsmul_eq_zero_of_res_eq_zero S A (n + 1) x hSres
    have hd : Nat.gcd m S.index • x = 0 := gcd_nsmul_eq_zero hm hidx
    refine ih (Nat.gcd m S.index) ?_ ((Nat.gcd_dvd_left m S.index).trans hmdvd) hd
    refine lt_of_le_of_ne (Nat.le_of_dvd hm0 (Nat.gcd_dvd_left m S.index)) fun hdm => ?_
    exact hSp ((Nat.minFac_dvd m).trans (hdm ▸ Nat.gcd_dvd_right m S.index))

end Reduction

end InverseGalois.CFT
