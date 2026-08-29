/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Restrict

/-!
# Restriction to a Sylow subgroup is injective on the primary part

Corestriction after restriction is multiplication by the index of the subgroup, so a class killed
by restriction to a subgroup is killed by the index.  A class of the complete cohomology that is
also killed by a power of a prime is therefore killed outright as soon as the index of the subgroup
is prime to that prime, which is exactly the situation of a Sylow subgroup.

This is the mechanism that reduces a statement about the complete cohomology of a finite group to
the same statement for its Sylow subgroups, one prime at a time.

## Main results

* `InverseGalois.CFT.Tate.index_smul_eq_zero_of_tateRes_eq_zero`: **a class killed by restriction
  to a subgroup is killed by the index of that subgroup.**
* `InverseGalois.CFT.Tate.eq_zero_of_tateRes_sylow_eq_zero`: **a class killed by a power of a prime
  and by restriction to a Sylow subgroup for that prime vanishes.**

## Tags

Tate cohomology, restriction, Sylow subgroup, primary component
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### Two coprime multiples -/

/-- **An element killed by two coprime multiples vanishes.** -/
theorem eq_zero_of_coprime_nsmul {M : Type*} [AddCommGroup M] {x : M} {a b : ℕ}
    (ha : a • x = 0) (hb : b • x = 0) (hab : Nat.Coprime a b) : x = 0 := by
  have hg : Nat.gcd a b = 1 := hab
  have h : ((Nat.gcd a b : ℕ) : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := Nat.gcd_eq_gcd_ab a b
  rw [hg, Nat.cast_one] at h
  have hx : (1 : ℤ) • x = 0 := by
    rw [h, add_smul, mul_comm (a : ℤ) (Nat.gcdA a b), mul_comm (b : ℤ) (Nat.gcdB a b), mul_smul,
      mul_smul, natCast_zsmul, natCast_zsmul, ha, hb, smul_zero, smul_zero, add_zero]
  simpa using hx

/-! ### Restriction and the index -/

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **A class killed by restriction to a subgroup is killed by the index of that subgroup.** -/
theorem index_smul_eq_zero_of_tateRes_eq_zero {H : Subgroup G} {A : Rep k G} {n : ℤ}
    {x : tateModule A n} (hx : tateRes H A n x = 0) : H.index • x = 0 := by
  rw [← tateCor_tateRes H A n x, hx, map_zero]

/-- **A class killed by restriction to a subgroup of index prime to a multiple that kills it
vanishes.** -/
theorem eq_zero_of_tateRes_eq_zero {H : Subgroup G} {A : Rep k G} {n : ℤ} {x : tateModule A n}
    (hx : tateRes H A n x = 0) {m : ℕ} (hm : m • x = 0) (hcop : Nat.Coprime H.index m) : x = 0 :=
  eq_zero_of_coprime_nsmul (index_smul_eq_zero_of_tateRes_eq_zero hx) hm hcop

/-- **A class killed by a power of a prime and by restriction to a Sylow subgroup for that prime
vanishes.** -/
theorem eq_zero_of_tateRes_sylow_eq_zero {p : ℕ} [Fact p.Prime] (P : Sylow p G) {A : Rep k G}
    {n : ℤ} {x : tateModule A n} (hx : tateRes (P : Subgroup G) A n x = 0) {j : ℕ}
    (hj : p ^ j • x = 0) : x = 0 :=
  eq_zero_of_tateRes_eq_zero hx hj
    (((Nat.Prime.coprime_iff_not_dvd Fact.out).2 P.not_dvd_index).symm.pow_right j)

end

end InverseGalois.CFT.Tate
