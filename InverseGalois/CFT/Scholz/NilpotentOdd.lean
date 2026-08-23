import Mathlib
import InverseGalois.CFT.Scholz.Induction
import InverseGalois.Solvable.Nilpotent

/-!
# From `ℓ`-groups to nilpotent groups of odd order

The Scholz–Reichardt induction realises one prime at a time: granted the central embedding step
`IsCentralStepSolvable ℓ`, every finite `ℓ`-group occurs as a Galois group over `ℚ`.  A finite
nilpotent group is the direct product of its Sylow subgroups, and those have coprime orders, so the
`ℚ`-realizations of the Sylow subgroups may be combined into one realization of the whole group.

This file carries out that combination for groups of **odd** order, the case in which the central
step is available: the Sylow subgroup for an odd prime is realised by the induction, and the Sylow
`2`-subgroup of a group of odd order is trivial, so the prime `2` never has to be treated.

## Main results

* `InverseGalois.CFT.subsingleton_of_isPGroup_two`: a `2`-subgroup of a finite group of odd order
  is trivial.
* `InverseGalois.CFT.odd_card_sylow`: every Sylow subgroup of a finite group of odd order again
  has odd order.
* `InverseGalois.CFT.isInverseGalois_of_isPGroup_odd`: granted the central step for the odd
  primes, every finite `ℓ`-group with `ℓ` odd is a Galois group over `ℚ`.
* `InverseGalois.CFT.isInverseGalois_of_isNilpotent_of_odd`: **granted the central step for the
  odd primes, every finite nilpotent group of odd order is a Galois group over `ℚ`.**
* `InverseGalois.CFT.isInverseGalois_of_isNilpotent_of_ne_two`: the same conclusion with the
  hypothesis on the central step phrased through `ℓ ≠ 2`.
* `InverseGalois.CFT.isInverseGalois_of_odd_order_nilpotent`: the same conclusion with nilpotency
  supplied as an ordinary hypothesis rather than an instance.
-/

namespace InverseGalois.CFT

/-! ### The prime `2` in a group of odd order -/

/-- **A `2`-subgroup of a finite group of odd order is trivial.**  Its order is a power of `2`
dividing the odd order of the ambient group, hence the empty power. -/
theorem subsingleton_of_isPGroup_two {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G))
    (H : Subgroup G) (hH : IsPGroup 2 H) : Subsingleton H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  have hk0 : k = 0 := by
    by_contra hne
    refine hodd.not_two_dvd_nat (dvd_trans ?_ H.card_subgroup_dvd_card)
    rw [hk]
    exact dvd_pow_self 2 hne
  rw [hk0, pow_zero] at hk
  exact (Nat.card_eq_one_iff_unique.mp hk).1

/-- **A Sylow subgroup of a finite group of odd order has odd order**, its order being a divisor
of the order of the ambient group. -/
theorem odd_card_sylow {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G)) {p : ℕ}
    (P : Sylow p G) : Odd (Nat.card ↥(P : Subgroup G)) := by
  rcases Nat.even_or_odd (Nat.card ↥(P : Subgroup G)) with he | ho
  · exact absurd (dvd_trans he.two_dvd (P : Subgroup G).card_subgroup_dvd_card)
      hodd.not_two_dvd_nat
  · exact ho

/-! ### Odd `ℓ`-groups -/

/-- **Granted the central step for the odd primes, every finite `ℓ`-group with `ℓ` odd is a Galois
group over `ℚ`.** -/
theorem isInverseGalois_of_isPGroup_odd
    (hstep : ∀ q : ℕ, q.Prime → Odd q → IsCentralStepSolvable q) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hodd : Odd ℓ) (G : Type) [Group G] [Finite G] (hG : IsPGroup ℓ G) : IsInverseGalois G :=
  isInverseGalois_of_isCentralStepSolvable hℓ (hstep ℓ hℓ hodd) G hG

/-! ### Nilpotent groups of odd order -/

/-- **Granted the central step for the odd primes, every finite nilpotent group of odd order is a
Galois group over `ℚ`.**  A finite nilpotent group is the direct product of its Sylow subgroups,
and the inverse Galois property is closed under products of groups of coprime order; the Sylow
subgroup for an odd prime is realised by the Scholz–Reichardt induction, and the Sylow
`2`-subgroup is trivial. -/
theorem isInverseGalois_of_isNilpotent_of_odd
    (hstep : ∀ q : ℕ, q.Prime → Odd q → IsCentralStepSolvable q) (G : Type) [Group G] [Finite G]
    [Group.IsNilpotent G] (hodd : Odd (Nat.card G)) : IsInverseGalois G := by
  refine isInverseGalois_of_isNilpotent fun p hp P => ?_
  rcases eq_or_ne p 2 with rfl | hp2
  · haveI := subsingleton_of_isPGroup_two hodd (P : Subgroup G) P.isPGroup'
    haveI : Unique ↥(P : Subgroup G) := uniqueOfSubsingleton 1
    exact IsInverseGalois.unit.of_mulEquiv (MulEquiv.ofUnique (M := Unit))
  · exact isInverseGalois_of_isPGroup_odd hstep hp.out (hp.out.odd_of_ne_two hp2) _ P.isPGroup'

/-- **Granted the central step for every prime other than `2`, every finite nilpotent group of odd
order is a Galois group over `ℚ`.**  For a prime, being odd and being different from `2` are the
same condition. -/
theorem isInverseGalois_of_isNilpotent_of_ne_two
    (hstep : ∀ q : ℕ, q.Prime → q ≠ 2 → IsCentralStepSolvable q) (G : Type) [Group G] [Finite G]
    [Group.IsNilpotent G] (hodd : Odd (Nat.card G)) : IsInverseGalois G :=
  isInverseGalois_of_isNilpotent_of_odd
    (fun q hq hq2 => hstep q hq (by rintro rfl; simp [Nat.odd_iff] at hq2)) G hodd

/-- **Granted the central step for the odd primes, a finite group of odd order that is nilpotent is
a Galois group over `ℚ`**, with the nilpotency supplied as an ordinary hypothesis. -/
theorem isInverseGalois_of_odd_order_nilpotent
    (hstep : ∀ q : ℕ, q.Prime → Odd q → IsCentralStepSolvable q) (G : Type) [Group G] [Finite G]
    (hnil : Group.IsNilpotent G) (hodd : Odd (Nat.card G)) : IsInverseGalois G :=
  haveI := hnil
  isInverseGalois_of_isNilpotent_of_odd hstep G hodd

end InverseGalois.CFT
