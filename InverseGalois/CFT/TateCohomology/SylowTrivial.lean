/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.CohomTrivial
import InverseGalois.CFT.TateCohomology.SylowInjective

/-!
# Cohomological triviality read off from the Sylow subgroups

The order of a class of the complete cohomology divides the index of every subgroup to which the
class restricts trivially.  A Sylow subgroup for a prime has index prime to that prime, so a class
restricting trivially to a Sylow subgroup for **every** prime has an order divisible by no prime at
all, and therefore vanishes.

Combined with the cohomological triviality of a representation of a `p`-group, this reads the
vanishing of the complete cohomology of a finite group off from its Sylow subgroups: it is enough
that the restriction of the representation to each of them have no complete cohomology in two
consecutive degrees, degrees which may even depend on the prime.

## Main results

* `InverseGalois.CFT.Tate.eq_zero_of_tateRes_sylow`: **a class restricting trivially to a Sylow
  subgroup for every prime vanishes.**
* `InverseGalois.CFT.Tate.isZero_tateModule_of_sylow`: **a representation over the integers whose
  restriction to a Sylow subgroup for each prime has no complete cohomology in two consecutive
  degrees has no complete cohomology in any degree.**

## Tags

Tate cohomology, cohomologically trivial, Sylow subgroup, order of a class
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### The order of a class -/

section Order

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **A class restricting trivially to a Sylow subgroup for every prime vanishes.** -/
theorem eq_zero_of_tateRes_sylow (A : Rep k G) (n : ℤ) (x : tateModule A n)
    (h : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, tateRes (P : Subgroup G) A n x = 0) : x = 0 := by
  by_contra hx
  have ht1 : addOrderOf x ≠ 1 := fun h => hx (AddMonoid.addOrderOf_eq_one_iff.1 h)
  have hqp : (addOrderOf x).minFac.Prime := Nat.minFac_prime ht1
  haveI : Fact (addOrderOf x).minFac.Prime := ⟨hqp⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow (addOrderOf x).minFac G))
  have hdvd : addOrderOf x ∣ (P : Subgroup G).index :=
    addOrderOf_dvd_iff_nsmul_eq_zero.2
      (index_smul_eq_zero_of_tateRes_eq_zero (h _ hqp P))
  exact P.not_dvd_index ((Nat.minFac_dvd (addOrderOf x)).trans hdvd)

end Order

/-! ### Vanishing read off from the Sylow subgroups -/

section Int

variable {G : Type} [Group G] [Finite G]

/-- **A representation over the integers whose restriction to a Sylow subgroup for each prime has
no complete cohomology in two consecutive degrees has no complete cohomology in any degree.** -/
theorem isZero_tateModule_of_sylow (A : Rep ℤ G)
    (h : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, ∃ i : ℤ,
      Limits.IsZero (tateModule (resObj (P : Subgroup G) A) i) ∧
        Limits.IsZero (tateModule (resObj (P : Subgroup G) A) (i + 1)))
    (n : ℤ) : Limits.IsZero (tateModule A n) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  refine eq_zero_of_tateRes_sylow A n x fun p hp P => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi, hi1⟩ := h p hp P
  exact eq_zero_of_isZero
    (isZero_tateModule_of_isZero_two P.isPGroup' (resObj (P : Subgroup G) A) hi hi1 n) _

end Int

end

end InverseGalois.CFT.Tate
