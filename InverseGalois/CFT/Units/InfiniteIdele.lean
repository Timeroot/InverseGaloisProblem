/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.InfiniteHerbrand
import InverseGalois.CFT.Tate.OrbitCocycle
import InverseGalois.CFT.Units.EquivariantLabel

/-!
# The local factor of the ideles at an infinite place of the base field

The infinite places of a cyclic extension of number fields lying above a fixed infinite place of the
base field form a single orbit of the Galois group, and the group carries the product of the unit
groups of the completions at them to itself.  Transporting all of the factors to the completion at
a chosen place turns that action into a shift of the index carrying with it, once around the orbit,
the action of the decomposition group of the chosen place; and Shapiro's lemma then reads the
Herbrand quotient of the product off the Herbrand quotient of the units of one completion.

The units of the completion at an infinite place have Herbrand quotient the order of the
decomposition group, so the whole local factor has that same Herbrand quotient.  This is word for
word the statement at a finite place, and it is what makes the archimedean places of a number field
contribute to the Herbrand quotient of the ideles by the same formula as the finite ones.

## Main results

* `InverseGalois.CFT.herbrand_twistShiftAut_infiniteUnits`: **the local factor of the ideles at an
  infinite place of the base field has Herbrand quotient the order of the decomposition group.**

## Tags

number field, idele, infinite place, decomposition group, Herbrand quotient, Shapiro's lemma
-/

namespace InverseGalois.CFT

open MulAction NumberField

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
variable {X : Type*} [Fintype X] [MulAction Gal(K/k) X] {ι : X → InfinitePlace K}
  (hι : ∀ (g : Gal(K/k)) (x : X), ι (g • x) = g • ι x) (hinj : Function.Injective ι) (x₀ : X)

include hι hinj

/-- **The local factor of the ideles at an infinite place of the base field has Herbrand quotient
the order of the decomposition group.**  Transporting the factors of the product to the completion
at a chosen place presents it as the module induced from the decomposition group, and the units of
a completion have Herbrand quotient the order of that group. -/
theorem herbrand_twistShiftAut_infiniteUnits [Finite Gal(K/k)] [IsPretransitive Gal(K/k) X]
    {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ)
    (htrans : ∀ y : X, ∃ j : ℕ, ((orbitShift X σ) ^ j) x₀ = y)
    (hH : ∀ g : Gal(K/k), g • x₀ = x₀ → g ∈ stabilizer Gal(K/k) (ι x₀))
    {n : ℕ} (hn : Nat.card Gal(K/k) = n) :
    herbrand (twistShiftAut
        (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (ι x₀))) (R := (ι x₀).Completion))
        (orbitCocycleSub x₀ htrans hH) (orbitShift X σ)) n
      = Nat.card ↥(stabilizer Gal(K/k) (ι x₀)) := by
  haveI : Fintype ↥(stabilizer Gal(K/k) (ι x₀)) := Fintype.ofFinite _
  haveI : NeZero (Nat.card ↥(stabilizer Gal(K/k) (ι x₀))) := ⟨Nat.card_pos.ne'⟩
  have hstab : stabilizer Gal(K/k) (ι x₀) = stabilizer Gal(K/k) x₀ :=
    stabilizer_eq_of_equivariant hι hinj x₀
  have hdm : period (orbitShift X σ) x₀ * Nat.card ↥(stabilizer Gal(K/k) (ι x₀)) = n := by
    rw [← card_eq_period (orbitShift X σ) x₀ htrans, hstab, card_mul_card_stabilizer, hn]
  have hσn : σ ^ n = 1 := by
    rw [← hn]
    exact pow_card_eq_one'
  have hturn : (orbitTurn σ x₀ hH) ^ Nat.card ↥(stabilizer Gal(K/k) (ι x₀)) = 1 :=
    orbitTurn_pow x₀ hH hσn hdm
  rw [herbrand_twistShiftAut_orbitCocycle x₀ htrans hH _ hturn hdm]
  exact herbrand_infiniteUnits_eq_card (ι x₀)
    (mem_zpowers_orbitTurn x₀ hH hgen (smul_eq_of_mem_stabilizer hι hinj x₀)) rfl

end InverseGalois.CFT
