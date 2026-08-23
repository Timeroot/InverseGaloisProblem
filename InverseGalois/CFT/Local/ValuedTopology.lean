/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnitFiltration

/-!
# The topology of a valued field

The neighbourhoods of zero in a valued ring contain the subgroups cut out by the valuation, so the
topology is nonarchimedean: every neighbourhood of zero contains an open subgroup.  For a
discretely valued field the steps of the additive filtration are themselves such subgroups, and
they form a basis of neighbourhoods of zero.  Being open they are closed, so an infinite sum of
elements of a given step again lies in that step, and a family whose valuations become arbitrarily
small tends to zero.

## Main results

* `InverseGalois.CFT.valued_nonarchimedeanRing`: **a valued ring is nonarchimedean.**
* `InverseGalois.CFT.isOpen_valAddSubgroup`, `InverseGalois.CFT.isClosed_valAddSubgroup`: the steps
  of the additive filtration are open, hence closed.
* `InverseGalois.CFT.tendsto_zero_of_valued`: a family whose valuations become arbitrarily small
  tends to zero.
* `InverseGalois.CFT.valued_le_of_hasSum`: **the valuation of a sum is at most the largest
  valuation of a term.**

## Tags

valued field, nonarchimedean topology, infinite sum
-/

namespace InverseGalois.CFT

open Filter Topology

open scoped WithZero

/-! ### Nonarchimedean topology -/

section Nonarchimedean

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀]

/-- **A valued ring is nonarchimedean.**  Every neighbourhood of zero contains a set of the form
`{x | v x < γ}`, and that set is an open additive subgroup. -/
instance valued_nonarchimedeanRing : NonarchimedeanRing R where
  is_nonarchimedean U hU := by
    obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation U).mp hU
    have hmem : ((Valuation.ltAddSubgroup (Valued.v : Valuation R Γ₀) γ : AddSubgroup R) :
        Set R) ∈ 𝓝 (0 : R) :=
      (Valued.is_topological_valuation _).mpr ⟨γ, fun x hx => hx⟩
    exact ⟨⟨Valuation.ltAddSubgroup Valued.v γ, AddSubgroup.isOpen_of_mem_nhds _ hmem⟩, hγ⟩

end Nonarchimedean

/-! ### The steps of the additive filtration -/

section Field

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰]

/-- A nonzero element of `ℤᵐ⁰` dominates the exponential of a small enough integer. -/
theorem exists_exp_lt (γ : ℤᵐ⁰ˣ) : ∃ j : ℤ, WithZero.exp (-j) < (γ : ℤᵐ⁰) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (γ : ℤᵐ⁰) = WithZero.exp m :=
    ⟨WithZero.log (γ : ℤᵐ⁰), (WithZero.exp_log γ.ne_zero).symm⟩
  refine ⟨-m + 1, ?_⟩
  rw [hm]
  exact WithZero.exp_lt_exp.mpr (by omega)

/-- **The steps of the additive filtration are open.**  A step contains the elements of strictly
smaller valuation, which form a neighbourhood of zero. -/
theorem isOpen_valAddSubgroup (j : ℤ) : IsOpen ((valAddSubgroup A j : AddSubgroup A) : Set A) := by
  refine AddSubgroup.isOpen_of_mem_nhds _ ((Valued.is_topological_valuation _).mpr
    ⟨Units.mk0 (WithZero.exp (1 - j)) WithZero.exp_ne_zero, fun x hx => ?_⟩)
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hx
  rw [SetLike.mem_coe, mem_valAddSubgroup]
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · rw [h0]
    exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    exact WithZero.exp_le_exp.mpr (by have := WithZero.exp_lt_exp.mp hx; omega)

/-- **The steps of the additive filtration are closed**, being open subgroups. -/
theorem isClosed_valAddSubgroup (j : ℤ) :
    IsClosed ((valAddSubgroup A j : AddSubgroup A) : Set A) :=
  AddSubgroup.isClosed_of_isOpen _ (isOpen_valAddSubgroup j)

/-- **A family whose valuations become arbitrarily small tends to zero.** -/
theorem tendsto_zero_of_valued {ι : Type*} {l : Filter ι} {f : ι → A}
    (h : ∀ j : ℤ, ∀ᶠ i in l, Valued.v (f i) ≤ WithZero.exp (-j)) : Tendsto f l (𝓝 0) := by
  rw [tendsto_def]
  intro U hU
  obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation U).mp hU
  obtain ⟨j, hj⟩ := exists_exp_lt γ
  filter_upwards [h j] with i hi
  exact hγ (lt_of_le_of_lt hi hj)

/-- **The valuation of a sum is at most the largest valuation of a term.**  The elements of
valuation at most a given power form a closed subgroup containing every partial sum. -/
theorem valued_le_of_hasSum {ι : Type*} {f : ι → A} {a : A} (h : HasSum f a) {j : ℤ}
    (hf : ∀ i, Valued.v (f i) ≤ WithZero.exp (-j)) : Valued.v a ≤ WithZero.exp (-j) := by
  have hmem : a ∈ (valAddSubgroup A j : AddSubgroup A) := by
    refine (isClosed_valAddSubgroup j).mem_of_tendsto h
      (Filter.Eventually.of_forall fun s => ?_)
    exact AddSubgroup.sum_mem _ fun i _ => mem_valAddSubgroup.mpr (hf i)
  exact mem_valAddSubgroup.mp hmem

end Field

end InverseGalois.CFT
