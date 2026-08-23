/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.FiltrationFinite
import InverseGalois.CFT.Local.FiltrationAction
import InverseGalois.CFT.Tate.FiniteExact

/-!
# The Herbrand quotient is the same on every step of the additive filtration

Any two steps of the additive filtration of a valued field with finite graded pieces are
commensurable: the deeper one sits inside the shallower one with finite quotient.  A group acting
by isometries preserves both steps, and the inclusion between them is equivariant, so it is an
equivariant injection with finite cokernel.  Such a map changes neither the finiteness of the Tate
groups nor the Herbrand quotient, and therefore a single step on which the Tate groups are known
to be finite determines the answer on all of them.

Because the steps are indexed by the integers and any two integers are comparable, no order
hypothesis survives into the final statements: knowing the Tate groups at one index gives them at
every index, with one and the same Herbrand quotient.

## Main results

* `InverseGalois.CFT.range_inclusion_valAddSubgroup`: the image of the inclusion of a deeper step
  of the additive filtration is that step, viewed inside the shallower one.
* `InverseGalois.CFT.inclusion_valAddSubgroupAut`: the inclusion of a deeper step into a shallower
  one commutes with the action of an isometry.
* `InverseGalois.CFT.finite_tate_valAddSubgroupAut_of_le`,
  `InverseGalois.CFT.finite_tate_valAddSubgroupAut_of_le'`: finiteness of the Tate groups passes
  between two comparable steps of the additive filtration, in both directions.
* `InverseGalois.CFT.herbrand_valAddSubgroupAut_eq_of_le`,
  `InverseGalois.CFT.herbrand_valAddSubgroupAut_eq_of_le'`: two comparable steps of the additive
  filtration have the same Herbrand quotient.
* `InverseGalois.CFT.finite_tate_valAddSubgroupAut`: **finiteness of the Tate groups on one step of
  the additive filtration gives it on every step.**
* `InverseGalois.CFT.herbrand_valAddSubgroupAut_eq`: **every step of the additive filtration has
  the same Herbrand quotient.**

## Tags

valued field, additive filtration, Herbrand quotient, Tate cohomology, commensurable
-/

namespace InverseGalois.CFT

open scoped WithZero

section NoAction

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰]

/-- The image of the inclusion of a deeper step of the additive filtration into a shallower one is
the deeper step, viewed as a subgroup of the shallower one. -/
theorem range_inclusion_valAddSubgroup {i j : ℤ} (h : i ≤ j) :
    (AddSubgroup.inclusion (valAddSubgroup_le_valAddSubgroup (A := A) h)).range
      = (valAddSubgroup A j).addSubgroupOf (valAddSubgroup A i) := by
  ext x
  simp only [AddMonoidHom.mem_range, AddSubgroup.mem_addSubgroupOf]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨(x : A), hx⟩, rfl⟩

/-- The quotient of a step of the additive filtration by the image of a deeper step is finite, when
every graded piece of the filtration is finite. -/
theorem finite_quotient_range_inclusion_valAddSubgroup [∀ k : ℤ, Finite (gradedAdd A k)] {i j : ℤ}
    (h : i ≤ j) :
    Finite (↥(valAddSubgroup A i)
      ⧸ (AddSubgroup.inclusion (valAddSubgroup_le_valAddSubgroup (A := A) h)).range) := by
  rw [range_inclusion_valAddSubgroup h]
  exact finite_quotient_valAddSubgroup h

end NoAction

variable {G A : Type*} [Group G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]
  (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

include hv

/-- The inclusion of a deeper step of the additive filtration into a shallower one commutes with
the action of an isometry, both actions being induced by the action on the field. -/
theorem inclusion_valAddSubgroupAut (σ : G) {i j : ℤ} (h : i ≤ j)
    (x : ↥(valAddSubgroup A j)) :
    AddSubgroup.inclusion (valAddSubgroup_le_valAddSubgroup (A := A) h)
        (valAddSubgroupAut hv σ j x)
      = valAddSubgroupAut hv σ i
          (AddSubgroup.inclusion (valAddSubgroup_le_valAddSubgroup (A := A) h) x) :=
  Subtype.ext rfl

/-- Finiteness of the Tate groups of a deeper step of the additive filtration passes to a shallower
step, the two being commensurable. -/
theorem finite_tate_valAddSubgroupAut_of_le [∀ k : ℤ, Finite (gradedAdd A k)] {σ : G} {n : ℕ}
    (hσ : σ ^ n = 1) {i j : ℤ} (h : i ≤ j)
    [Finite (tateH0 (valAddSubgroupAut hv σ j) n)]
    [Finite (tateHm1 (valAddSubgroupAut hv σ j) n)] :
    Finite (tateH0 (valAddSubgroupAut hv σ i) n)
      ∧ Finite (tateHm1 (valAddSubgroupAut hv σ i) n) := by
  haveI := finite_quotient_range_inclusion_valAddSubgroup (A := A) h
  exact ⟨finite_tateH0_of_injective (valAddSubgroupAut_pow_eq_one hv hσ j)
      (valAddSubgroupAut_pow_eq_one hv hσ i) _ (inclusion_valAddSubgroupAut hv σ h)
      (AddSubgroup.inclusion_injective _),
    finite_tateHm1_of_injective (valAddSubgroupAut_pow_eq_one hv hσ j)
      (valAddSubgroupAut_pow_eq_one hv hσ i) _ (inclusion_valAddSubgroupAut hv σ h)
      (AddSubgroup.inclusion_injective _)⟩

/-- Finiteness of the Tate groups of a step of the additive filtration passes to any deeper step,
the two being commensurable. -/
theorem finite_tate_valAddSubgroupAut_of_le' [∀ k : ℤ, Finite (gradedAdd A k)] {σ : G} {n : ℕ}
    (hσ : σ ^ n = 1) {i j : ℤ} (h : i ≤ j)
    [Finite (tateH0 (valAddSubgroupAut hv σ i) n)]
    [Finite (tateHm1 (valAddSubgroupAut hv σ i) n)] :
    Finite (tateH0 (valAddSubgroupAut hv σ j) n)
      ∧ Finite (tateHm1 (valAddSubgroupAut hv σ j) n) := by
  haveI := finite_quotient_range_inclusion_valAddSubgroup (A := A) h
  exact ⟨finite_tateH0_of_injective' (valAddSubgroupAut_pow_eq_one hv hσ j)
      (valAddSubgroupAut_pow_eq_one hv hσ i) _ (inclusion_valAddSubgroupAut hv σ h)
      (AddSubgroup.inclusion_injective _),
    finite_tateHm1_of_injective' (valAddSubgroupAut_pow_eq_one hv hσ j)
      (valAddSubgroupAut_pow_eq_one hv hσ i) _ (inclusion_valAddSubgroupAut hv σ h)
      (AddSubgroup.inclusion_injective _)⟩

/-- Two comparable steps of the additive filtration have the same Herbrand quotient, the finiteness
of the Tate groups being assumed on the deeper one. -/
theorem herbrand_valAddSubgroupAut_eq_of_le [∀ k : ℤ, Finite (gradedAdd A k)] {σ : G} {n : ℕ}
    (hσ : σ ^ n = 1) {i j : ℤ} (h : i ≤ j)
    [Finite (tateH0 (valAddSubgroupAut hv σ j) n)]
    [Finite (tateHm1 (valAddSubgroupAut hv σ j) n)] :
    herbrand (valAddSubgroupAut hv σ j) n = herbrand (valAddSubgroupAut hv σ i) n := by
  haveI := finite_quotient_range_inclusion_valAddSubgroup (A := A) h
  exact herbrand_eq_of_injective_of_finite_quotient_of_finite_source
    (valAddSubgroupAut_pow_eq_one hv hσ j) (valAddSubgroupAut_pow_eq_one hv hσ i) _
    (inclusion_valAddSubgroupAut hv σ h) (AddSubgroup.inclusion_injective _)

/-- Two comparable steps of the additive filtration have the same Herbrand quotient, the finiteness
of the Tate groups being assumed on the shallower one. -/
theorem herbrand_valAddSubgroupAut_eq_of_le' [∀ k : ℤ, Finite (gradedAdd A k)] {σ : G} {n : ℕ}
    (hσ : σ ^ n = 1) {i j : ℤ} (h : i ≤ j)
    [Finite (tateH0 (valAddSubgroupAut hv σ i) n)]
    [Finite (tateHm1 (valAddSubgroupAut hv σ i) n)] :
    herbrand (valAddSubgroupAut hv σ j) n = herbrand (valAddSubgroupAut hv σ i) n := by
  haveI := finite_quotient_range_inclusion_valAddSubgroup (A := A) h
  exact herbrand_eq_of_injective_of_finite_quotient_of_finite_target
    (valAddSubgroupAut_pow_eq_one hv hσ j) (valAddSubgroupAut_pow_eq_one hv hσ i) _
    (inclusion_valAddSubgroupAut hv σ h) (AddSubgroup.inclusion_injective _)

/-- **Finiteness of the Tate groups on one step of the additive filtration gives it on every
step**, since all the steps are commensurable. -/
theorem finite_tate_valAddSubgroupAut [∀ k : ℤ, Finite (gradedAdd A k)] {σ : G} {n : ℕ}
    (hσ : σ ^ n = 1) (j k : ℤ)
    [Finite (tateH0 (valAddSubgroupAut hv σ j) n)]
    [Finite (tateHm1 (valAddSubgroupAut hv σ j) n)] :
    Finite (tateH0 (valAddSubgroupAut hv σ k) n)
      ∧ Finite (tateHm1 (valAddSubgroupAut hv σ k) n) := by
  rcases le_total j k with h | h
  · exact finite_tate_valAddSubgroupAut_of_le' hv hσ h
  · exact finite_tate_valAddSubgroupAut_of_le hv hσ h

/-- **Every step of the additive filtration has the same Herbrand quotient**, the finiteness of the
Tate groups being assumed on a single step. -/
theorem herbrand_valAddSubgroupAut_eq [∀ k : ℤ, Finite (gradedAdd A k)] {σ : G} {n : ℕ}
    (hσ : σ ^ n = 1) (j k : ℤ)
    [Finite (tateH0 (valAddSubgroupAut hv σ j) n)]
    [Finite (tateHm1 (valAddSubgroupAut hv σ j) n)] :
    herbrand (valAddSubgroupAut hv σ k) n = herbrand (valAddSubgroupAut hv σ j) n := by
  rcases le_total j k with h | h
  · exact herbrand_valAddSubgroupAut_eq_of_le' hv hσ h
  · exact (herbrand_valAddSubgroupAut_eq_of_le hv hσ h).symm

end InverseGalois.CFT
