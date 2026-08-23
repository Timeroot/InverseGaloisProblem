/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.FiltrationHerbrand
import InverseGalois.CFT.Local.TraceIntegral
import InverseGalois.CFT.Tate.CyclicInduced
import InverseGalois.CFT.Tate.NormalBasis

/-!
# The valuation ring contains a normal lattice of finite index

A finite group acting faithfully by isometries on a valued field makes the field a Galois extension
of the subfield it fixes, and the normal basis theorem produces an element whose orbit is a basis.
The integral combinations of that orbit form a subgroup of a step of the additive filtration on
which the group acts by translating the coefficients.  It is of finite index there: expanding an
element in the basis dual to the orbit for the trace form expresses its coefficients as traces, and
those are integral as soon as the element is small enough, so the subgroup contains a step of the
filtration.  For a cyclic group this makes the step of the filtration a module containing an
induced lattice of finite index, whence its Herbrand quotient is one.

## Main definitions

* `InverseGalois.CFT.normalLatticeHom`: the integral combinations of the orbit, as a map from the
  functions on the group with integral values in the fixed field.

## Main results

* `InverseGalois.CFT.normalLatticeHom_equivariant`: the group acts on the coefficients by
  translation.
* `InverseGalois.CFT.exists_valAddSubgroup_le_range`: **a deep enough step of the additive
  filtration consists of integral combinations of the orbit.**
* `InverseGalois.CFT.finite_quotient_range_normalLatticeHom`: the integral combinations are of
  finite index.
* `InverseGalois.CFT.herbrand_valAddSubgroupAut_normal`: **a step of the additive filtration
  containing the chosen element has Herbrand quotient one under a cyclic group.**
* `InverseGalois.CFT.herbrand_valAddSubgroupAut_eq_one`: **every step of the additive filtration
  has Herbrand quotient one under a cyclic group.**

## Tags

valued field, normal basis, lattice, Herbrand quotient, trace form
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {G A : Type*} [Group G] [Fintype G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]
  [FaithfulSMul G A]

/-! ### Integral combinations of the orbit -/

omit [Fintype G] [FaithfulSMul G A] in
/-- An element of the fixed field with integral value scales the additive filtration. -/
theorem smul_mem_valAddSubgroup_of_fixedInt {c : ↥(FixedPoints.subfield G A)}
    (hc : c ∈ fixedInt G A) {j : ℤ} {x : A} (hx : x ∈ valAddSubgroup A j) :
    c • x ∈ valAddSubgroup A j := by
  rw [Algebra.smul_def]
  have h := mul_mem_valAddSubgroup (algebraMap_mem_valAddSubgroup hc) hx
  rwa [zero_add] at h

variable (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

include hv

/-- Every member of the orbit lies as deep in the additive filtration as the chosen element. -/
theorem normalBasisOfGroup_mem (g : G) {j : ℤ} (hj : normalElt G A ∈ valAddSubgroup A j) :
    normalBasisOfGroup G A g ∈ valAddSubgroup A j := by
  rw [normalBasisOfGroup_apply]
  exact smul_mem_valAddSubgroup hv g hj

/-- **The integral combinations of the orbit**, as a map from the functions on the group with
integral values in the fixed field. -/
noncomputable def normalLatticeHom (j : ℤ) (hj : normalElt G A ∈ valAddSubgroup A j) :
    (G → ↥(fixedInt G A)) →+ ↥(valAddSubgroup A j) where
  toFun f :=
    ⟨∑ g : G, ((f g : ↥(FixedPoints.subfield G A))) • normalBasisOfGroup G A g,
      AddSubgroup.sum_mem _ fun g _ =>
        smul_mem_valAddSubgroup_of_fixedInt (f g).2 (normalBasisOfGroup_mem hv g hj)⟩
  map_zero' := by
    refine Subtype.ext ?_
    show ∑ g : G, ((0 : G → ↥(fixedInt G A)) g : ↥(FixedPoints.subfield G A)) • _ = (0 : A)
    simp
  map_add' f f' := by
    refine Subtype.ext ?_
    show ∑ g : G, (((f + f') g : ↥(fixedInt G A)) : ↥(FixedPoints.subfield G A)) • _
      = (∑ g : G, ((f g : ↥(FixedPoints.subfield G A))) • normalBasisOfGroup G A g)
        + ∑ g : G, ((f' g : ↥(FixedPoints.subfield G A))) • normalBasisOfGroup G A g
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← add_smul]
    rfl

@[simp]
theorem coe_normalLatticeHom (j : ℤ) (hj : normalElt G A ∈ valAddSubgroup A j)
    (f : G → ↥(fixedInt G A)) :
    ((normalLatticeHom hv j hj f : ↥(valAddSubgroup A j)) : A)
      = ∑ g : G, ((f g : ↥(FixedPoints.subfield G A))) • normalBasisOfGroup G A g := rfl

/-- **The group acts on the integral combinations by translating the coefficients.** -/
theorem normalLatticeHom_equivariant (j : ℤ) (hj : normalElt G A ∈ valAddSubgroup A j) (σ : G)
    (f : G → ↥(fixedInt G A)) :
    normalLatticeHom hv j hj (translateAut σ f)
      = valAddSubgroupAut hv σ j (normalLatticeHom hv j hj f) := by
  refine Subtype.ext ?_
  rw [coe_valAddSubgroupAut, coe_normalLatticeHom, coe_normalLatticeHom, Finset.smul_sum]
  simp only [translateAut_apply]
  refine Fintype.sum_equiv (Equiv.mulLeft σ⁻¹) _ _ fun g => ?_
  show ((f (σ⁻¹ * g) : ↥(FixedPoints.subfield G A))) • normalBasisOfGroup G A g
    = σ • ((f (σ⁻¹ * g) : ↥(FixedPoints.subfield G A))) • normalBasisOfGroup G A (σ⁻¹ * g)
  rw [smul_smul_fixed, normalBasisOfGroup_apply, normalBasisOfGroup_apply, smul_smul]
  simp

theorem normalLatticeHom_injective (j : ℤ) (hj : normalElt G A ∈ valAddSubgroup A j) :
    Function.Injective (normalLatticeHom hv j hj) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h0 : ∑ g : G, ((f g : ↥(FixedPoints.subfield G A))) • normalBasisOfGroup G A g = 0 :=
    congrArg Subtype.val hf
  have hz := Fintype.linearIndependent_iff.mp (normalBasisOfGroup G A).linearIndependent _ h0
  funext g
  exact Subtype.ext (hz g)

/-! ### The index is finite -/

omit [Valued A ℤᵐ⁰] [FaithfulSMul G A] hv in
/-- The coefficients of an element with respect to a basis are the traces against the dual basis
for the trace form. -/
theorem repr_eq_trace [DecidableEq G] (b : Module.Basis G ↥(FixedPoints.subfield G A) A) (x : A)
    (g : G) :
    b.repr x g = Algebra.trace ↥(FixedPoints.subfield G A) A (x * b.traceDual g) := by
  conv_lhs => rw [← Module.Basis.traceDual_traceDual (b := b)]
  rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply]

/-- **A deep enough step of the additive filtration consists of integral combinations of the
orbit**: the coefficients of a small element are traces of small elements, hence integral. -/
theorem exists_valAddSubgroup_le_range (j : ℤ) (hj : normalElt G A ∈ valAddSubgroup A j) :
    ∃ N : ℤ, j ≤ N ∧ ∀ x ∈ valAddSubgroup A N,
      ∃ f : G → ↥(fixedInt G A), ((normalLatticeHom hv j hj f : ↥(valAddSubgroup A j)) : A) = x := by
  classical
  set b := normalBasisOfGroup G A with hb
  have hne : ∀ g : G, Valued.v (b.traceDual g) ≠ 0 := by
    intro g
    rw [Valuation.ne_zero_iff]
    exact b.traceDual.ne_zero g
  set m : G → ℤ := fun g => WithZero.log (Valued.v (b.traceDual g)) with hm
  have hmv : ∀ g : G, Valued.v (b.traceDual g) = WithZero.exp (m g) := fun g =>
    (WithZero.exp_log (hne g)).symm
  obtain ⟨N₀, hN₀⟩ := Finite.exists_le m
  refine ⟨max j N₀, le_max_left _ _, ?_⟩
  intro x hx
  have hxv : Valued.v x ≤ WithZero.exp (-max j N₀) := mem_valAddSubgroup.mp hx
  have hcoeff : ∀ g : G,
      Algebra.trace ↥(FixedPoints.subfield G A) A (x * b.traceDual g) ∈ fixedInt G A := by
    intro g
    refine trace_mem_fixedInt hv ?_
    rw [map_mul, hmv g]
    calc Valued.v x * WithZero.exp (m g)
        ≤ WithZero.exp (-max j N₀) * WithZero.exp (m g) := by gcongr
      _ = WithZero.exp (m g - max j N₀) := by rw [← WithZero.exp_add]; ring_nf
      _ ≤ 1 := by
          rw [show (1 : ℤᵐ⁰) = WithZero.exp (0 : ℤ) from rfl]
          have h₁ := hN₀ g
          have h₂ := le_max_right j N₀
          exact WithZero.exp_le_exp.mpr (by omega)
  refine ⟨fun g => ⟨_, hcoeff g⟩, ?_⟩
  rw [coe_normalLatticeHom]
  conv_rhs => rw [← b.sum_repr x]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [repr_eq_trace]

/-- The integral combinations of the orbit are of finite index in the step of the additive
filtration. -/
theorem finite_quotient_range_normalLatticeHom [∀ k : ℤ, Finite (gradedAdd A k)] (j : ℤ)
    (hj : normalElt G A ∈ valAddSubgroup A j) :
    Finite (↥(valAddSubgroup A j) ⧸ (normalLatticeHom hv j hj).range) := by
  obtain ⟨N, hjN, hN⟩ := exists_valAddSubgroup_le_range hv j hj
  haveI := finite_quotient_valAddSubgroup (A := A) hjN
  have hle : (valAddSubgroup A N).addSubgroupOf (valAddSubgroup A j)
      ≤ (normalLatticeHom hv j hj).range.comap (AddMonoidHom.id ↥(valAddSubgroup A j)) := by
    intro y hy
    obtain ⟨f, hf⟩ := hN (y : A) (AddSubgroup.mem_addSubgroupOf.mp hy)
    exact ⟨f, Subtype.ext hf⟩
  refine Finite.of_surjective (QuotientAddGroup.map _ _ (AddMonoidHom.id _) hle) ?_
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H z => exact ⟨QuotientAddGroup.mk z, rfl⟩

/-! ### The Herbrand quotient of the valuation ring -/

/-- **A step of the additive filtration containing the chosen element has Herbrand quotient one
under a cyclic group.** -/
theorem herbrand_valAddSubgroupAut_normal [∀ k : ℤ, Finite (gradedAdd A k)] {σ : G}
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d] (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) (j : ℤ) (hj : normalElt G A ∈ valAddSubgroup A j) :
    herbrand (valAddSubgroupAut hv σ j) d = 1 := by
  haveI := finite_quotient_range_normalLatticeHom hv j hj
  exact herbrand_eq_one_of_translationLattice hgen hσ hcard
    (valAddSubgroupAut_pow_eq_one hv hσ j) (normalLatticeHom hv j hj)
    (normalLatticeHom_equivariant hv j hj σ) (normalLatticeHom_injective hv j hj)

/-- The Tate groups of a step of the additive filtration containing the chosen element are finite
under a cyclic group. -/
theorem finite_tate_valAddSubgroupAut_normal [∀ k : ℤ, Finite (gradedAdd A k)] {σ : G}
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d] (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) (j : ℤ) (hj : normalElt G A ∈ valAddSubgroup A j) :
    Finite (tateH0 (valAddSubgroupAut hv σ j) d)
      ∧ Finite (tateHm1 (valAddSubgroupAut hv σ j) d) := by
  haveI := finite_quotient_range_normalLatticeHom hv j hj
  exact finite_tate_of_translationLattice hgen hσ hcard
    (valAddSubgroupAut_pow_eq_one hv hσ j) (normalLatticeHom hv j hj)
    (normalLatticeHom_equivariant hv j hj σ) (normalLatticeHom_injective hv j hj)

omit [FaithfulSMul G A] hv in
/-- The chosen element lies in some step of the additive filtration. -/
theorem exists_mem_valAddSubgroup_normalElt : ∃ j : ℤ, normalElt G A ∈ valAddSubgroup A j := by
  have hne : Valued.v (normalElt G A) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact (IsGalois.normalBasis ↥(FixedPoints.subfield G A) A).ne_zero 1
  refine ⟨-WithZero.log (Valued.v (normalElt G A)), ?_⟩
  rw [mem_valAddSubgroup, neg_neg, WithZero.exp_log hne]

/-- **Every step of the additive filtration has Herbrand quotient one under a cyclic group.** -/
theorem herbrand_valAddSubgroupAut_eq_one [∀ k : ℤ, Finite (gradedAdd A k)] {σ : G}
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d] (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) (k : ℤ) : herbrand (valAddSubgroupAut hv σ k) d = 1 := by
  obtain ⟨j, hj⟩ := exists_mem_valAddSubgroup_normalElt (G := G) (A := A)
  obtain ⟨h0, h1⟩ := finite_tate_valAddSubgroupAut_normal hv hgen hσ hcard j hj
  haveI := h0
  haveI := h1
  rw [herbrand_valAddSubgroupAut_eq hv hσ j k]
  exact herbrand_valAddSubgroupAut_normal hv hgen hσ hcard j hj

end InverseGalois.CFT
