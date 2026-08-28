/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Multiquadratic
import InverseGalois.CFT.SqrtFrattini

/-!
# The sign character of a square root

An automorphism of a Galois extension multiplies an element whose square lies in the base field by
a sign, and recording that sign gives a homomorphism from the Galois group to `ZMod 2`.  Recorded
as a function of the automorphism rather than produced by an existential statement, the sign
becomes a canonical invariant of the element, so signs of different elements can be compared and
multiplied.

Two such elements carrying the same sign character have a product fixed by the whole Galois group,
hence lying in the base field; equivalently, the product of the two base elements is a square
there.  This is the mechanism that identifies the radicand of a square root once its character is
known, without any Kummer theory.

## Main definitions

* `InverseGalois.CFT.sqrtSign`: the sign by which an automorphism moves an element.

## Main results

* `InverseGalois.CFT.sqrtSign_apply_mul`: the sign character is a homomorphism on the Galois group.
* `InverseGalois.CFT.sqrtSign_mul_apply` and `InverseGalois.CFT.sqrtSign_prod_apply`: the sign
  character of a product of square roots is the sum of their sign characters.
* `InverseGalois.CFT.sqrtSign_eq_zero_of_mem_frattini`: the Frattini subgroup lies in the kernel of
  every sign character.
* `InverseGalois.CFT.sqrtSign_inclusion`: **the sign character is compatible with restriction to a
  smaller intermediate field.**
* `InverseGalois.CFT.exists_sq_eq_mul_of_sqrtSign_eq`: **two square roots of base elements with the
  same sign character have a product of radicands which is a square in the base field.**

## Tags

square root, quadratic character, Galois group, Frattini subgroup
-/

namespace InverseGalois.CFT

open scoped Classical

variable {F M : Type*} [Field F] [Field M] [Algebra F M]

/-! ### The sign of an element under an automorphism -/

/-- The **sign** by which an automorphism of a field extension moves an element: zero when the
automorphism fixes the element and one otherwise. -/
noncomputable def sqrtSign (u : M) (σ : Gal(M/F)) : ZMod 2 := if σ u = u then 0 else 1

theorem sqrtSign_eq_zero_iff (u : M) (σ : Gal(M/F)) : sqrtSign u σ = 0 ↔ σ u = u := by
  unfold sqrtSign
  by_cases h : σ u = u
  · simp [h]
  · simp [h]

theorem sqrtSign_one (u : M) : sqrtSign (F := F) u 1 = 0 :=
  (sqrtSign_eq_zero_iff u 1).mpr rfl

variable {u u' : M} {m m' : F}

/-- An automorphism moves an element whose square lies in the base field to itself or to its
negative. -/
theorem apply_eq_or_eq_neg (hm : u ^ 2 = algebraMap F M m) (σ : Gal(M/F)) :
    σ u = u ∨ σ u = -u := by
  have hsq : σ u ^ 2 = u ^ 2 := by rw [← map_pow, hm, AlgEquiv.commutes]
  have hfac : (σ u - u) * (σ u + u) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- An automorphism multiplies an element whose square lies in the base field by its sign. -/
theorem apply_eq_signZMod_mul (hm : u ^ 2 = algebraMap F M m) (σ : Gal(M/F)) :
    σ u = signZMod M (sqrtSign u σ) * u := by
  by_cases h : σ u = u
  · rw [sqrtSign, if_pos h, signZMod_zero, one_mul, h]
  · rw [sqrtSign, if_neg h, signZMod_one, neg_one_mul]
    exact (apply_eq_or_eq_neg hm σ).resolve_left h

/-- The sign is determined by the multiplication rule it satisfies. -/
theorem sqrtSign_eq_of_apply_eq [CharZero M] (hu : u ≠ 0) (hm : u ^ 2 = algebraMap F M m)
    {z : ZMod 2} {σ : Gal(M/F)} (h : σ u = signZMod M z * u) : sqrtSign u σ = z :=
  signZMod_injective M (mul_right_cancel₀ hu ((apply_eq_signZMod_mul hm σ).symm.trans h))

/-! ### The sign character -/

/-- **The sign character is a homomorphism on the Galois group.** -/
theorem sqrtSign_apply_mul [CharZero M] (hu : u ≠ 0) (hm : u ^ 2 = algebraMap F M m)
    (σ τ : Gal(M/F)) : sqrtSign u (σ * τ) = sqrtSign u σ + sqrtSign u τ := by
  refine sqrtSign_eq_of_apply_eq hu hm ?_
  rw [AlgEquiv.mul_apply, apply_eq_signZMod_mul hm τ, signZMod_add]
  rcases eq_zero_or_one_zmod_two (sqrtSign u τ) with h | h
  · rw [h, signZMod_zero, one_mul, mul_one, apply_eq_signZMod_mul hm σ]
  · rw [h, signZMod_one, neg_one_mul, map_neg, apply_eq_signZMod_mul hm σ]
    ring

/-- **The sign character of a product of two square roots is the sum of their sign
characters.** -/
theorem sqrtSign_mul_apply [CharZero M] (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hm : u ^ 2 = algebraMap F M m) (hm' : u' ^ 2 = algebraMap F M m') (σ : Gal(M/F)) :
    sqrtSign (u * u') σ = sqrtSign u σ + sqrtSign u' σ := by
  refine sqrtSign_eq_of_apply_eq (mul_ne_zero hu hu') (m := m * m') ?_ ?_
  · rw [mul_pow, hm, hm', map_mul]
  · rw [map_mul, apply_eq_signZMod_mul hm σ, apply_eq_signZMod_mul hm' σ, signZMod_add]
    ring

/-- The square of a product of square roots is the product of the radicands. -/
theorem sq_prod_eq_algebraMap {ι : Type*} {v : ι → M} {n : ι → F}
    (hn : ∀ i, (v i) ^ 2 = algebraMap F M (n i)) (J : Finset ι) :
    (∏ i ∈ J, v i) ^ 2 = algebraMap F M (∏ i ∈ J, n i) := by
  rw [← Finset.prod_pow, map_prod]
  exact Finset.prod_congr rfl fun i _ => hn i

/-- **The sign character of a product of square roots is the sum of their sign characters.** -/
theorem sqrtSign_prod_apply [CharZero M] {ι : Type*} {v : ι → M} {n : ι → F} (hv : ∀ i, v i ≠ 0)
    (hn : ∀ i, (v i) ^ 2 = algebraMap F M (n i)) (J : Finset ι) (σ : Gal(M/F)) :
    sqrtSign (∏ i ∈ J, v i) σ = ∑ i ∈ J, sqrtSign (v i) σ := by
  induction J using Finset.cons_induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact (sqrtSign_eq_zero_iff (1 : M) σ).mpr (map_one σ)
  | cons a J ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons, ← ih,
      sqrtSign_mul_apply (hv a) (Finset.prod_ne_zero_iff.mpr fun i _ => hv i) (hn a)
        (sq_prod_eq_algebraMap hn J)]

/-- **The Frattini subgroup lies in the kernel of every sign character.**  A square root of a base
element is fixed by every automorphism in the Frattini subgroup. -/
theorem sqrtSign_eq_zero_of_mem_frattini (hm : u ^ 2 = algebraMap F M m) {σ : Gal(M/F)}
    (hσ : σ ∈ frattini Gal(M/F)) : sqrtSign u σ = 0 := by
  refine (sqrtSign_eq_zero_iff u σ).mpr ?_
  have h := MulAction.mem_stabilizer_iff.mp (frattini_le_stabilizer_of_sq_eq hm hσ)
  simpa using h

/-! ### Restriction to a smaller intermediate field -/

section Restrict

open IntermediateField

variable {L : Type*} [Field L] [Algebra F L] {E E' : IntermediateField F L}

/-- **The sign character is compatible with restriction to a smaller intermediate field.**  An
automorphism of the larger field moves the image of an element of the smaller one by the same sign
by which its restriction moves the element itself. -/
theorem sqrtSign_inclusion (h : E ≤ E') [Normal F ↥E] (u : ↥E) (σ : Gal(↥E'/F)) :
    sqrtSign (inclusion h u) σ = sqrtSign u (galRestrictLE h σ) := by
  have key : ((σ (inclusion h u) : ↥E') : L) = ((galRestrictLE h σ u : ↥E) : L) := by
    rw [coe_galRestrictLE h σ u]
    rfl
  have hiff : σ (inclusion h u) = inclusion h u ↔ galRestrictLE h σ u = u := by
    constructor
    · exact fun hc => Subtype.ext (key.symm.trans (congrArg Subtype.val hc))
    · exact fun hc => Subtype.ext (key.trans (congrArg Subtype.val hc))
  unfold sqrtSign
  by_cases hu : galRestrictLE h σ u = u
  · rw [if_pos (hiff.mpr hu), if_pos hu]
  · rw [if_neg fun hc => hu (hiff.mp hc), if_neg hu]

end Restrict

/-! ### Recovering the radicand from the sign character -/

/-- Two square roots of base elements with the same sign character have a product lying in the base
field, being fixed by every automorphism. -/
theorem exists_algebraMap_eq_mul_of_sqrtSign_eq [FiniteDimensional F M] [IsGalois F M]
    (hm : u ^ 2 = algebraMap F M m) (hm' : u' ^ 2 = algebraMap F M m')
    (h : ∀ σ : Gal(M/F), sqrtSign u σ = sqrtSign u' σ) :
    ∃ c : F, u * u' = algebraMap F M c := by
  have hfix : ∀ σ : Gal(M/F), σ (u * u') = u * u' := by
    intro σ
    rw [map_mul, apply_eq_signZMod_mul hm σ, apply_eq_signZMod_mul hm' σ, ← h σ]
    rcases eq_zero_or_one_zmod_two (sqrtSign u σ) with hz | hz <;> rw [hz] <;>
      simp only [signZMod_zero, signZMod_one] <;> ring
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (u * u')).mpr hfix
  exact ⟨c, hc.symm⟩

/-- **Two square roots of base elements with the same sign character have a product of radicands
which is a square in the base field.** -/
theorem exists_sq_eq_mul_of_sqrtSign_eq [FiniteDimensional F M] [IsGalois F M]
    (hm : u ^ 2 = algebraMap F M m) (hm' : u' ^ 2 = algebraMap F M m')
    (h : ∀ σ : Gal(M/F), sqrtSign u σ = sqrtSign u' σ) : ∃ c : F, c ^ 2 = m * m' := by
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_mul_of_sqrtSign_eq hm hm' h
  refine ⟨c, (algebraMap F M).injective ?_⟩
  rw [map_pow, ← hc, mul_pow, hm, hm', map_mul]

end InverseGalois.CFT
