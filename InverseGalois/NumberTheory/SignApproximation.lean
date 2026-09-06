/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Prescribing the signs of a unit at the real places of a number field

A number field has finitely many real places, and each of them is given by an embedding into the
reals.  A nonzero element of the field therefore has a well defined sign at every real place, and
the question is which patterns of signs occur.  The answer is that all of them do: the real places
are independent of one another, so for any prescribed set of real places there is an element of the
field which is negative exactly at those and positive at the others.

The proof is elementary and avoids any approximation theorem for the infinite places.  A primitive
element `θ` of the field takes pairwise distinct real values at the real places, because a ring
homomorphism out of the field is determined by the image of `θ`.  Picking two rationals `c < d`
that straddle the value of `θ` at one chosen real place and are closer to it than any other real
value of `θ`, the element `(θ - c)(θ - d)` is a product of two factors of opposite sign at the
chosen place and of two factors of the same sign at every other real place, hence is negative
exactly at the chosen one.  Multiplying such elements together realizes an arbitrary pattern.

## Main results

* `InverseGalois.NumberTheory.exists_adjoin_singleton_eq_top`: a number field is generated over the
  rationals by a single element, as an algebra.
* `InverseGalois.NumberTheory.embedding_of_isReal_ne_of_ne`: a generator takes distinct values at
  distinct real places.
* `InverseGalois.NumberTheory.exists_units_neg_at`: **there is a unit which is negative at one
  prescribed real place and positive at every other real place.**
* `InverseGalois.NumberTheory.exists_units_pos_iff_notMem`: **for any finite set of infinite places
  there is a unit which is positive exactly at the real places outside that set.**
* `InverseGalois.NumberTheory.exists_units_pos_iff_notMem_set`: the same statement for an arbitrary
  set of infinite places.

## Tags

number field, real place, real embedding, sign, primitive element, approximation
-/

open Module NumberField

namespace InverseGalois.NumberTheory

/-! ### Distinct real places are separated by a generator -/

section Separate

variable {k : Type*} [Field k] [NumberField k]

omit [NumberField k] in
/-- Two real places sharing the same real embedding are equal. -/
theorem infinitePlace_eq_of_embedding_of_isReal_eq {u v : InfinitePlace k} (hu : u.IsReal)
    (hv : v.IsReal)
    (h : InfinitePlace.embedding_of_isReal hu = InfinitePlace.embedding_of_isReal hv) : u = v := by
  have hemb : u.embedding = v.embedding := by
    ext x
    rw [← InfinitePlace.embedding_of_isReal_apply hu, ← InfinitePlace.embedding_of_isReal_apply hv,
      h]
  rw [← InfinitePlace.mk_embedding u, ← InfinitePlace.mk_embedding v, hemb]

/-- A number field is generated over the rationals, as an algebra, by a single element. -/
theorem exists_adjoin_singleton_eq_top (k : Type*) [Field k] [NumberField k] :
    ∃ θ : k, Algebra.adjoin ℚ ({θ} : Set k) = ⊤ := by
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ k
  refine ⟨θ, ?_⟩
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsIntegral.isIntegral θ).isAlgebraic, hθ, IntermediateField.top_toSubalgebra]

/-- **A generator of a number field takes distinct values at distinct real places.** -/
theorem embedding_of_isReal_ne_of_ne {θ : k} (hθ : Algebra.adjoin ℚ ({θ} : Set k) = ⊤)
    {u v : InfinitePlace k} (hu : u.IsReal) (hv : v.IsReal) (huv : u ≠ v) :
    InfinitePlace.embedding_of_isReal hu θ ≠ InfinitePlace.embedding_of_isReal hv θ := by
  intro h
  refine huv (infinitePlace_eq_of_embedding_of_isReal_eq hu hv ?_)
  have halg : (InfinitePlace.embedding_of_isReal hu).toRatAlgHom
      = (InfinitePlace.embedding_of_isReal hv).toRatAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top hθ ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simpa using h
  simpa using congrArg (fun f : k →ₐ[ℚ] ℝ => (f : k →+* ℝ)) halg

end Separate

/-! ### A unit negative at a single real place -/

section Single

/-- A product of two nonzero reals is positive exactly when the two factors have the same sign. -/
private theorem pos_mul_iff_of_ne_zero {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    0 < x * y ↔ (0 < x ↔ 0 < y) := by
  rw [mul_pos_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · exact ⟨fun h => absurd h (asymm h1), fun h => absurd h (asymm h2)⟩
  · intro h
    rcases hx.lt_or_gt with hx' | hx'
    · refine Or.inr ⟨hx', ?_⟩
      rcases hy.lt_or_gt with hy' | hy'
      · exact hy'
      · exact absurd (h.mpr hy') (asymm hx')
    · exact Or.inl ⟨hx', h.mp hx'⟩

/-- **A unit of a number field which is negative at one prescribed real place and positive at
every other real place.** -/
theorem exists_units_neg_at (k : Type*) [Field k] [NumberField k] {u₀ : InfinitePlace k}
    (hu₀ : u₀.IsReal) :
    ∃ a : kˣ, InfinitePlace.embedding_of_isReal hu₀ (a : k) < 0 ∧
      ∀ (v : InfinitePlace k) (hv : v.IsReal), v ≠ u₀ →
        0 < InfinitePlace.embedding_of_isReal hv (a : k) := by
  classical
  obtain ⟨θ, hθ⟩ := exists_adjoin_singleton_eq_top k
  obtain ⟨F, hFr⟩ : ∃ F : InfinitePlace k → ℝ, ∀ (w : InfinitePlace k) (hw : w.IsReal),
      F w = InfinitePlace.embedding_of_isReal hw θ :=
    ⟨fun w => if hw : w.IsReal then InfinitePlace.embedding_of_isReal hw θ else 0,
      fun w hw => dif_pos hw⟩
  -- the distances from the other real values of the generator, bounded away from zero
  set A : Finset ℝ := insert (1 : ℝ)
    ((Finset.univ.filter fun w : InfinitePlace k => w.IsReal ∧ w ≠ u₀).image
      fun w => |F w - F u₀|) with hA
  have hApos : ∀ x ∈ A, 0 < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact one_pos
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hwr, hwne⟩ := (Finset.mem_filter.mp hw).2
      rw [abs_pos, sub_ne_zero, hFr w hwr, hFr u₀ hu₀]
      exact embedding_of_isReal_ne_of_ne hθ hwr hu₀ hwne
  have hAne : A.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hδpos : 0 < A.min' hAne := (Finset.lt_min'_iff A hAne).mpr hApos
  have hδle : ∀ (w : InfinitePlace k), w.IsReal → w ≠ u₀ → A.min' hAne ≤ |F w - F u₀| := by
    intro w hwr hwne
    exact Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwr, hwne⟩)))
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show F u₀ - A.min' hAne < F u₀ by linarith)
  obtain ⟨d, hd1, hd2⟩ := exists_rat_btwn (show F u₀ < F u₀ + A.min' hAne by linarith)
  have hval : ∀ (w : InfinitePlace k) (hw : w.IsReal),
      InfinitePlace.embedding_of_isReal hw ((θ - (c : k)) * (θ - (d : k)))
        = (F w - (c : ℝ)) * (F w - (d : ℝ)) := by
    intro w hw
    rw [map_mul, map_sub, map_sub, map_ratCast, map_ratCast, hFr w hw]
  have hneg : InfinitePlace.embedding_of_isReal hu₀ ((θ - (c : k)) * (θ - (d : k))) < 0 := by
    rw [hval u₀ hu₀]
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hy0 : (θ - (c : k)) * (θ - (d : k)) ≠ 0 := by
    intro h
    rw [h, map_zero] at hneg
    exact lt_irrefl 0 hneg
  refine ⟨Units.mk0 _ hy0, ?_, ?_⟩
  · simpa only [Units.val_mk0] using hneg
  · intro v hv hvne
    simp only [Units.val_mk0, hval v hv]
    have hdist := hδle v hv hvne
    rcases le_or_gt (F v) (F u₀) with hle | hlt
    · rw [abs_of_nonpos (by linarith)] at hdist
      exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    · rw [abs_of_pos (by linarith)] at hdist
      exact mul_pos (by linarith) (by linarith)

end Single

/-! ### Realizing an arbitrary pattern of signs -/

section Pattern

/-- **Every pattern of signs at the real places of a number field is realized by a unit:** for a
finite set `S` of infinite places there is a unit which is positive at exactly the real places
outside `S`. -/
theorem exists_units_pos_iff_notMem (k : Type*) [Field k] [NumberField k]
    (S : Finset (InfinitePlace k)) :
    ∃ a : kˣ, ∀ (u : InfinitePlace k) (hu : u.IsReal),
      (0 < InfinitePlace.embedding_of_isReal hu (a : k) ↔ u ∉ S) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun u hu => by simp⟩
  | insert u₀ S hu₀S ih =>
    obtain ⟨a, ha⟩ := ih
    by_cases hr : u₀.IsReal
    · obtain ⟨b, hbneg, hbpos⟩ := exists_units_neg_at k hr
      refine ⟨a * b, fun u hu => ?_⟩
      have hane : InfinitePlace.embedding_of_isReal hu (a : k) ≠ 0 := (map_ne_zero _).mpr a.ne_zero
      have hbne : InfinitePlace.embedding_of_isReal hu (b : k) ≠ 0 := (map_ne_zero _).mpr b.ne_zero
      rw [Units.val_mul, map_mul, pos_mul_iff_of_ne_zero hane hbne, ha u hu, Finset.mem_insert]
      by_cases huu : u = u₀
      · subst huu
        simp only [true_or, not_true, iff_false]
        intro h
        exact absurd (h.mp hu₀S) (asymm hbneg)
      · simp only [hbpos u hu huu, iff_true, not_or]
        exact ⟨fun h => ⟨huu, h⟩, fun h => h.2⟩
    · refine ⟨a, fun u hu => ?_⟩
      have huu : u ≠ u₀ := fun h => hr (h ▸ hu)
      rw [ha u hu, Finset.mem_insert]
      simp only [not_or]
      exact ⟨fun h => ⟨huu, h⟩, fun h => h.2⟩

/-- **Every pattern of signs at the real places of a number field is realized by a unit,** stated
for an arbitrary set of infinite places. -/
theorem exists_units_pos_iff_notMem_set (k : Type*) [Field k] [NumberField k]
    (S : Set (InfinitePlace k)) :
    ∃ a : kˣ, ∀ (u : InfinitePlace k) (hu : u.IsReal),
      (0 < InfinitePlace.embedding_of_isReal hu (a : k) ↔ u ∉ S) := by
  classical
  obtain ⟨a, ha⟩ := exists_units_pos_iff_notMem k S.toFinset
  exact ⟨a, fun u hu => (ha u hu).trans (by simp)⟩

end Pattern

end InverseGalois.NumberTheory
