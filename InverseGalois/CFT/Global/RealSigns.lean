import Mathlib
import InverseGalois.CFT.Global.DiagRepr
import InverseGalois.CFT.Global.OddQuinary

/-!
# The real place, and an explicit criterion in five variables

A diagonal quadratic form over the real field is isotropic exactly when its coefficients are not
all of one sign: if they are all positive the value of the form at a nonzero point is a sum of
nonnegative terms one of which is positive, while a positive and a negative coefficient are made
to cancel by the square roots of one another's absolute values.

Together with the Hasse principle and the fact that at an odd finite place a form in five or more
variables is always isotropic, this leaves a criterion in which only one place is not decided by
inspection: a diagonal form over the rational field in at least five variables is isotropic
exactly when its coefficients are not all of one sign and it is isotropic over the dyadic field.

## Main results

* `InverseGalois.CFT.Local.isDiagIsotropic_of_two`: two coefficients suffice to witness isotropy.
* `InverseGalois.CFT.Local.isDiagIsotropic_neg_iff`: negating every coefficient does not change
  isotropy.
* `InverseGalois.CFT.not_isDiagIsotropic_of_pos`: a form with positive real coefficients is
  anisotropic.
* `InverseGalois.CFT.isDiagIsotropic_real_iff`: a diagonal real form is isotropic exactly when its
  coefficients are not all of one sign.
* `InverseGalois.CFT.exists_repr_real_iff`: a diagonal real form represents a nonzero number
  exactly when one of its coefficients shares that number's sign.
* `InverseGalois.CFT.isDiagIsotropic_rat_iff_signs`: the Hasse principle in at least five
  variables, with the condition at the real place made explicit.
* `InverseGalois.CFT.exists_repr_rat_iff_signs`: the same for the representation of a nonzero
  rational number by a form in at least four variables.
-/

namespace InverseGalois.CFT.Local

variable {K : Type*} [Field K]

/-- **Two coefficients suffice to witness isotropy.**  The remaining variables are set to zero. -/
theorem isDiagIsotropic_of_two {n : ℕ} {b : Fin n → K} {i j : Fin n} (hij : i ≠ j) {x y : K}
    (hne : ¬(x = 0 ∧ y = 0)) (h : b i * x ^ 2 + b j * y ^ 2 = 0) : IsDiagIsotropic b := by
  classical
  refine ⟨fun l => if l = i then x else if l = j then y else 0, ?_, ?_⟩
  · intro hc
    refine hne ⟨?_, ?_⟩
    · have := congrFun hc i
      simpa using this
    · have := congrFun hc j
      simpa [hij.symm] using this
  · have hzero : ∀ l ∈ Finset.univ, l ∉ ({i, j} : Finset (Fin n)) →
        b l * (if l = i then x else if l = j then y else 0) ^ 2 = 0 := by
      intro l _ hl
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      rw [if_neg hl.1, if_neg hl.2]
      ring
    rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin n))) hzero,
      Finset.sum_insert (by simpa using hij), Finset.sum_singleton, if_pos rfl,
      if_neg hij.symm, if_pos rfl]
    exact h

/-- **Negating every coefficient does not change isotropy**, the value of the form at a point
being negated with it. -/
theorem isDiagIsotropic_neg_iff {n : ℕ} {a : Fin n → K} :
    IsDiagIsotropic (fun i => -(a i)) ↔ IsDiagIsotropic a := by
  have key : ∀ b : Fin n → K, IsDiagIsotropic (fun i => -(b i)) → IsDiagIsotropic b := by
    intro b h
    obtain ⟨x, hx, hsum⟩ := h
    refine ⟨x, hx, ?_⟩
    have hneg : -∑ i, b i * x i ^ 2 = 0 := by
      rw [← hsum]
      simp [neg_mul, Finset.sum_neg_distrib]
    exact neg_eq_zero.mp hneg
  refine ⟨key a, fun h => key _ ?_⟩
  simpa using h

end InverseGalois.CFT.Local

namespace InverseGalois.CFT

open Local

/-- **A form with positive real coefficients is anisotropic.**  Its value at a point is a sum of
nonnegative terms, so it vanishes only where every variable does. -/
theorem not_isDiagIsotropic_of_pos {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    ¬ IsDiagIsotropic a := by
  rintro ⟨x, hx, hsum⟩
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ a i * x i ^ 2 :=
    fun i _ => mul_nonneg (ha i).le (sq_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  refine hx (funext fun i => ?_)
  show x i = 0
  have h := hzero i (Finset.mem_univ i)
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' (ha i).ne'
  · exact sq_eq_zero_iff.mp h'

/-- **A diagonal real form is isotropic exactly when its coefficients are not all of one sign.**
A positive and a negative coefficient cancel at the square roots of one another's absolute
values. -/
theorem isDiagIsotropic_real_iff {n : ℕ} (a : Fin n → ℝ) :
    IsDiagIsotropic a ↔ (∃ i, a i = 0) ∨ ∃ i j, a i < 0 ∧ 0 < a j := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨hz, hmix⟩ := hcon
    by_cases hneg : ∃ i, a i < 0
    · obtain ⟨i, hi⟩ := hneg
      refine not_isDiagIsotropic_of_pos (a := fun j => -(a j)) (fun j => ?_) ?_
      · have := hmix i j hi
        rcases lt_trichotomy (a j) 0 with hj | hj | hj
        · linarith
        · exact absurd hj (hz j)
        · linarith
      · exact isDiagIsotropic_neg_iff.mpr h
    · push_neg at hneg
      refine not_isDiagIsotropic_of_pos (a := a) (fun j => ?_) h
      exact lt_of_le_of_ne (hneg j) (Ne.symm (hz j))
  · rintro (⟨i, hi⟩ | ⟨i, j, hi, hj⟩)
    · exact isDiagIsotropic_of_coeff_eq_zero hi
    · have hij : i ≠ j := by
        rintro rfl
        linarith
      refine isDiagIsotropic_of_two hij (x := Real.sqrt (a j)) (y := Real.sqrt (-(a i))) ?_ ?_
      · rintro ⟨h1, -⟩
        exact absurd h1 (Real.sqrt_pos.mpr hj).ne'
      · rw [Real.sq_sqrt hj.le, Real.sq_sqrt (by linarith : (0:ℝ) ≤ -(a i))]
        ring

/-- **A diagonal real form represents a nonzero number exactly when some coefficient shares its
sign.**  That coefficient alone represents the number, at the square root of their quotient. -/
theorem exists_repr_real_iff {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, a i ≠ 0) {s : ℝ} (hs : s ≠ 0) :
    (∃ x : Fin n → ℝ, s = ∑ i, a i * x i ^ 2) ↔ ∃ i, 0 < a i * s := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    by_contra hcon
    push_neg at hcon
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · have hpos' : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ a i * x i ^ 2 := by
        intro i _
        have h1 : 0 < a i := by
          rcases lt_or_gt_of_ne (ha i) with h | h
          · nlinarith [hcon i]
          · exact h
        positivity
      have := Finset.sum_nonneg hpos'
      linarith [hx ▸ this]
    · have hnonpos : ∀ i ∈ (Finset.univ : Finset (Fin n)), a i * x i ^ 2 ≤ 0 := by
        intro i _
        have h1 : a i < 0 := by
          rcases lt_or_gt_of_ne (ha i) with h | h
          · exact h
          · nlinarith [hcon i]
        nlinarith [sq_nonneg (x i)]
      have := Finset.sum_nonpos hnonpos
      linarith [hx ▸ this]
  · rintro ⟨i, hi⟩
    have hai : a i ≠ 0 := ha i
    have hquot : 0 < s / a i := by
      rcases lt_or_gt_of_ne (ha i) with h | h
      · have : s < 0 := by nlinarith
        exact div_pos_of_neg_of_neg this h
      · have : 0 < s := by nlinarith
        exact div_pos this h
    refine ⟨(Pi.single i (Real.sqrt (s / a i)) : Fin n → ℝ), ?_⟩
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, Real.sq_sqrt hquot.le]
      field_simp
    · intro b _ hb
      rw [show (Pi.single i (Real.sqrt (s / a i)) : Fin n → ℝ) b = 0 from
        Pi.single_eq_of_ne hb _]
      ring
    · intro hb
      exact absurd (Finset.mem_univ i) hb

/-- **Representation in four or more variables, with the real condition made explicit.**  A
diagonal form over the rational field in at least four variables, with invertible coefficients,
represents a nonzero rational number exactly when one of its coefficients shares that number's
sign and it represents the number over the dyadic field. -/
theorem exists_repr_rat_iff_signs {n : ℕ} (hn : 4 ≤ n) {a : Fin n → ℚ} (ha : ∀ i, a i ≠ 0)
    {s : ℚ} (hs : s ≠ 0) :
    (∃ x : Fin n → ℚ, s = ∑ i, a i * x i ^ 2) ↔ (∃ i, 0 < a i * s) ∧
      ∃ x : Fin n → ℚ_[2], ((s : ℚ_[2])) = ∑ i, ((a i : ℚ_[2])) * x i ^ 2 := by
  have hR : ∀ i, ((a i : ℝ)) ≠ 0 := fun i => by exact_mod_cast ha i
  have hsR : ((s : ℝ)) ≠ 0 := by exact_mod_cast hs
  have hcast : (∃ i, 0 < ((a i : ℝ)) * ((s : ℝ))) ↔ ∃ i, 0 < a i * s := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by exact_mod_cast hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by exact_mod_cast hi⟩
  rw [exists_repr_rat_iff_two_real hn ha s, exists_repr_real_iff hR hsR, hcast, and_comm]

/-- **The Hasse principle in five or more variables, with the real condition made explicit.**  A
diagonal form over the rational field in at least five variables is isotropic exactly when its
coefficients are not all of one sign and it is isotropic over the dyadic field. -/
theorem isDiagIsotropic_rat_iff_signs {n : ℕ} (hn : 5 ≤ n) (a : Fin n → ℚ) :
    IsDiagIsotropic a ↔ ((∃ i, a i = 0) ∨ ∃ i j, a i < 0 ∧ 0 < a j) ∧
      IsDiagIsotropic fun i => ((a i : ℚ_[2])) := by
  rw [isDiagIsotropic_rat_iff_two_real hn, isDiagIsotropic_real_iff]
  have hcast : ((∃ i, ((a i : ℝ)) = 0) ∨ ∃ i j, ((a i : ℝ)) < 0 ∧ 0 < ((a j : ℝ))) ↔
      ((∃ i, a i = 0) ∨ ∃ i j, a i < 0 ∧ 0 < a j) := by
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, j, hi, hj⟩)
      · exact Or.inl ⟨i, by exact_mod_cast hi⟩
      · exact Or.inr ⟨i, j, by exact_mod_cast hi, by exact_mod_cast hj⟩
    · rintro (⟨i, hi⟩ | ⟨i, j, hi, hj⟩)
      · exact Or.inl ⟨i, by exact_mod_cast hi⟩
      · exact Or.inr ⟨i, j, by exact_mod_cast hi, by exact_mod_cast hj⟩
  rw [hcast, and_comm]

end InverseGalois.CFT
