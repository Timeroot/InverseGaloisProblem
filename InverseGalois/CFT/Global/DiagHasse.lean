import Mathlib
import InverseGalois.CFT.Global.DiagBase
import InverseGalois.CFT.Global.DiagSplit
import InverseGalois.CFT.Global.QuinaryForms

/-!
# The Hasse principle for diagonal forms in any number of variables

A diagonal quadratic form over the rational field with invertible coefficients represents zero
nontrivially as soon as it does so over the real field and over every field of `p`-adic numbers.
The proof is an induction on the number of variables: the forms in at most four variables are
already settled, and a form in at least five variables is split into a binary head and a tail,
a rational value shared by the two halves is produced from the local ones, and the induction
hypothesis is applied to the tail enlarged by that value.

## Main results

* `InverseGalois.CFT.Local.isDiagIsotropic_of_three`: a diagonal form with an isotropic ternary
  subform is isotropic.
* `InverseGalois.CFT.Local.isDiagIsotropic_cons_of_repr`: adjoining the coefficient `-c` to a form
  representing `c` yields an isotropic form.
* `InverseGalois.CFT.isDiagIsotropic_rat_of_forall_local`: the Hasse principle for a diagonal form
  in an arbitrary number of variables.
* `InverseGalois.CFT.isDiagIsotropic_rat_iff_forall_local`: the same statement as an equivalence.
-/

namespace InverseGalois.CFT.Local

variable {K : Type*} [Field K]

/-- **A diagonal form with an isotropic ternary subform is isotropic.**  The isotropic vector of
the subform is extended by zeros. -/
theorem isDiagIsotropic_of_three {n : ℕ} {b : Fin n → K} {i j k : Fin n} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) {x y z : K} (hne : ¬(x = 0 ∧ y = 0 ∧ z = 0))
    (h : b i * x ^ 2 + b j * y ^ 2 + b k * z ^ 2 = 0) : IsDiagIsotropic b := by
  classical
  set v : Fin n → K := fun l => if l = i then x else if l = j then y else if l = k then z else 0
    with hv
  have hvi : v i = x := by
    rw [hv]
    simp
  have hvj : v j = y := by
    rw [hv]
    simp [Ne.symm hij]
  have hvk : v k = z := by
    rw [hv]
    simp [Ne.symm hik, Ne.symm hjk]
  have hvz : ∀ l, l ≠ i → l ≠ j → l ≠ k → v l = 0 := by
    intro l h1 h2 h3
    rw [hv]
    simp [h1, h2, h3]
  have hzero : ∀ l ∈ Finset.univ, l ∉ ({i, j, k} : Finset (Fin n)) → b l * v l ^ 2 = 0 := by
    intro l _ hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    rw [hvz l hl.1 hl.2.1 hl.2.2]
    ring
  have hsum : ∑ l, b l * v l ^ 2 = b i * x ^ 2 + b j * y ^ 2 + b k * z ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ ({i, j, k} : Finset (Fin n))) hzero,
      Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
      Finset.sum_singleton, hvi, hvj, hvk, add_assoc]
  refine ⟨v, ?_, by rw [hsum]; exact h⟩
  intro hcon
  refine hne ⟨?_, ?_, ?_⟩
  · rw [← hvi, hcon]
    rfl
  · rw [← hvj, hcon]
    rfl
  · rw [← hvk, hcon]
    rfl

/-- **Adjoining the coefficient `-c` to a form representing `c` yields an isotropic form.** -/
theorem isDiagIsotropic_cons_of_repr {n : ℕ} {c : K} {b : Fin n → K} {w : Fin n → K}
    (h : c = ∑ i, b i * w i ^ 2) : IsDiagIsotropic (Fin.cons (-c) b) := by
  refine ⟨Fin.cons 1 w, ?_, ?_⟩
  · intro hcon
    have h0 := congrFun hcon 0
    rw [Fin.cons_zero] at h0
    simp at h0
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← h]
    ring

/-- The coefficient family obtained by adjoining `-q` to the negated tail, read in an extension
of the rational field. -/
theorem cast_cons_neg {L : Type*} [DivisionRing L] {n : ℕ} (q : ℚ) (c : Fin n → ℚ) :
    (fun i => (((Fin.cons (-q) (fun j => -(c j)) : Fin (n + 1) → ℚ) i : ℚ) : L))
      = Fin.cons (-((q : ℚ) : L)) (fun j => -(((c j : ℚ)) : L)) := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp
  · simp

end InverseGalois.CFT.Local

namespace InverseGalois.CFT

open Local

/-- Three distinct indices in a type of indices with at least three elements. -/
private theorem three_indices (m : ℕ) :
    (0 : Fin (m + 3)) ≠ Fin.succ (0 : Fin (m + 2)) ∧
      (0 : Fin (m + 3)) ≠ Fin.succ (Fin.succ (0 : Fin (m + 1))) ∧
      Fin.succ (0 : Fin (m + 2)) ≠ Fin.succ (Fin.succ (0 : Fin (m + 1))) := by
  refine ⟨(Fin.succ_ne_zero _).symm, (Fin.succ_ne_zero _).symm, ?_⟩
  intro hc
  exact Fin.succ_ne_zero _ (Fin.succ_injective _ hc).symm

set_option maxHeartbeats 1000000 in
/-- **The two halves of a diagonal form share a rational value.**  Given a nonzero value shared by
the two halves over every completion, with the sign of the first coefficient at the real place,
the halves share a nonzero rational value. -/
private theorem exists_rat_common_value {m : ℕ} {α β : ℚ} (hα : α ≠ 0) (hβ : β ≠ 0)
    {c : Fin (m + 3) → ℚ} (hc : ∀ i, c i ≠ 0)
    (IH : ∀ b : Fin (m + 4) → ℚ, (∀ i, b i ≠ 0) →
      (∀ p : Nat.Primes, IsDiagIsotropic fun i => ((b i : ℚ_[(p : ℕ)]))) →
      (IsDiagIsotropic fun i => ((b i : ℝ))) → IsDiagIsotropic b)
    (t : ∀ p : Nat.Primes, ℚ_[(p : ℕ)]) (ht : ∀ p, t p ≠ 0)
    (htbin : ∀ p : Nat.Primes, ∃ x y : ℚ_[(p : ℕ)],
      t p = ((α : ℚ_[(p : ℕ)])) * x ^ 2 + ((β : ℚ_[(p : ℕ)])) * y ^ 2)
    (httail : ∀ p : Nat.Primes, ∃ w : Fin (m + 3) → ℚ_[(p : ℕ)],
      t p = ∑ i, -((c i : ℚ_[(p : ℕ)])) * w i ^ 2)
    {tr : ℝ} (htr : tr ≠ 0) (hsign : 0 < ((α : ℝ)) * tr)
    (htrtail : ∃ w : Fin (m + 3) → ℝ, tr = ∑ i, -((c i : ℝ)) * w i ^ 2) :
    ∃ q : ℚ, q ≠ 0 ∧ (∃ x y : ℚ, q = α * x ^ 2 + β * y ^ 2) ∧
      ∃ w : Fin (m + 3) → ℚ, q = ∑ i, -(c i) * w i ^ 2 := by
  classical
  obtain ⟨hij, hik, hjk⟩ := three_indices m
  set j₀ : Fin (m + 3) := 0
  set j₁ : Fin (m + 3) := Fin.succ (0 : Fin (m + 2))
  set j₂ : Fin (m + 3) := Fin.succ (Fin.succ (0 : Fin (m + 1)))
  set S : Finset Nat.Primes := insert primeTwo ((finite_setOf_norm_ne_one (hc j₀)).toFinset ∪
    (finite_setOf_norm_ne_one (hc j₁)).toFinset ∪ (finite_setOf_norm_ne_one (hc j₂)).toFinset)
    with hS
  obtain ⟨q, hqsign, hqbin, hqsq⟩ :=
    exists_rat_value_of_local S hα hβ t (fun p _ => ht p) (fun p _ => htbin p)
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hqsign
    exact lt_irrefl 0 hqsign
  set b : Fin (m + 4) → ℚ := Fin.cons (-q) (fun i => -(c i)) with hb
  have hbne : ∀ i, b i ≠ 0 := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rw [hb, Fin.cons_zero]
      exact neg_ne_zero.2 hq0
    · rw [hb, Fin.cons_succ]
      exact neg_ne_zero.2 (hc j)
  have hbloc : ∀ p : Nat.Primes, IsDiagIsotropic fun i => ((b i : ℚ_[(p : ℕ)])) := by
    intro p
    rw [hb, cast_cons_neg]
    by_cases hp : p ∈ S
    · obtain ⟨w', hw'⟩ := exists_repr_of_isSquare_div (ht p) (httail p) (hqsq p hp)
      exact isDiagIsotropic_cons_of_repr hw'
    · have hp2 : ((p : ℕ)) ≠ 2 := by
        intro hcon
        refine hp ?_
        rw [show p = primeTwo from Subtype.ext hcon, hS]
        exact Finset.mem_insert_self _ _
      have h0' : ‖((c j₀ : ℚ_[(p : ℕ)]))‖ = 1 := by
        by_contra hcon
        refine hp ?_
        rw [hS]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_union_left _ (((finite_setOf_norm_ne_one (hc j₀)).mem_toFinset).2 hcon)))
      have h1' : ‖((c j₁ : ℚ_[(p : ℕ)]))‖ = 1 := by
        by_contra hcon
        refine hp ?_
        rw [hS]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_union_right _ (((finite_setOf_norm_ne_one (hc j₁)).mem_toFinset).2 hcon)))
      have h2' : ‖((c j₂ : ℚ_[(p : ℕ)]))‖ = 1 := by
        by_contra hcon
        refine hp ?_
        rw [hS]
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (((finite_setOf_norm_ne_one (hc j₂)).mem_toFinset).2 hcon))
      obtain ⟨x, y, z, hne, h0⟩ := isotropic_ternary_of_norm_one (p := (p : ℕ)) hp2
        (u₁ := -((c j₀ : ℚ_[(p : ℕ)]))) (u₂ := -((c j₁ : ℚ_[(p : ℕ)])))
        (u₃ := -((c j₂ : ℚ_[(p : ℕ)]))) (by rw [norm_neg]; exact h0')
        (by rw [norm_neg]; exact h1') (by rw [norm_neg]; exact h2')
      refine isDiagIsotropic_of_three (i := j₀.succ) (j := j₁.succ) (k := j₂.succ)
        (fun hcon => hij (Fin.succ_injective _ hcon))
        (fun hcon => hik (Fin.succ_injective _ hcon))
        (fun hcon => hjk (Fin.succ_injective _ hcon)) (x := x) (y := y) (z := z) hne ?_
      simp only [Fin.cons_succ]
      exact h0
  have hbreal : IsDiagIsotropic fun i => ((b i : ℝ)) := by
    rw [hb, cast_cons_neg]
    have hprod : 0 < ((α : ℝ)) * ((q : ℝ)) := by exact_mod_cast hqsign
    have hqtr : 0 < ((q : ℝ)) * tr := by nlinarith [mul_pos hprod hsign, sq_nonneg ((α : ℝ))]
    have htr2 : 0 < tr ^ 2 := lt_of_le_of_ne (sq_nonneg tr) (Ne.symm (pow_ne_zero 2 htr))
    have hsq : IsSquare (((q : ℝ)) / tr) := by
      refine (isSquare_real_iff _).2 ?_
      have hrw : ((q : ℝ)) / tr = ((q : ℝ)) * tr / tr ^ 2 := by field_simp
      rw [hrw]
      exact le_of_lt (div_pos hqtr htr2)
    obtain ⟨w, hw⟩ := exists_repr_of_isSquare_div htr htrtail hsq
    exact isDiagIsotropic_cons_of_repr hw
  have hbiso := IH b hbne hbloc hbreal
  refine ⟨q, hq0, hqbin, ?_⟩
  rw [hb] at hbiso
  exact exists_repr_of_isDiagIsotropic_cons (by norm_num) (fun i => neg_ne_zero.2 (hc i)) hbiso

/-- **The Hasse principle for a diagonal quadratic form.**  A diagonal form over the rational
field with invertible coefficients represents zero nontrivially as soon as it does so over the
real field and over every field of `p`-adic numbers. -/
theorem isDiagIsotropic_rat_of_forall_local : ∀ (n : ℕ) (a : Fin n → ℚ), (∀ i, a i ≠ 0) →
    (∀ p : Nat.Primes, IsDiagIsotropic fun i => ((a i : ℚ_[(p : ℕ)]))) →
    (IsDiagIsotropic fun i => ((a i : ℝ))) → IsDiagIsotropic a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro a ha hloc hreal
    by_cases hn : n ≤ 4
    · exact isDiagIsotropic_rat_of_forall_local_of_le_four hn ha hloc hreal
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    set c : Fin (m + 3) → ℚ := fun i => a i.succ.succ
    have hc : ∀ i, c i ≠ 0 := fun i => ha _
    have hsplitℝ := (isDiagIsotropic_split (K := ℝ) (n := m + 2) (by norm_num)
      (fun i => Rat.cast_ne_zero.2 (ha i))).1 hreal
    obtain ⟨tr, htr, htrbin, htrtail⟩ := hsplitℝ
    have hlocsplit : ∀ p : Nat.Primes, ∃ tp : ℚ_[(p : ℕ)], tp ≠ 0 ∧
        (∃ x y : ℚ_[(p : ℕ)], tp = ((a 0 : ℚ_[(p : ℕ)])) * x ^ 2 + ((a 1 : ℚ_[(p : ℕ)])) * y ^ 2) ∧
        ∃ w : Fin (m + 3) → ℚ_[(p : ℕ)], tp = ∑ i, -((c i : ℚ_[(p : ℕ)])) * w i ^ 2 := by
      intro p
      exact (isDiagIsotropic_split (K := ℚ_[(p : ℕ)]) (n := m + 2) (by norm_num)
        (fun i => Rat.cast_ne_zero.2 (ha i))).1 (hloc p)
    choose t ht htbin httail using hlocsplit
    have hIH : ∀ b : Fin (m + 4) → ℚ, (∀ i, b i ≠ 0) →
        (∀ p : Nat.Primes, IsDiagIsotropic fun i => ((b i : ℚ_[(p : ℕ)]))) →
        (IsDiagIsotropic fun i => ((b i : ℝ))) → IsDiagIsotropic b :=
      fun b => IH (m + 4) (by omega) b
    have hsign : 0 < ((a 0 : ℚ) : ℝ) * tr ∨ 0 < ((a 1 : ℚ) : ℝ) * tr := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨y, z, hyz⟩ := htrbin
      have h1 : ((a 0 : ℚ) : ℝ) * tr * y ^ 2 ≤ 0 :=
        mul_nonpos_iff.2 (Or.inr ⟨hcon.1, sq_nonneg y⟩)
      have h2 : ((a 1 : ℚ) : ℝ) * tr * z ^ 2 ≤ 0 :=
        mul_nonpos_iff.2 (Or.inr ⟨hcon.2, sq_nonneg z⟩)
      have htr2 : 0 < tr ^ 2 := lt_of_le_of_ne (sq_nonneg tr) (Ne.symm (pow_ne_zero 2 htr))
      have hsq : tr ^ 2 = ((a 0 : ℚ) : ℝ) * tr * y ^ 2 + ((a 1 : ℚ) : ℝ) * tr * z ^ 2 := by
        linear_combination tr * hyz
      linarith
    refine (isDiagIsotropic_split (K := ℚ) (n := m + 2) (by norm_num) ha).2 ?_
    rcases hsign with hs | hs
    · obtain ⟨q, hq0, hqbin, hqtail⟩ :=
        exists_rat_common_value (ha 0) (ha 1) hc hIH t ht htbin httail htr hs htrtail
      exact ⟨q, hq0, hqbin, hqtail⟩
    · obtain ⟨q, hq0, hqbin, hqtail⟩ :=
        exists_rat_common_value (ha 1) (ha 0) hc hIH t ht
          (fun p => by
            obtain ⟨x, y, hxy⟩ := htbin p
            exact ⟨y, x, by linear_combination hxy⟩) httail htr hs htrtail
      refine ⟨q, hq0, ?_, hqtail⟩
      obtain ⟨x, y, hxy⟩ := hqbin
      exact ⟨y, x, by linear_combination hxy⟩

/-- **The Hasse principle for a diagonal quadratic form, as an equivalence.** -/
theorem isDiagIsotropic_rat_iff_forall_local {n : ℕ} {a : Fin n → ℚ} (ha : ∀ i, a i ≠ 0) :
    IsDiagIsotropic a ↔ (∀ p : Nat.Primes, IsDiagIsotropic fun i => ((a i : ℚ_[(p : ℕ)]))) ∧
      IsDiagIsotropic fun i => ((a i : ℝ)) := by
  refine ⟨fun h => ⟨fun p => ?_, ?_⟩, fun h => isDiagIsotropic_rat_of_forall_local n a ha h.1 h.2⟩
  · exact h.map (Rat.castHom ℚ_[(p : ℕ)])
  · exact h.map (Rat.castHom ℝ)

end InverseGalois.CFT
