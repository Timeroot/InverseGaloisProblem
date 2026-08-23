import Mathlib
import InverseGalois.CFT.Global.DiagHasse

/-!
# Representation of a rational number by a diagonal form

The Hasse principle for isotropy of a diagonal quadratic form is here freed of its hypothesis
that the coefficients be invertible, and recast as a Hasse principle for the representation of a
prescribed rational number: a diagonal form represents a rational number over the rational field
as soon as it does so over the real field and over every field of `p`-adic numbers.

## Main results

* `InverseGalois.CFT.isDiagIsotropic_rat_iff`: the Hasse principle for isotropy of an arbitrary
  diagonal form.
* `InverseGalois.CFT.exists_repr_rat_iff`: the Hasse principle for the representation of a
  rational number by a diagonal form.
-/

namespace InverseGalois.CFT.Local

variable {L : Type*} [DivisionRing L]

/-- A coefficient family with a value adjoined, read in an extension of the rational field. -/
theorem cast_cons {n : ℕ} (q : ℚ) (c : Fin n → ℚ) :
    (fun i => (((Fin.cons q c : Fin (n + 1) → ℚ) i : ℚ) : L))
      = Fin.cons ((q : L)) fun j => ((c j : L)) := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp
  · simp

end InverseGalois.CFT.Local

namespace InverseGalois.CFT

open Local

/-- The value of a diagonal form at a rational point, read in an extension of the rational
field. -/
theorem cast_sum_sq {L : Type*} [Field L] [CharZero L] {n : ℕ} (a x : Fin n → ℚ) :
    (((∑ i, a i * x i ^ 2 : ℚ)) : L) = ∑ i, ((a i : L)) * ((x i : L)) ^ 2 := by
  push_cast
  rfl

/-- A diagonal form one of whose coefficients vanishes is isotropic. -/
theorem isDiagIsotropic_of_coeff_eq_zero {K : Type*} [Field K] {n : ℕ} {a : Fin n → K} {i : Fin n}
    (hi : a i = 0) : IsDiagIsotropic a := by
  classical
  refine ⟨(Pi.single i 1 : Fin n → K), ?_, ?_⟩
  · intro hc
    have h1 : (Pi.single i 1 : Fin n → K) i = 0 := by rw [hc]; rfl
    rw [Pi.single_eq_same] at h1
    exact one_ne_zero h1
  · rw [Finset.sum_eq_single i]
    · rw [hi, zero_mul]
    · intro b _ hb
      rw [show (Pi.single i 1 : Fin n → K) b = 0 from Pi.single_eq_of_ne hb 1]
      ring
    · intro hb
      exact absurd (Finset.mem_univ i) hb

/-- **The Hasse principle for the isotropy of a diagonal quadratic form.**  No hypothesis is made
on the coefficients. -/
theorem isDiagIsotropic_rat_iff {n : ℕ} (a : Fin n → ℚ) :
    IsDiagIsotropic a ↔ (∀ p : Nat.Primes, IsDiagIsotropic fun i => ((a i : ℚ_[(p : ℕ)]))) ∧
      IsDiagIsotropic fun i => ((a i : ℝ)) := by
  refine ⟨fun h => ⟨fun p => h.map (Rat.castHom ℚ_[(p : ℕ)]), h.map (Rat.castHom ℝ)⟩, fun h => ?_⟩
  by_cases ha : ∀ i, a i ≠ 0
  · exact isDiagIsotropic_rat_of_forall_local n a ha h.1 h.2
  · push_neg at ha
    obtain ⟨i, hi⟩ := ha
    exact isDiagIsotropic_of_coeff_eq_zero hi

/-- **The Hasse principle for the representation of a rational number by a diagonal form.**  A
diagonal form with invertible coefficients represents a rational number over the rational field
as soon as it represents it over the real field and over every field of `p`-adic numbers. -/
theorem exists_repr_rat_iff {n : ℕ} {a : Fin n → ℚ} (ha : ∀ i, a i ≠ 0) (s : ℚ) :
    (∃ x : Fin n → ℚ, s = ∑ i, a i * x i ^ 2) ↔
      (∀ p : Nat.Primes, ∃ x : Fin n → ℚ_[(p : ℕ)],
          ((s : ℚ_[(p : ℕ)])) = ∑ i, ((a i : ℚ_[(p : ℕ)])) * x i ^ 2) ∧
        ∃ x : Fin n → ℝ, ((s : ℝ)) = ∑ i, ((a i : ℝ)) * x i ^ 2 := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun p => ⟨fun i => ((x i : ℚ_[(p : ℕ)])), ?_⟩, ⟨fun i => ((x i : ℝ)), ?_⟩⟩
    · rw [← cast_sum_sq a x, ← hx]
    · rw [← cast_sum_sq a x, ← hx]
  · rintro ⟨hp, hr⟩
    rcases eq_or_ne s 0 with rfl | hs
    · exact ⟨0, by simp⟩
    have hb : ∀ i, (Fin.cons (-s) a : Fin (n + 1) → ℚ) i ≠ 0 := by
      intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · rw [Fin.cons_zero]
        exact neg_ne_zero.2 hs
      · rw [Fin.cons_succ]
        exact ha j
    have hbloc : ∀ p : Nat.Primes,
        IsDiagIsotropic fun i => (((Fin.cons (-s) a : Fin (n + 1) → ℚ) i : ℚ_[(p : ℕ)])) := by
      intro p
      rw [cast_cons, Rat.cast_neg]
      obtain ⟨x, hx⟩ := hp p
      exact isDiagIsotropic_cons_of_repr hx
    have hbreal : IsDiagIsotropic fun i => (((Fin.cons (-s) a : Fin (n + 1) → ℚ) i : ℝ)) := by
      rw [cast_cons, Rat.cast_neg]
      obtain ⟨x, hx⟩ := hr
      exact isDiagIsotropic_cons_of_repr hx
    have hiso := isDiagIsotropic_rat_of_forall_local (n + 1) _ hb hbloc hbreal
    exact exists_repr_of_isDiagIsotropic_cons (by norm_num) ha hiso

end InverseGalois.CFT
