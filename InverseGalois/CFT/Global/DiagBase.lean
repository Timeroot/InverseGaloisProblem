import Mathlib
import InverseGalois.CFT.Global.DiagForm
import InverseGalois.CFT.Global.LocalSquares
import InverseGalois.CFT.Global.TernaryForms
import InverseGalois.CFT.Global.QuaternaryForms

/-!
# The Hasse principle for diagonal forms in at most four variables

The predicate `IsDiagIsotropic` records isotropy of a diagonal quadratic form presented by a
family of coefficients indexed by `Fin n`, whereas the Hasse principle has been established for
forms written out variable by variable: as a square class in two variables, as a conic in three,
and as a pair of binary forms sharing a value in four.  This file supplies the dictionary between
the two presentations in each of those arities and then transports the known global statements
across it, obtaining the Hasse principle for a family of at most four coefficients.

The two extreme arities are degenerate: a form in no variables and a form in one variable with
invertible coefficient are anisotropic over every field, so for them the hypothesis at the real
place is already contradictory.

## Main results

* `InverseGalois.CFT.Local.isDiagIsotropic_two_iff`: a diagonal binary form with invertible
  coefficients is isotropic exactly when minus the product of its coefficients is a square.
* `InverseGalois.CFT.Local.isDiagIsotropic_three_iff`: the `Fin 3`-indexed predicate agrees with
  `IsTernaryIsotropic`.
* `InverseGalois.CFT.Local.isDiagIsotropic_four_iff`: the `Fin 4`-indexed predicate agrees with
  `IsQuaternaryIsotropic`.
* `InverseGalois.CFT.isDiagIsotropic_rat_of_forall_local_of_le_four`: **the Hasse principle for a
  diagonal form over the rational field in at most four variables.**
-/

namespace InverseGalois.CFT.Local

variable {K : Type*} [Field K]

/-- **A diagonal binary form with invertible coefficients is isotropic exactly when minus the
product of its coefficients is a square.**  A nontrivial zero has both coordinates nonzero, and
their ratio scaled by the leading coefficient is the square root sought. -/
theorem isDiagIsotropic_two_iff {a : Fin 2 → K} (ha : ∀ i, a i ≠ 0) :
    IsDiagIsotropic a ↔ IsSquare (-(a 0 * a 1)) := by
  constructor
  · rintro ⟨x, hx, hsum⟩
    rw [Fin.sum_univ_two] at hsum
    have hx1 : x 1 ≠ 0 := by
      intro h1
      have hx0 : x 0 = 0 := by
        have : a 0 * x 0 ^ 2 = 0 := by
          rw [h1] at hsum
          simpa using hsum
        exact sq_eq_zero_iff.1 ((mul_eq_zero.1 this).resolve_left (ha 0))
      refine hx (funext fun i => ?_)
      fin_cases i <;> simpa using ‹_›
    refine ⟨a 0 * x 0 / x 1, ?_⟩
    field_simp
    linear_combination (-(a 0)) * hsum
  · rintro ⟨s, hs⟩
    refine ⟨![s, a 0], ?_, ?_⟩
    · intro h
      exact ha 0 (by simpa using congrFun h 1)
    · rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (-(a 0)) * hs

/-- **The `Fin 3`-indexed isotropy predicate is the ternary one.** -/
theorem isDiagIsotropic_three_iff {a : Fin 3 → K} :
    IsDiagIsotropic a ↔ IsTernaryIsotropic (a 0) (a 1) (a 2) := by
  constructor
  · rintro ⟨x, hx, hsum⟩
    rw [Fin.sum_univ_three] at hsum
    refine ⟨x 0, x 1, x 2, ?_, hsum⟩
    rintro ⟨h0, h1, h2⟩
    exact hx (funext fun i => by fin_cases i <;> assumption)
  · rintro ⟨x, y, z, hne, hsum⟩
    refine ⟨![x, y, z], ?_, ?_⟩
    · intro h
      exact hne ⟨by simpa using congrFun h 0, by simpa using congrFun h 1,
        by simpa using congrFun h 2⟩
    · rw [Fin.sum_univ_three]
      simpa using hsum

/-- **The `Fin 4`-indexed isotropy predicate is the quaternary one.** -/
theorem isDiagIsotropic_four_iff {a : Fin 4 → K} :
    IsDiagIsotropic a ↔ IsQuaternaryIsotropic (a 0) (a 1) (a 2) (a 3) := by
  constructor
  · rintro ⟨x, hx, hsum⟩
    rw [Fin.sum_univ_four] at hsum
    refine ⟨x 0, x 1, x 2, x 3, ?_, hsum⟩
    rintro ⟨h0, h1, h2, h3⟩
    exact hx (funext fun i => by fin_cases i <;> assumption)
  · rintro ⟨x, y, z, w, hne, hsum⟩
    refine ⟨![x, y, z, w], ?_, ?_⟩
    · intro h
      exact hne ⟨by simpa using congrFun h 0, by simpa using congrFun h 1,
        by simpa using congrFun h 2, by simpa using congrFun h 3⟩
    · rw [Fin.sum_univ_four]
      simpa using hsum

end InverseGalois.CFT.Local

namespace InverseGalois.CFT

open Local

/-- **The Hasse principle for a diagonal binary form over the rational field.** -/
theorem isDiagIsotropic_rat_two_of_forall_local {a : Fin 2 → ℚ} (ha : ∀ i, a i ≠ 0)
    (hloc : ∀ p : Nat.Primes, IsDiagIsotropic fun i => ((a i : ℚ_[(p : ℕ)]))) :
    IsDiagIsotropic a := by
  rw [isDiagIsotropic_two_iff ha]
  refine isSquare_of_forall_isSquare_padic fun p => ?_
  have hap : ∀ i, ((a i : ℚ_[(p : ℕ)])) ≠ 0 := fun i => by
    simpa using ha i
  have h := (isDiagIsotropic_two_iff hap).1 (hloc p)
  push_cast
  exact h

/-- **The Hasse principle for a diagonal ternary form over the rational field**, in the
`Fin 3`-indexed presentation. -/
theorem isDiagIsotropic_rat_three_of_forall_local {a : Fin 3 → ℚ} (ha : ∀ i, a i ≠ 0)
    (hloc : ∀ p : Nat.Primes, IsDiagIsotropic fun i => ((a i : ℚ_[(p : ℕ)]))) :
    IsDiagIsotropic a := by
  rw [isDiagIsotropic_three_iff]
  refine isTernaryIsotropic_rat_of_forall_local (ha 0) (ha 1) (ha 2) fun p => ?_
  exact isDiagIsotropic_three_iff.1 (hloc p)

/-- **The Hasse principle for a diagonal quaternary form over the rational field**, in the
`Fin 4`-indexed presentation.  The real place is a genuine hypothesis here. -/
theorem isDiagIsotropic_rat_four_of_forall_local {a : Fin 4 → ℚ} (ha : ∀ i, a i ≠ 0)
    (hloc : ∀ p : Nat.Primes, IsDiagIsotropic fun i => ((a i : ℚ_[(p : ℕ)])))
    (hreal : IsDiagIsotropic fun i => ((a i : ℝ))) :
    IsDiagIsotropic a := by
  rw [isDiagIsotropic_four_iff]
  refine isQuaternaryIsotropic_rat_of_forall_local (ha 0) (ha 1) (ha 2) (ha 3)
    (fun p => isDiagIsotropic_four_iff.1 (hloc p)) ?_
  exact isDiagIsotropic_four_iff.1 hreal

/-- **The Hasse principle for a diagonal form over the rational field in at most four
variables.**  A form with invertible rational coefficients that has a nontrivial zero over every
field of `p`-adic numbers and over the real field has a nontrivial rational zero. -/
theorem isDiagIsotropic_rat_of_forall_local_of_le_four {n : ℕ} (hn : n ≤ 4) {a : Fin n → ℚ}
    (ha : ∀ i, a i ≠ 0)
    (hloc : ∀ p : Nat.Primes, IsDiagIsotropic fun i => ((a i : ℚ_[(p : ℕ)])))
    (hreal : IsDiagIsotropic fun i => ((a i : ℝ))) :
    IsDiagIsotropic a := by
  interval_cases n
  · exact absurd hreal (not_isDiagIsotropic_zero _)
  · exact absurd hreal (not_isDiagIsotropic_one fun i => by simpa using ha i)
  · exact isDiagIsotropic_rat_two_of_forall_local ha hloc
  · exact isDiagIsotropic_rat_three_of_forall_local ha hloc
  · exact isDiagIsotropic_rat_four_of_forall_local ha hloc hreal

end InverseGalois.CFT
