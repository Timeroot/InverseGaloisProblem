import Mathlib
import InverseGalois.CFT.Global.DiagForm
import InverseGalois.CFT.Global.QuaternaryForms

/-!
# Splitting a diagonal form into a binary head and a tail

A diagonal quadratic form in at least three variables is isotropic exactly when its first two
coefficients and its remaining ones represent a common nonzero value.  This file proves that
dichotomy over an arbitrary field of characteristic other than two, together with the companion
statement that adjoining a variable with coefficient `-c` to a form makes it isotropic exactly
when the original form represents `c`.

## Main results

* `InverseGalois.CFT.Local.sum_univ_add_two`: a sum over `Fin (n + 3)` with its first two terms
  split off.
* `InverseGalois.CFT.Local.isDiagIsotropic_split`: a diagonal form in at least three variables is
  isotropic if and only if its binary head and its tail represent a common nonzero value.
* `InverseGalois.CFT.Local.exists_repr_of_isDiagIsotropic_cons`: adjoining the coefficient `-c` to
  a form with invertible coefficients yields an isotropic form only if the original form
  represents `c`.
-/

namespace InverseGalois.CFT.Local

variable {K : Type*} [Field K]

/-- A sum over `Fin (n + 3)` with its first two terms split off. -/
theorem sum_univ_add_two {n : ℕ} (f : Fin (n + 3) → K) :
    ∑ i, f i = f 0 + f 1 + ∑ i : Fin (n + 1), f i.succ.succ := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.succ_zero_eq_one]
  ring

/-- Negating every coefficient of a diagonal form negates its values. -/
theorem sum_neg_coeff {n : ℕ} (b : Fin n → K) (v : Fin n → K) :
    ∑ i, -(b i) * v i ^ 2 = -∑ i, b i * v i ^ 2 := by
  simp only [neg_mul]
  exact Finset.sum_neg_distrib (f := fun i => b i * v i ^ 2)

/-- **A diagonal form in at least three variables splits as a binary head and a tail sharing a
value.**  The form is isotropic exactly when its first two coefficients and its remaining ones
represent a common nonzero value. -/
theorem isDiagIsotropic_split (h2 : (2 : K) ≠ 0) {n : ℕ} {a : Fin (n + 3) → K}
    (ha : ∀ i, a i ≠ 0) :
    IsDiagIsotropic a ↔ ∃ t : K, t ≠ 0 ∧ (∃ y z : K, t = a 0 * y ^ 2 + a 1 * z ^ 2) ∧
      ∃ w : Fin (n + 1) → K, t = ∑ i, -(a i.succ.succ) * w i ^ 2 := by
  constructor
  · rintro ⟨x, hx, hsum⟩
    rw [sum_univ_add_two] at hsum
    by_cases ht : a 0 * x 0 ^ 2 + a 1 * x 1 ^ 2 = 0
    · rw [ht, zero_add] at hsum
      by_cases hx01 : x 0 = 0 ∧ x 1 = 0
      · have hxt : (fun i : Fin (n + 1) => x i.succ.succ) ≠ 0 := by
          intro hc
          refine hx (funext fun i => ?_)
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
          · simpa using hx01.1
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
            · rw [Fin.succ_zero_eq_one]
              simpa using hx01.2
            · simpa using congrFun hc k
        have hiso : IsDiagIsotropic fun i : Fin (n + 1) => -(a i.succ.succ) := by
          refine ⟨fun i => x i.succ.succ, hxt, ?_⟩
          rw [sum_neg_coeff, hsum, neg_zero]
        refine ⟨a 0, ha 0, ⟨1, 0, by ring⟩, ?_⟩
        exact exists_repr_of_isDiagIsotropic h2 (fun i => neg_ne_zero.2 (ha _)) hiso (a 0)
      · refine ⟨-(a (Fin.succ (Fin.succ (0 : Fin (n + 1))))), neg_ne_zero.2 (ha _), ?_, ?_⟩
        · exact exists_repr_of_binary_isotropic h2 (ha 0) (ha 1) hx01 ht _
        · refine ⟨Pi.single 0 1, ?_⟩
          rw [Finset.sum_eq_single (0 : Fin (n + 1))]
          · simp
          · intro b _ hb
            rw [Pi.single_eq_of_ne hb]
            ring
          · intro hb
            exact absurd (Finset.mem_univ (0 : Fin (n + 1))) hb
    · refine ⟨_, ht, ⟨x 0, x 1, rfl⟩, fun i => x i.succ.succ, ?_⟩
      rw [sum_neg_coeff]
      linear_combination hsum
  · rintro ⟨t, ht, ⟨y, z, hyz⟩, w, hw⟩
    have e0 : (Fin.cons y (Fin.cons z w) : Fin (n + 3) → K) 0 = y := Fin.cons_zero _ _
    have e1 : (Fin.cons y (Fin.cons z w) : Fin (n + 3) → K) 1 = z := by
      rw [← Fin.succ_zero_eq_one, Fin.cons_succ, Fin.cons_zero]
    have e2 : ∀ i : Fin (n + 1),
        (Fin.cons y (Fin.cons z w) : Fin (n + 3) → K) i.succ.succ = w i := by
      intro i
      rw [Fin.cons_succ, Fin.cons_succ]
    rw [sum_neg_coeff] at hw
    refine ⟨Fin.cons y (Fin.cons z w), ?_, ?_⟩
    · intro hc
      refine ht ?_
      have hy : y = 0 := by
        rw [← e0, hc]
        rfl
      have hz : z = 0 := by
        rw [← e1, hc]
        rfl
      rw [hyz, hy, hz]
      ring
    · rw [sum_univ_add_two, e0, e1,
        Finset.sum_congr rfl fun i _ => by rw [e2 i]]
      linear_combination hw - hyz

/-- **Adjoining a variable with coefficient `-c` detects representability of `c`.**  If the
enlarged form is isotropic and all the original coefficients are invertible, the original form
represents `c`. -/
theorem exists_repr_of_isDiagIsotropic_cons (h2 : (2 : K) ≠ 0) {n : ℕ} {c : K} {b : Fin n → K}
    (hb : ∀ i, b i ≠ 0) (h : IsDiagIsotropic (Fin.cons (-c) b)) :
    ∃ w : Fin n → K, c = ∑ i, b i * w i ^ 2 := by
  obtain ⟨x, hx, hsum⟩ := h
  rw [Fin.sum_univ_succ] at hsum
  simp only [Fin.cons_zero, Fin.cons_succ] at hsum
  by_cases h0 : x 0 = 0
  · have hiso : IsDiagIsotropic b := by
      refine ⟨fun i => x i.succ, ?_, ?_⟩
      · intro hc
        refine hx (funext fun i => ?_)
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · simpa using h0
        · simpa using congrFun hc j
      · rw [h0] at hsum
        linear_combination hsum
    exact exists_repr_of_isDiagIsotropic h2 hb hiso c
  · refine ⟨fun i => x i.succ / x 0, ?_⟩
    have hdiv : ∑ i, b i * (x i.succ / x 0) ^ 2 = (∑ i, b i * x i.succ ^ 2) / x 0 ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by field_simp
    have hS : ∑ i, b i * x i.succ ^ 2 = c * x 0 ^ 2 := by linear_combination hsum
    rw [hdiv, hS]
    field_simp

end InverseGalois.CFT.Local
