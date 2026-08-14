/-
# Gram matrix discriminant computation

Given the power sums of 5 elements, compute det(V^T V) = det(Gram matrix)
where V is the Vandermonde matrix.
-/
import Mathlib

open Finset Matrix

noncomputable section


variable {K : Type*} [Field K]

/-- The Gram matrix (V^T V) from power sums. Entries are p_{i+j}. -/
def gramMatrixOfPowerSums (p : ℕ → K) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.of fun i j ↦ p (i.val + j.val)

/-
Vandermonde det squared equals det of the Gram matrix.
-/
lemma vandermonde_det_sq (v : Fin 5 → K) :
    (Matrix.vandermonde v).det ^ 2 =
    (gramMatrixOfPowerSums (fun k => ∑ i : Fin 5, v i ^ k)).det := by
      convert det_mul (vandermonde v).transpose (vandermonde v) using 1
      · rw [det_mul, det_transpose, sq]
      · convert det_mul _ _ using 2
        ext i j
        simp only [gramMatrixOfPowerSums, of_apply, mul_apply, transpose_apply, vandermonde_apply]
        ring_nf

/-
If the power sums have specific values, the Gram matrix determinant is 32000².
-/
lemma gram_det_value (r : Fin 5 → K)
    (hp0 : ∑ i : Fin 5, r i ^ 0 = 5)
    (hp1 : ∑ i : Fin 5, r i ^ 1 = 0)
    (hp2 : ∑ i : Fin 5, r i ^ 2 = 0)
    (hp3 : ∑ i : Fin 5, r i ^ 3 = 0)
    (hp4 : ∑ i : Fin 5, r i ^ 4 = (-80 : K))
    (hp5 : ∑ i : Fin 5, r i ^ 5 = (-80 : K))
    (hp6 : ∑ i : Fin 5, r i ^ 6 = 0)
    (hp7 : ∑ i : Fin 5, r i ^ 7 = 0)
    (hp8 : ∑ i : Fin 5, r i ^ 8 = (1600 : K)) :
    (gramMatrixOfPowerSums (fun k => ∑ i : Fin 5, r i ^ k)).det =
    (32000 : K) ^ 2 := by
      -- Show that the matrix equals the specific matrix.
      have h_matrix : gramMatrixOfPowerSums (fun k ↦ ∑ i, r i ^ k) =
          !![5, 0, 0, 0, -80; 0, 0, 0, -80, -80; 0, 0, -80, -80, 0;
            0, -80, -80, 0, 0; -80, -80, 0, 0, 1600] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp only [gramMatrixOfPowerSums, of_apply, Nat.reduceAdd,
            hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8] <;>
          simp
      simp only [h_matrix, det_succ_row_zero]
      simp [Fin.sum_univ_succ, Fin.succAbove]
      grind

end