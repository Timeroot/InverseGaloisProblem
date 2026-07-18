/-
# Gram matrix discriminant computation

Given the power sums of 5 elements, compute det(V^T V) = det(Gram matrix)
where V is the Vandermonde matrix.
-/
import Mathlib

open Finset Matrix

noncomputable section

set_option maxHeartbeats 3200000

variable {K : Type*} [Field K]

/-- The Gram matrix (V^T V) from power sums. Entries are p_{i+j}. -/
def gramMatrixOfPowerSums (p : ℕ → K) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.of fun i j => p (i.val + j.val)

/-
Vandermonde det squared equals det of the Gram matrix.
-/
lemma vandermonde_det_sq (v : Fin 5 → K) :
    (Matrix.vandermonde v).det ^ 2 =
    (gramMatrixOfPowerSums (fun k => ∑ i : Fin 5, v i ^ k)).det := by
      convert Matrix.det_mul ( Matrix.transpose ( vandermonde v ) ) ( vandermonde v ) using 1;
      · rw [ Matrix.det_mul, Matrix.det_transpose, sq ];
      · convert Matrix.det_mul _ _ using 2;
        ext i j; simp [ Matrix.mul_apply, gramMatrixOfPowerSums ] ; ring;

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
      have h_matrix : gramMatrixOfPowerSums (fun k => ∑ i, r i ^ k) = !![5, 0, 0, 0, -80; 0, 0, 0, -80, -80; 0, 0, -80, -80, 0; 0, -80, -80, 0, 0; -80, -80, 0, 0, 1600] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp_all [ gramMatrixOfPowerSums ] ;
      simp only [h_matrix, det_succ_row_zero];
      simp [ Fin.sum_univ_succ, Fin.succAbove ];
      grind

end