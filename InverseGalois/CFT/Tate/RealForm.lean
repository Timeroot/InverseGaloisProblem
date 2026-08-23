/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Averaging

/-!
# An integral intertwiner from a real one

Two integer matrices `SA` and `SB` of order dividing `n`, invertible over the integers, may happen
to be conjugate over the reals without any conjugating matrix having integer entries.  Nevertheless
an *invertible integer intertwiner* -- an integer matrix `W` with `W * SA = SB * W` and nonzero
determinant -- exists as soon as a real one does.

The proof is a specialisation argument.  Averaging over the cyclic group turns the elementary
matrices into finitely many integer intertwiners `W p`, and every real intertwiner is a real
combination of them: this is `InverseGalois.CFT.nsmul_eq_sum_smul_map_avgMatrix`.  The determinant
of the generic combination `∑ p, X p • W p` is therefore a polynomial with integer coefficients
that does not vanish at the real point given by the entries of the real intertwiner, hence is not
the zero polynomial; and a nonzero polynomial over the integers does not vanish identically on
integer points.  Any integer point where it does not vanish gives the intertwiner.

This is the form in which the invariance of the Herbrand quotient under a change of the ambient
field is used: two lattices whose real representations are isomorphic are isogenous, and so have
the same Herbrand quotient.

## Main definitions

* `InverseGalois.CFT.genericDet`: the determinant of the generic combination of a finite family of
  integer matrices, as a polynomial in one variable per member of the family.

## Main results

* `InverseGalois.CFT.map_genericDet`: the value of that polynomial under a ring homomorphism.
* `InverseGalois.CFT.exists_ne_zero_of_eval_ne_zero`: a polynomial over the integers that is
  nonzero at a real point is nonzero at an integer point.
* `InverseGalois.CFT.exists_intMatrix_intertwine`: **an invertible real intertwiner of two integer
  matrices of finite order produces an invertible integer one.**

## Tags

matrix, cyclic group, averaging, intertwiner, specialisation
-/

namespace InverseGalois.CFT

open Matrix MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]

/-! ### The determinant of a generic combination -/

/-- **The determinant of the generic combination** of a finite family of integer matrices, a
polynomial with one variable for each member of the family. -/
noncomputable def genericDet (W : κ → Matrix ι ι ℤ) : MvPolynomial κ ℤ :=
  (Matrix.of fun i j => ∑ p : κ, X p * C (W p i j)).det

omit [Fintype κ] in
/-- A ring homomorphism out of a polynomial ring over the integers sends a constant to the integer
it names. -/
theorem map_C_int {S : Type*} [CommRing S] (g : MvPolynomial κ ℤ →+* S) (z : ℤ) :
    g (C z) = (z : S) := by
  have h : (C z : MvPolynomial κ ℤ) = (z : MvPolynomial κ ℤ) := by simp
  rw [h, map_intCast]

/-- **The value of the generic determinant** under a ring homomorphism is the determinant of the
corresponding combination. -/
theorem map_genericDet {S : Type*} [CommRing S] (g : MvPolynomial κ ℤ →+* S)
    (W : κ → Matrix ι ι ℤ) :
    g (genericDet W) = (Matrix.of fun i j => ∑ p : κ, g (X p) * ((W p i j : ℤ) : S)).det := by
  rw [genericDet, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  simp only [Matrix.of_apply, map_sum, map_mul, map_C_int]

/-! ### Specialisation to an integer point -/

omit [Fintype κ] in
/-- **A polynomial over the integers that does not vanish at a real point does not vanish at some
integer point.** -/
theorem exists_ne_zero_of_eval_ne_zero {P : MvPolynomial κ ℤ} {v : κ → ℝ}
    (hv : (eval₂Hom (Int.castRingHom ℝ) v) P ≠ 0) : ∃ m : κ → ℤ, eval m P ≠ 0 := by
  by_contra hc
  push_neg at hc
  refine hv ?_
  have hP : P = 0 := MvPolynomial.funext fun x => by rw [hc x, map_zero]
  rw [hP, map_zero]

/-! ### From a real intertwiner to an integral one -/

variable {SA SB TB : Matrix ι ι ℤ} {n : ℕ}

omit [DecidableEq ι] in
/-- A combination of intertwiners is an intertwiner. -/
theorem sum_smul_intertwine {W : κ → Matrix ι ι ℤ} (hW : ∀ p, W p * SA = SB * W p) (m : κ → ℤ) :
    (∑ p : κ, m p • W p) * SA = SB * ∑ p : κ, m p • W p := by
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by
    rw [Matrix.smul_mul, hW p, Matrix.mul_smul]

/-- **An invertible real intertwiner of two integer matrices of finite order produces an invertible
integer one.** -/
theorem exists_intMatrix_intertwine (hn : n ≠ 0) (hSA : SA ^ n = 1) (hSB : SB ^ n = 1)
    (hTB : TB * SB = 1) (hBT : SB * TB = 1) (Φ : Matrix ι ι ℝ)
    (hΦ : Φ * SA.map (Int.cast) = SB.map (Int.cast) * Φ) (hdet : Φ.det ≠ 0) :
    ∃ W : Matrix ι ι ℤ, W * SA = SB * W ∧ W.det ≠ 0 := by
  classical
  obtain ⟨W, hWdef⟩ : ∃ W : ι × ι → Matrix ι ι ℤ,
      ∀ p, W p = avgMatrix SA TB n (single p.1 p.2 1) := ⟨_, fun _ => rfl⟩
  have hWeq : ∀ p, W p * SA = SB * W p := fun p => by
    rw [hWdef p]
    exact avgMatrix_intertwine hSA hSB hTB hBT _
  -- the real intertwiner is the combination of the `W p` with its own entries as coefficients
  have hΦ' : Φ * SA.map (Int.castRingHom ℝ) = SB.map (Int.castRingHom ℝ) * Φ := hΦ
  have hcomb : (n : ℝ) • Φ
      = ∑ p : ι × ι, Φ p.1 p.2 • (W p).map (Int.castRingHom ℝ) := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_sum_smul_map_avgMatrix (Int.castRingHom ℝ) hTB hBT hΦ']
    exact Finset.sum_congr rfl fun p _ => by rw [hWdef p]
  -- so the generic determinant does not vanish at the real point given by its entries
  have hval : (eval₂Hom (Int.castRingHom ℝ) fun p : ι × ι => Φ p.1 p.2) (genericDet W) ≠ 0 := by
    have hmat : (Matrix.of fun i j =>
        ∑ p : ι × ι, (eval₂Hom (Int.castRingHom ℝ) fun p : ι × ι => Φ p.1 p.2) (X p)
          * ((W p i j : ℤ) : ℝ)) = (n : ℝ) • Φ := by
      rw [hcomb]
      ext i j
      rw [Matrix.sum_apply]
      simp
    rw [map_genericDet, hmat, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hn)) hdet
  -- and therefore does not vanish at some integer point
  obtain ⟨m, hm⟩ := exists_ne_zero_of_eval_ne_zero hval
  refine ⟨∑ p : ι × ι, m p • W p, sum_smul_intertwine hWeq m, ?_⟩
  have hmat : (Matrix.of fun i j => ∑ p : ι × ι, (eval m) (X p) * ((W p i j : ℤ) : ℤ))
      = ∑ p : ι × ι, m p • W p := by
    ext i j
    rw [Matrix.sum_apply]
    simp
  have hgd := map_genericDet (eval m) W
  simp only [Int.cast_id] at hgd
  rw [hgd] at hm
  rw [← hmat]
  exact hm

end InverseGalois.CFT
