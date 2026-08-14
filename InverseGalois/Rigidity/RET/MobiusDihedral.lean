/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.DihedralLift
import InverseGalois.Rigidity.RET.FixedField
import InverseGalois.Rigidity.RET.MobiusAut
import InverseGalois.Rigidity.RET.Specialization

/-!
# Dihedral groups of fractional linear substitutions

A rotation of exact order `n` among the fractional linear substitutions of `ℚ(u)`, together with
an involution inverting it, presents the dihedral group of order `2n` faithfully inside the ring
automorphisms of `ℚ(u)`; Artin's theorem and Lüroth's theorem then make that dihedral group a
regular inverse Galois group.  Everything needed is a matrix computation, since the substitutions
compose by matrix multiplication and coincide exactly when their matrices are proportional.

The inverting involution is the same one throughout, `u ↦ 1/u`, and the rotations are the ones
whose matrices have the right ratio of eigenvalues:

* `u ↦ -u`, of order two, giving the dihedral group of order four — the Klein four group;
* `u ↦ (u - 1)/(u + 1)`, of order four, whose matrix squares to `u ↦ -1/u` and whose fourth power
  is the negative identity, giving the dihedral group of order eight;
* `u ↦ (2u - 1)/(u + 1)`, of order six, whose matrix has trace `3` and determinant `3` — the ratio
  `trace² / determinant = 3` that a rotation of order six needs — giving the dihedral group of
  order twelve.

## Main results

* `Rigidity.RET.isRegularInverseGalois_dihedralGroup` — the criterion: a rotation of exact order
  `n` with an inverting involution, none of whose powers it is, realizes the dihedral group of
  order `2n` regularly.
* `Rigidity.RET.isRegularInverseGalois_dihedralGroup_two`,
  `Rigidity.RET.isRegularInverseGalois_dihedralGroup_four`,
  `Rigidity.RET.isRegularInverseGalois_dihedralGroup_six` — the three dihedral groups the
  substitutions of `ℚ(u)` supply, of orders four, eight and twelve, and the corresponding
  `Rigidity.RET.isInverseGalois_dihedralGroup_two`,
  `Rigidity.RET.isInverseGalois_dihedralGroup_four`,
  `Rigidity.RET.isInverseGalois_dihedralGroup_six` over the rationals.
-/

noncomputable section

namespace Rigidity.RET

/-! ## The criterion -/

/-- **A rotation and an inverting involution among the substitutions of `ℚ(u)` realize the
dihedral group.**  The two nondegeneracy hypotheses — the rotation has exact order `n`, and the
involution is none of its powers — make the presentation faithful, and a faithful finite group of
ring automorphisms of `ℚ(u)` is a regular inverse Galois group. -/
theorem isRegularInverseGalois_dihedralGroup {n : ℕ} [NeZero n] {ρ σ : RingAut (RatFunc ℚ)}
    (hρ : ρ ^ n = 1) (hσ : σ * σ = 1) (hc : σ * ρ * σ⁻¹ = ρ⁻¹) (hord : orderOf ρ = n)
    (hnot : ∀ m : ℕ, m < n → σ ≠ ρ ^ m) : IsRegularInverseGalois (DihedralGroup n) :=
  IsRegularInverseGalois.of_injective_ringAut _ (dihedralLift hρ hσ hc)
    (dihedralLift_injective hρ hσ hc hord hnot)

/-! ## The identity and the inverting involution -/

/-- The identity matrix is invertible. -/
theorem mobiusOne_det : (1 : ℚ) * 1 - 0 * 0 ≠ 0 := by norm_num

/-- The matrix of the involution `u ↦ 1/u` is invertible. -/
theorem mobiusRefl_det : (0 : ℚ) * 0 - 1 * 1 ≠ 0 := by norm_num

/-- The identity matrix gives the identity automorphism. -/
theorem mobiusRingAut_mobiusOne : mobiusRingAut mobiusOne_det = 1 :=
  mobiusRingAut_scalar one_ne_zero mobiusOne_det

/-- **The inverting involution** `u ↦ 1/u` of `ℚ(u)`. -/
def mobiusRefl : RingAut (RatFunc ℚ) := mobiusRingAut mobiusRefl_det

theorem mobiusRefl_sq : mobiusRefl * mobiusRefl = 1 := by
  calc mobiusRefl * mobiusRefl = mobiusRingAut mobiusOne_det :=
        mobiusRingAut_mul_eq mobiusRefl_det mobiusRefl_det mobiusOne_det one_ne_zero
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ = 1 := mobiusRingAut_mobiusOne

/-! ## The Klein four group: the rotation `u ↦ -u` -/

/-- The matrix of `u ↦ -u` is invertible. -/
theorem kleinRot_det : (-1 : ℚ) * 1 - 0 * 0 ≠ 0 := by norm_num

/-- The matrix of the composite `u ↦ -1/u` of the involution and the rotation is invertible. -/
theorem kleinRefl_det : (0 : ℚ) * 0 - (-1) * 1 ≠ 0 := by norm_num

/-- **The rotation `u ↦ -u`** of order two. -/
def kleinRot : RingAut (RatFunc ℚ) := mobiusRingAut kleinRot_det

theorem kleinRot_pow_two : kleinRot ^ 2 = 1 := by
  rw [pow_two]
  calc kleinRot * kleinRot = mobiusRingAut mobiusOne_det :=
        mobiusRingAut_mul_eq kleinRot_det kleinRot_det mobiusOne_det one_ne_zero
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ = 1 := mobiusRingAut_mobiusOne

theorem kleinRot_ne_one : kleinRot ≠ 1 := by
  rw [← mobiusRingAut_mobiusOne]
  exact mobiusRingAut_ne kleinRot_det mobiusOne_det (by norm_num)

theorem orderOf_kleinRot : orderOf kleinRot = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime kleinRot_pow_two kleinRot_ne_one

/-- The involution inverts the rotation: the fourfold product is trivial. -/
theorem kleinRot_conj : mobiusRefl * kleinRot * mobiusRefl⁻¹ = kleinRot⁻¹ := by
  refine conj_eq_inv_of_mul_eq_one mobiusRefl_sq ?_
  have h1 : mobiusRefl * kleinRot = mobiusRingAut kleinRefl_det :=
    mobiusRingAut_mul_eq mobiusRefl_det kleinRot_det kleinRefl_det one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : mobiusRingAut kleinRefl_det * mobiusRefl = mobiusRingAut kleinRot_det :=
    mobiusRingAut_mul_eq kleinRefl_det mobiusRefl_det kleinRot_det
      (by norm_num : (-1 : ℚ) ≠ 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h1, h2]
  calc mobiusRingAut kleinRot_det * kleinRot = mobiusRingAut mobiusOne_det :=
        mobiusRingAut_mul_eq kleinRot_det kleinRot_det mobiusOne_det one_ne_zero
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ = 1 := mobiusRingAut_mobiusOne

theorem kleinRefl_ne_rot_pow : ∀ m : ℕ, m < 2 → mobiusRefl ≠ kleinRot ^ m := by
  intro m hm
  interval_cases m
  · rw [pow_zero, ← mobiusRingAut_mobiusOne]
    exact mobiusRingAut_ne mobiusRefl_det mobiusOne_det (by norm_num)
  · rw [pow_one]
    exact mobiusRingAut_ne mobiusRefl_det kleinRot_det (by norm_num)

/-- **The Klein four group is a regular inverse Galois group**: it acts on `ℚ(u)` as the four
substitutions `u`, `-u`, `1/u`, `-1/u`. -/
theorem isRegularInverseGalois_dihedralGroup_two : IsRegularInverseGalois (DihedralGroup 2) :=
  isRegularInverseGalois_dihedralGroup kleinRot_pow_two mobiusRefl_sq kleinRot_conj
    orderOf_kleinRot kleinRefl_ne_rot_pow

/-- **The Klein four group is a Galois group over the rationals.** -/
theorem isInverseGalois_dihedralGroup_two : IsInverseGalois (DihedralGroup 2) :=
  isRegularInverseGalois_dihedralGroup_two.isInverseGalois

/-! ## The dihedral group of order eight: the rotation `u ↦ (u - 1)/(u + 1)` -/

/-- The matrix of `u ↦ (u - 1)/(u + 1)` is invertible. -/
theorem squareRot_det : (1 : ℚ) * 1 - (-1) * 1 ≠ 0 := by norm_num

/-- The matrix of the square `u ↦ -1/u` of the rotation is invertible. -/
theorem squareSq_det : (0 : ℚ) * 0 - (-1) * 1 ≠ 0 := by norm_num

/-- The matrix of the cube `u ↦ (u + 1)/(1 - u)` of the rotation is invertible. -/
theorem squareCube_det : (1 : ℚ) * 1 - 1 * (-1) ≠ 0 := by norm_num

/-- The matrix of the composite `u ↦ (1 - u)/(1 + u)` of the involution and the rotation is
invertible. -/
theorem squareRefl_det : (-1 : ℚ) * 1 - 1 * 1 ≠ 0 := by norm_num

/-- **The rotation `u ↦ (u - 1)/(u + 1)`** of order four. -/
def squareRot : RingAut (RatFunc ℚ) := mobiusRingAut squareRot_det

theorem squareRot_sq : squareRot ^ 2 = mobiusRingAut squareSq_det := by
  rw [pow_two]
  exact mobiusRingAut_mul_eq squareRot_det squareRot_det squareSq_det (by norm_num : (2 : ℚ) ≠ 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem squareRot_cube : squareRot ^ 3 = mobiusRingAut squareCube_det := by
  rw [pow_succ, squareRot_sq]
  exact mobiusRingAut_mul_eq squareSq_det squareRot_det squareCube_det
    (by norm_num : (-1 : ℚ) ≠ 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem squareRot_pow_four : squareRot ^ 4 = 1 := by
  rw [pow_succ, squareRot_cube]
  calc mobiusRingAut squareCube_det * squareRot = mobiusRingAut mobiusOne_det :=
        mobiusRingAut_mul_eq squareCube_det squareRot_det mobiusOne_det
          (by norm_num : (2 : ℚ) ≠ 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ = 1 := mobiusRingAut_mobiusOne

theorem squareRot_sq_ne_one : squareRot ^ 2 ≠ 1 := by
  rw [squareRot_sq, ← mobiusRingAut_mobiusOne]
  exact mobiusRingAut_ne squareSq_det mobiusOne_det (by norm_num)

theorem orderOf_squareRot : orderOf squareRot = 4 :=
  orderOf_eq_of_pow_and_pow_div_prime (by norm_num) squareRot_pow_four (by
    intro p hp hpd
    have hple : p ≤ 4 := Nat.le_of_dvd (by norm_num) hpd
    have hp2 := hp.two_le
    interval_cases p
    · exact squareRot_sq_ne_one
    · exact absurd hpd (by decide)
    · exact absurd hp (by decide))

/-- The involution inverts the rotation: the fourfold product is trivial. -/
theorem squareRot_conj : mobiusRefl * squareRot * mobiusRefl⁻¹ = squareRot⁻¹ := by
  refine conj_eq_inv_of_mul_eq_one mobiusRefl_sq ?_
  have h1 : mobiusRefl * squareRot = mobiusRingAut squareRefl_det :=
    mobiusRingAut_mul_eq mobiusRefl_det squareRot_det squareRefl_det one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : mobiusRingAut squareRefl_det * mobiusRefl = mobiusRingAut squareCube_det :=
    mobiusRingAut_mul_eq squareRefl_det mobiusRefl_det squareCube_det one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h1, h2]
  calc mobiusRingAut squareCube_det * squareRot = mobiusRingAut mobiusOne_det :=
        mobiusRingAut_mul_eq squareCube_det squareRot_det mobiusOne_det
          (by norm_num : (2 : ℚ) ≠ 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ = 1 := mobiusRingAut_mobiusOne

theorem squareRefl_ne_rot_pow : ∀ m : ℕ, m < 4 → mobiusRefl ≠ squareRot ^ m := by
  intro m hm
  interval_cases m
  · rw [pow_zero, ← mobiusRingAut_mobiusOne]
    exact mobiusRingAut_ne mobiusRefl_det mobiusOne_det (by norm_num)
  · rw [pow_one]
    exact mobiusRingAut_ne mobiusRefl_det squareRot_det (by norm_num)
  · rw [squareRot_sq]
    exact mobiusRingAut_ne mobiusRefl_det squareSq_det (by norm_num)
  · rw [squareRot_cube]
    exact mobiusRingAut_ne mobiusRefl_det squareCube_det (by norm_num)

/-- **The dihedral group of order eight is a regular inverse Galois group**, realized by the
substitutions generated by `u ↦ (u - 1)/(u + 1)` and `u ↦ 1/u`. -/
theorem isRegularInverseGalois_dihedralGroup_four : IsRegularInverseGalois (DihedralGroup 4) :=
  isRegularInverseGalois_dihedralGroup squareRot_pow_four mobiusRefl_sq squareRot_conj
    orderOf_squareRot squareRefl_ne_rot_pow

/-- **The dihedral group of order eight is a Galois group over the rationals.** -/
theorem isInverseGalois_dihedralGroup_four : IsInverseGalois (DihedralGroup 4) :=
  isRegularInverseGalois_dihedralGroup_four.isInverseGalois

/-! ## The dihedral group of order twelve: the rotation `u ↦ (2u - 1)/(u + 1)` -/

/-- The matrix of `u ↦ (2u - 1)/(u + 1)` is invertible. -/
theorem hexRot_det : (2 : ℚ) * 1 - (-1) * 1 ≠ 0 := by norm_num

/-- The matrix of the square `u ↦ (u - 1)/u` of the rotation is invertible. -/
theorem hexSq_det : (1 : ℚ) * 0 - (-1) * 1 ≠ 0 := by norm_num

/-- The matrix of the cube `u ↦ (u - 2)/(2u - 1)` of the rotation is invertible. -/
theorem hexCube_det : (1 : ℚ) * (-1) - (-2) * 2 ≠ 0 := by norm_num

/-- The matrix of the fourth power `u ↦ -1/(u - 1)` of the rotation is invertible. -/
theorem hexFour_det : (0 : ℚ) * (-1) - (-1) * 1 ≠ 0 := by norm_num

/-- The matrix of the fifth power `u ↦ (u + 1)/(2 - u)` of the rotation is invertible. -/
theorem hexFive_det : (-1 : ℚ) * (-2) - (-1) * 1 ≠ 0 := by norm_num

/-- The matrix of the composite `u ↦ (2 - u)/(u + 1)` of the involution and the rotation is
invertible. -/
theorem hexRefl_det : (-1 : ℚ) * 1 - 2 * 1 ≠ 0 := by norm_num

/-- The matrix of the inverse `u ↦ (u + 1)/(2 - u)` of the rotation is invertible. -/
theorem hexInv_det : (1 : ℚ) * 2 - 1 * (-1) ≠ 0 := by norm_num

/-- **The rotation `u ↦ (2u - 1)/(u + 1)`** of order six: its matrix has trace three and
determinant three. -/
def hexRot : RingAut (RatFunc ℚ) := mobiusRingAut hexRot_det

theorem hexRot_sq : hexRot ^ 2 = mobiusRingAut hexSq_det := by
  rw [pow_two]
  exact mobiusRingAut_mul_eq hexRot_det hexRot_det hexSq_det (by norm_num : (3 : ℚ) ≠ 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem hexRot_cube : hexRot ^ 3 = mobiusRingAut hexCube_det := by
  rw [pow_succ, hexRot_sq]
  exact mobiusRingAut_mul_eq hexSq_det hexRot_det hexCube_det one_ne_zero
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem hexRot_pow_four : hexRot ^ 4 = mobiusRingAut hexFour_det := by
  rw [pow_succ, hexRot_cube]
  exact mobiusRingAut_mul_eq hexCube_det hexRot_det hexFour_det (by norm_num : (3 : ℚ) ≠ 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem hexRot_pow_five : hexRot ^ 5 = mobiusRingAut hexFive_det := by
  rw [pow_succ, hexRot_pow_four]
  exact mobiusRingAut_mul_eq hexFour_det hexRot_det hexFive_det one_ne_zero
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem hexRot_pow_six : hexRot ^ 6 = 1 := by
  rw [pow_succ, hexRot_pow_five]
  calc mobiusRingAut hexFive_det * hexRot = mobiusRingAut mobiusOne_det :=
        mobiusRingAut_mul_eq hexFive_det hexRot_det mobiusOne_det (by norm_num : (-3 : ℚ) ≠ 0)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ = 1 := mobiusRingAut_mobiusOne

theorem hexRot_sq_ne_one : hexRot ^ 2 ≠ 1 := by
  rw [hexRot_sq, ← mobiusRingAut_mobiusOne]
  exact mobiusRingAut_ne hexSq_det mobiusOne_det (by norm_num)

theorem hexRot_cube_ne_one : hexRot ^ 3 ≠ 1 := by
  rw [hexRot_cube, ← mobiusRingAut_mobiusOne]
  exact mobiusRingAut_ne hexCube_det mobiusOne_det (by norm_num)

theorem orderOf_hexRot : orderOf hexRot = 6 :=
  orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hexRot_pow_six (by
    intro p hp hpd
    have hple : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpd
    have hp2 := hp.two_le
    interval_cases p
    · exact hexRot_cube_ne_one
    · exact hexRot_sq_ne_one
    · exact absurd hp (by decide)
    · exact absurd hpd (by decide)
    · exact absurd hp (by decide))

/-- The involution inverts the rotation: the fourfold product is trivial. -/
theorem hexRot_conj : mobiusRefl * hexRot * mobiusRefl⁻¹ = hexRot⁻¹ := by
  refine conj_eq_inv_of_mul_eq_one mobiusRefl_sq ?_
  have h1 : mobiusRefl * hexRot = mobiusRingAut hexRefl_det :=
    mobiusRingAut_mul_eq mobiusRefl_det hexRot_det hexRefl_det one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : mobiusRingAut hexRefl_det * mobiusRefl = mobiusRingAut hexInv_det :=
    mobiusRingAut_mul_eq hexRefl_det mobiusRefl_det hexInv_det one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h1, h2]
  calc mobiusRingAut hexInv_det * hexRot = mobiusRingAut mobiusOne_det :=
        mobiusRingAut_mul_eq hexInv_det hexRot_det mobiusOne_det (by norm_num : (3 : ℚ) ≠ 0)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ = 1 := mobiusRingAut_mobiusOne

theorem hexRefl_ne_rot_pow : ∀ m : ℕ, m < 6 → mobiusRefl ≠ hexRot ^ m := by
  intro m hm
  interval_cases m
  · rw [pow_zero, ← mobiusRingAut_mobiusOne]
    exact mobiusRingAut_ne mobiusRefl_det mobiusOne_det (by norm_num)
  · rw [pow_one]
    exact mobiusRingAut_ne mobiusRefl_det hexRot_det (by norm_num)
  · rw [hexRot_sq]
    exact mobiusRingAut_ne mobiusRefl_det hexSq_det (by norm_num)
  · rw [hexRot_cube]
    exact mobiusRingAut_ne mobiusRefl_det hexCube_det (by norm_num)
  · rw [hexRot_pow_four]
    exact mobiusRingAut_ne mobiusRefl_det hexFour_det (by norm_num)
  · rw [hexRot_pow_five]
    exact mobiusRingAut_ne mobiusRefl_det hexFive_det (by norm_num)

/-- **The dihedral group of order twelve is a regular inverse Galois group**, realized by the
substitutions generated by `u ↦ (2u - 1)/(u + 1)` and `u ↦ 1/u`. -/
theorem isRegularInverseGalois_dihedralGroup_six : IsRegularInverseGalois (DihedralGroup 6) :=
  isRegularInverseGalois_dihedralGroup hexRot_pow_six mobiusRefl_sq hexRot_conj
    orderOf_hexRot hexRefl_ne_rot_pow

/-- **The dihedral group of order twelve is a Galois group over the rationals.** -/
theorem isInverseGalois_dihedralGroup_six : IsInverseGalois (DihedralGroup 6) :=
  isRegularInverseGalois_dihedralGroup_six.isInverseGalois

end Rigidity.RET
