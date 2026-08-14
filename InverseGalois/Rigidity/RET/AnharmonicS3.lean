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
# The symmetric group on three letters as a regular inverse Galois group

The six fractional linear substitutions permuting `{0, 1, ∞}` — the anharmonic group — form a
group of automorphisms of `ℚ(u)` isomorphic to the symmetric group on three letters.  Two of them
generate it: the rotation `u ↦ 1/(1 - u)`, of order three because its matrix cubes to the
negative identity, and the reflection `u ↦ 1/u`, which inverts the rotation.  Since fractional
linear automorphisms compose by matrix multiplication, every relation is a matrix identity, and
two of them are distinct as soon as their matrices are not proportional.

The rotation and the reflection therefore present a copy of the dihedral group of order six inside
the automorphism group of `ℚ(u)`, and Artin's theorem together with Lüroth's theorem turns any
finite group of such automorphisms into a regular realization over `ℚ(T)`.

## Main results

* `Rigidity.RET.anharmonicHom_injective` — the anharmonic group is a faithful copy of the dihedral
  group of order six inside the automorphisms of `ℚ(u)`.
* `Rigidity.RET.dihedralGroupThreeMulEquivPerm` — that dihedral group is the symmetric group on
  three letters.
* `Rigidity.RET.isRegularInverseGalois_perm_fin_three` — **the symmetric group on three letters is
  a regular inverse Galois group**, hence `Rigidity.RET.isInverseGalois_perm_fin_three`: it is a
  Galois group over the rationals.
-/

noncomputable section

namespace Rigidity.RET

/-! ## The two generating substitutions -/

/-- The matrix of the rotation `u ↦ 1/(1 - u)` is invertible. -/
theorem anharmonicRot_det : (0 : ℚ) * 1 - 1 * (-1) ≠ 0 := by norm_num

/-- The matrix of the reflection `u ↦ 1/u` is invertible. -/
theorem anharmonicRefl_det : (0 : ℚ) * 0 - 1 * 1 ≠ 0 := by norm_num

/-- The matrix of the square `u ↦ (u - 1)/u` of the rotation is invertible. -/
theorem anharmonicRotSq_det : (-1 : ℚ) * 0 - 1 * (-1) ≠ 0 := by norm_num

/-- The matrix of the composite `u ↦ u/(u - 1)` of the reflection and the rotation is
invertible. -/
theorem anharmonicReflRot_det : (1 : ℚ) * (-1) - 0 * 1 ≠ 0 := by norm_num

/-- The identity matrix is invertible. -/
theorem anharmonicOne_det : (1 : ℚ) * 1 - 0 * 0 ≠ 0 := by norm_num

/-- The rotation `u ↦ 1/(1 - u)` of the anharmonic group. -/
def anharmonicRot := mobiusAut anharmonicRot_det

/-- The reflection `u ↦ 1/u` of the anharmonic group. -/
def anharmonicRefl := mobiusAut anharmonicRefl_det

/-! ## The relations -/

/-- The identity matrix gives the identity automorphism. -/
theorem mobiusAut_anharmonicOne : mobiusAut anharmonicOne_det = 1 :=
  mobiusAut_scalar one_ne_zero anharmonicOne_det

/-- The square of the rotation is `u ↦ (u - 1)/u`. -/
theorem anharmonicRot_sq : anharmonicRot * anharmonicRot = mobiusAut anharmonicRotSq_det :=
  mobiusAut_mul_eq anharmonicRot_det anharmonicRot_det anharmonicRotSq_det one_ne_zero
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The rotation has order three**: its matrix cubes to the negative identity. -/
theorem anharmonicRot_cube : anharmonicRot ^ 3 = 1 := by
  have h : anharmonicRot * anharmonicRot * anharmonicRot = mobiusAut anharmonicOne_det := by
    rw [anharmonicRot_sq]
    exact mobiusAut_mul_eq anharmonicRotSq_det anharmonicRot_det anharmonicOne_det
      (neg_ne_zero.mpr one_ne_zero) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  calc anharmonicRot ^ 3 = anharmonicRot * anharmonicRot * anharmonicRot := by
        rw [pow_succ, pow_succ, pow_one]
    _ = mobiusAut anharmonicOne_det := h
    _ = 1 := mobiusAut_anharmonicOne

/-- **The reflection is an involution.** -/
theorem anharmonicRefl_sq : anharmonicRefl * anharmonicRefl = 1 := by
  calc anharmonicRefl * anharmonicRefl = mobiusAut anharmonicOne_det :=
        mobiusAut_mul_eq anharmonicRefl_det anharmonicRefl_det anharmonicOne_det one_ne_zero
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ = 1 := mobiusAut_anharmonicOne

/-- The reflection followed by the rotation is `u ↦ u/(u - 1)`. -/
theorem anharmonicRefl_mul_rot :
    anharmonicRefl * anharmonicRot = mobiusAut anharmonicReflRot_det :=
  mobiusAut_mul_eq anharmonicRefl_det anharmonicRot_det anharmonicReflRot_det one_ne_zero
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The reflection inverts the rotation.** -/
theorem anharmonicRefl_mul_rot_mul_refl :
    anharmonicRefl * anharmonicRot * anharmonicRefl = anharmonicRot * anharmonicRot := by
  rw [anharmonicRefl_mul_rot, anharmonicRot_sq]
  exact mobiusAut_mul_eq anharmonicReflRot_det anharmonicRefl_det anharmonicRotSq_det
    (neg_ne_zero.mpr one_ne_zero) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The dihedral relation in the form required by the lift. -/
theorem anharmonicRefl_conj_rot :
    anharmonicRefl * anharmonicRot * anharmonicRefl⁻¹ = anharmonicRot⁻¹ := by
  have hinvRefl : anharmonicRefl⁻¹ = anharmonicRefl :=
    inv_eq_of_mul_eq_one_right anharmonicRefl_sq
  have hcube : anharmonicRot * (anharmonicRot * anharmonicRot) = 1 := by
    rw [← mul_assoc]
    simpa [pow_succ, pow_one] using anharmonicRot_cube
  have hinvRot : anharmonicRot⁻¹ = anharmonicRot * anharmonicRot :=
    inv_eq_of_mul_eq_one_right hcube
  rw [hinvRefl, hinvRot]
  exact anharmonicRefl_mul_rot_mul_refl

/-! ## Nondegeneracy -/

/-- The rotation is not the identity. -/
theorem anharmonicRot_ne_one : anharmonicRot ≠ 1 := by
  rw [← mobiusAut_anharmonicOne]
  exact mobiusAut_ne anharmonicRot_det anharmonicOne_det (by norm_num)

/-- The order of the rotation is exactly three. -/
theorem orderOf_anharmonicRot : orderOf anharmonicRot = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime anharmonicRot_cube anharmonicRot_ne_one

/-- The reflection is none of the three rotations. -/
theorem anharmonicRefl_ne_rot_pow : ∀ m : ℕ, m < 3 → anharmonicRefl ≠ anharmonicRot ^ m := by
  intro m hm
  interval_cases m
  · rw [pow_zero, ← mobiusAut_anharmonicOne]
    exact mobiusAut_ne anharmonicRefl_det anharmonicOne_det (by norm_num)
  · rw [pow_one]
    exact mobiusAut_ne anharmonicRefl_det anharmonicRot_det (by norm_num)
  · rw [pow_succ, pow_one, anharmonicRot_sq]
    exact mobiusAut_ne anharmonicRefl_det anharmonicRotSq_det (by norm_num)

/-! ## The anharmonic group -/

/-- **The anharmonic group**: the dihedral group of order six, mapped to the automorphisms of
`ℚ(u)` by sending the rotation to `u ↦ 1/(1 - u)` and the reflection to `u ↦ 1/u`, and read as
a group of ring automorphisms. -/
def anharmonicHom : DihedralGroup 3 →* RingAut (RatFunc ℚ) :=
  ratFuncAlgEquivToRingAut.comp
    (dihedralLift anharmonicRot_cube anharmonicRefl_sq anharmonicRefl_conj_rot)

theorem anharmonicHom_injective : Function.Injective anharmonicHom :=
  ratFuncAlgEquivToRingAut_injective.comp
    (dihedralLift_injective anharmonicRot_cube anharmonicRefl_sq anharmonicRefl_conj_rot
      orderOf_anharmonicRot anharmonicRefl_ne_rot_pow)

/-- **The dihedral group of order six is a regular inverse Galois group**, realized by the
anharmonic group of substitutions. -/
theorem isRegularInverseGalois_dihedralGroup_three :
    IsRegularInverseGalois (DihedralGroup 3) :=
  IsRegularInverseGalois.of_injective_ringAut _ anharmonicHom anharmonicHom_injective

/-! ## The symmetric group on three letters -/

/-- The three-cycle of the symmetric group on three letters. -/
def permRot : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- The transposition of the symmetric group on three letters. -/
def permRefl : Equiv.Perm (Fin 3) := Equiv.swap 0 1

theorem permRot_cube : permRot ^ 3 = 1 := by decide

theorem permRefl_sq : permRefl * permRefl = 1 := by decide

theorem permRefl_conj_rot : permRefl * permRot * permRefl⁻¹ = permRot⁻¹ := by decide

theorem orderOf_permRot : orderOf permRot = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime permRot_cube (by decide)

theorem permRefl_ne_rot_pow : ∀ m : ℕ, m < 3 → permRefl ≠ permRot ^ m := by
  intro m hm
  interval_cases m <;> decide

/-- The dihedral group of order six, mapped to the symmetric group on three letters. -/
def permHom : DihedralGroup 3 →* Equiv.Perm (Fin 3) :=
  dihedralLift permRot_cube permRefl_sq permRefl_conj_rot

theorem permHom_bijective : Function.Bijective permHom := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨dihedralLift_injective permRot_cube permRefl_sq permRefl_conj_rot orderOf_permRot
    permRefl_ne_rot_pow, ?_⟩
  rw [DihedralGroup.nat_card, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

/-- **The dihedral group of order six is the symmetric group on three letters.** -/
def dihedralGroupThreeMulEquivPerm : DihedralGroup 3 ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective permHom permHom_bijective

/-- **The symmetric group on three letters is a regular inverse Galois group**: it acts on `ℚ(u)`
as the anharmonic group of fractional linear substitutions, and the extension of the field of
invariants by the parameter is a regular realization. -/
theorem isRegularInverseGalois_perm_fin_three :
    IsRegularInverseGalois (Equiv.Perm (Fin 3)) :=
  isRegularInverseGalois_dihedralGroup_three.of_mulEquiv dihedralGroupThreeMulEquivPerm

/-- **The symmetric group on three letters is a Galois group over the rationals**: specializing the
regular realization at a suitable rational number keeps the group, by Hilbert irreducibility. -/
theorem isInverseGalois_perm_fin_three : IsInverseGalois (Equiv.Perm (Fin 3)) :=
  isRegularInverseGalois_perm_fin_three.isInverseGalois

end Rigidity.RET
