import Mathlib

/-!
# Diagonal quadratic forms in an arbitrary number of variables

A diagonal quadratic form is recorded by its family of coefficients `a : Fin n → K`, and it is
isotropic when it represents zero at a point other than the origin.  This file collects the
elementary facts about such a form that hold over any field of characteristic other than two:
an isotropic form with invertible coefficients is universal, the values of a form are a union of
square classes, isotropy is preserved by a field homomorphism, and a form splits as a pair of
smaller forms sharing a value.

## Main results

* `InverseGalois.CFT.Local.IsDiagIsotropic`: the diagonal form with coefficient family `a`
  represents zero nontrivially.
* `InverseGalois.CFT.Local.exists_repr_of_isDiagIsotropic`: an isotropic diagonal form with
  invertible coefficients is universal.
* `InverseGalois.CFT.Local.exists_repr_of_isSquare_div`: the values of a diagonal form are a
  union of square classes.
* `InverseGalois.CFT.Local.IsDiagIsotropic.map`: isotropy is carried along a field homomorphism.
-/

namespace InverseGalois.CFT.Local

variable {K : Type*} [Field K]

/-- The diagonal quadratic form with coefficient family `a` is **isotropic** when it represents
zero at a point other than the origin. -/
def IsDiagIsotropic {n : ℕ} (a : Fin n → K) : Prop :=
  ∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0

/-- **An isotropic diagonal form with invertible coefficients is universal.**  Translating an
isotropic vector along a coordinate direction sweeps out every value. -/
theorem exists_repr_of_isDiagIsotropic (h2 : (2 : K) ≠ 0) {n : ℕ} {a : Fin n → K}
    (ha : ∀ i, a i ≠ 0) (h : IsDiagIsotropic a) (c : K) :
    ∃ x : Fin n → K, c = ∑ i, a i * x i ^ 2 := by
  obtain ⟨v, hv, hsum⟩ := h
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (funext hcon)
  set s : K := (c - a j) / (2 * a j * v j) with hs
  refine ⟨fun i => s * v i + (Pi.single j 1 : Fin n → K) i, ?_⟩
  have hexp : ∀ i, a i * (s * v i + (Pi.single j 1 : Fin n → K) i) ^ 2
      = s ^ 2 * (a i * v i ^ 2) + 2 * s * (a i * v i * (Pi.single j 1 : Fin n → K) i)
        + a i * (Pi.single j 1 : Fin n → K) i ^ 2 := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  have hone : ∑ i, a i * v i * (Pi.single j 1 : Fin n → K) i = a j * v j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ j) hb
  have htwo : ∑ i, a i * (Pi.single j 1 : Fin n → K) i ^ 2 = a j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]
      ring
    · intro hb
      exact absurd (Finset.mem_univ j) hb
  have haj : a j ≠ 0 := ha j
  rw [hone, htwo, hs]
  field_simp
  ring

/-- **The values of a diagonal form are a union of square classes.** -/
theorem exists_repr_of_isSquare_div {n : ℕ} {a : Fin n → K} {t s : K} (ht : t ≠ 0)
    (h : ∃ x : Fin n → K, t = ∑ i, a i * x i ^ 2) (hs : IsSquare (s / t)) :
    ∃ x : Fin n → K, s = ∑ i, a i * x i ^ 2 := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨d, hd⟩ := hs
  rw [div_eq_iff ht] at hd
  refine ⟨fun i => x i * d, ?_⟩
  rw [hd, hx, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Isotropy is carried along a field homomorphism.** -/
theorem IsDiagIsotropic.map {L : Type*} [Field L] (f : K →+* L) {n : ℕ} {a : Fin n → K}
    (h : IsDiagIsotropic a) : IsDiagIsotropic fun i => f (a i) := by
  obtain ⟨x, hx, hsum⟩ := h
  refine ⟨fun i => f (x i), ?_, ?_⟩
  · intro hc
    refine hx (funext fun i => ?_)
    have hi : f (x i) = f 0 := by
      rw [map_zero]
      exact congrFun hc i
    exact f.injective hi
  · have hmap : ∑ i, f (a i) * f (x i) ^ 2 = f (∑ i, a i * x i ^ 2) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_pow]
    rw [hmap, hsum, map_zero]

/-- A diagonal form in no variables at all is anisotropic. -/
theorem not_isDiagIsotropic_zero (a : Fin 0 → K) : ¬IsDiagIsotropic a := by
  rintro ⟨x, hx, -⟩
  exact hx (funext fun i => absurd i.2 (by omega))

/-- A diagonal form in one variable with invertible coefficient is anisotropic. -/
theorem not_isDiagIsotropic_one {a : Fin 1 → K} (ha : ∀ i, a i ≠ 0) : ¬IsDiagIsotropic a := by
  rintro ⟨x, hx, hsum⟩
  rw [Fin.sum_univ_one] at hsum
  refine hx (funext fun i => ?_)
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  have := (mul_eq_zero.1 hsum).resolve_left (ha 0)
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

end InverseGalois.CFT.Local
