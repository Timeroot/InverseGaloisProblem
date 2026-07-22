/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.DorgeBauerAnalytic
import InverseGalois.Hilbert.Analytic.SmoothSeparableReduction

/-!
# Separable radical reduction of the integer family, complex specialisation

This is the complex/integer analogue of
`SmoothSeparableReduction.exists_smooth_separable_reduction_real`.

Given `P : ℤ[x][Y]` monic in `Y`, its radical `Q := radical P` in the UFD `ℤ[x][Y]` is
again monic (`radical_monic_int`), divides `P` (`radical_dvd_self`), and has the same roots
under every complex specialisation `P.map (evalIntPolyComplex z)`
(`roots_radical_iff`).  Because `Q` is squarefree, it is separable over the fraction field
`Frac(ℤ[x])` (which is perfect, characteristic zero), giving a Bezout identity with cleared
denominators; past a radius `B` (the moduli of the finitely many complex roots of the Bezout
constant) the complex specialisation `Q.map (evalIntPolyComplex z)` is **separable**.

The upshot `exists_complex_separable_reduction` is exactly the separability-on-the-annulus
input needed by the monodromy step `ramified_root_section`: over the annulus
`{ z | B < ‖z‖ }` the family (its radical) is separable, so `DorgeBauer.rootProj` is a
covering map there, while root membership is unchanged.
-/

open Polynomial UniqueFactorizationMonoid
open scoped Classical

set_option maxHeartbeats 1000000

noncomputable section

namespace ComplexSeparableReduction

/-- The radical of a monic polynomial over `ℤ[x]` is monic. -/
lemma radical_monic_int {F : Polynomial (Polynomial ℤ)} (hF : F.Monic) :
    (radical F).Monic := by
  have h_leading_coeff_div : (radical F).leadingCoeff ∣ F.leadingCoeff :=
    Polynomial.leadingCoeff_dvd_leadingCoeff radical_dvd_self
  have h_leading_coeff_unit : IsUnit ((radical F).leadingCoeff : Polynomial ℤ) := by
    refine isUnit_of_dvd_one (h_leading_coeff_div.trans ?_)
    aesop
  have h_radical_normalized : normalize (radical F) = radical F := by
    simp [radical]
    apply Finset.prod_congr rfl
    simp +contextual [primeFactors]
    exact normalize_normalized_factor
  rw [Polynomial.Monic, ← h_radical_normalized, Polynomial.leadingCoeff_normalize]
  exact normalize_eq_one.mpr h_leading_coeff_unit

/-- A nonzero element of `ℤ[x][Y]` divides some positive power of its radical. -/
lemma dvd_radical_pow_int {F : Polynomial (Polynomial ℤ)} (hF0 : F ≠ 0) :
    ∃ m, 1 ≤ m ∧ F ∣ (radical F) ^ m := by
  by_contra h_contra
  have h_prime_divisors : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors F, p ∣ radical F := by
    intro p hp
    refine Finset.dvd_prod_of_mem _ ?_
    simp_all [primeFactors]
  have h_divides_product :
      F ∣ Multiset.prod (Multiset.map (fun p ↦ p) (UniqueFactorizationMonoid.normalizedFactors F)) := by
    simpa using (UniqueFactorizationMonoid.prod_normalizedFactors hF0).symm.dvd
  refine h_contra ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors F) + 1,
    Nat.succ_pos _, dvd_trans h_divides_product ?_⟩
  refine dvd_trans (Multiset.prod_dvd_prod_of_dvd _ _ h_prime_divisors) ?_
  norm_num [pow_succ']

/-- A squarefree primitive polynomial over `ℤ[x]` stays squarefree over the fraction field. -/
lemma squarefree_map_frac_int {s : Polynomial (Polynomial ℤ)}
    (hs : Squarefree s) (hmon : s.Monic) :
    Squarefree (s.map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)))) := by
  intro x hx
  set xm := x * Polynomial.C (Polynomial.leadingCoeff x)⁻¹ with hxm_def
  have hxm_monic : xm.Monic := by
    by_cases hx0 : x = 0 <;> simp_all [Polynomial.Monic]
    rw [Polynomial.map_eq_zero_iff] at hx <;> aesop_cat
  have hxm_assoc : Associated x xm := by
    by_cases hx : x = 0 <;> simp_all [Polynomial.Monic.def]
    refine associated_of_dvd_dvd ?_ ?_ <;> norm_num [hx]
  have hxm_dvd : xm ∣ Polynomial.map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ))) s :=
    dvd_trans hxm_assoc.symm.dvd (dvd_of_mul_left_dvd hx)
  have hxm_sq_dvd : xm * xm ∣ Polynomial.map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ))) s := by
    convert dvd_trans _ hx using 1
    ring_nf
    exact pow_dvd_pow_of_dvd hxm_assoc.symm.dvd 2
  obtain ⟨x', hx'eq⟩ :
      ∃ x' : Polynomial (Polynomial ℤ),
        x'.map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ))) = xm := by
    have := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := FractionRing (Polynomial ℤ)) hmon hxm_dvd
    aesop
  have hx'mon : x'.Monic := by
    convert hxm_monic using 1
    rw [← hx'eq, Polynomial.Monic.def, Polynomial.Monic.def,
      Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
    · aesop
    · intro h
      simp_all [Polynomial.Monic.def]
  have hx'_sq_dvd : x' * x' ∣ s := by
    rw [← Polynomial.map_dvd_map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)))]
    · aesop
    · exact IsFractionRing.injective _ _
    · exact hx'mon.mul hx'mon
  have := hs x' hx'_sq_dvd
  convert hxm_assoc.symm.isUnit
  simp [← hx'eq]
  refine Or.inl <| Polynomial.isUnit_iff_degree_eq_zero.mpr ?_
  rw [Polynomial.degree_map_eq_of_injective <| IsFractionRing.injective _ _]
  exact Polynomial.degree_eq_zero_of_isUnit this

/-- Bezout with cleared denominators for a squarefree monic polynomial over `ℤ[x]`. -/
lemma exists_bezout_of_squarefree_int {s : Polynomial (Polynomial ℤ)}
    (hs : Squarefree s) (hmon : s.Monic) :
    ∃ (A B : Polynomial (Polynomial ℤ)) (w0 : Polynomial ℤ),
      w0 ≠ 0 ∧ A * s + B * Polynomial.derivative s = Polynomial.C w0 := by
  obtain ⟨U, V, h_bezout⟩ :
      ∃ U V : Polynomial (FractionRing (Polynomial ℤ)),
        U * (s.map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)))) +
          V * (Polynomial.derivative (s.map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ))))) = 1 := by
    exact PerfectField.separable_iff_squarefree.mpr (squarefree_map_frac_int hs hmon)
  obtain ⟨w0, hw0ne, A, B, hAB⟩ :
      ∃ w0 : Polynomial ℤ, w0 ≠ 0 ∧
        ∃ A B : Polynomial (Polynomial ℤ), A * s + B * (derivative s) = Polynomial.C w0 := by
    obtain ⟨w0, hw0⟩ :
        ∃ w0 : Polynomial ℤ, w0 ≠ 0 ∧ ∃ A B : Polynomial (Polynomial ℤ),
          Polynomial.map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ))) A =
            U * Polynomial.C (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)) w0) ∧
          Polynomial.map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ))) B =
            V * Polynomial.C (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)) w0) := by
      have h_clear_denom :
          ∀ p : Polynomial (FractionRing (Polynomial ℤ)), ∃ w0 : Polynomial ℤ, w0 ≠ 0 ∧
            ∃ A : Polynomial (Polynomial ℤ),
              Polynomial.map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ))) A =
                p * Polynomial.C (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)) w0) := by
        intro p
        induction' p using Polynomial.induction_on' with p hp ih ih2
        · obtain ⟨w0, hw0, A, hA⟩ := ih
          obtain ⟨w1, hw1, B, hB⟩ := ih2
          use w0 * w1
          simp_all
          refine ⟨A * Polynomial.C w1 + B * Polynomial.C w0, ?_⟩
          simp [*, add_mul, mul_comm, mul_left_comm]
        · rename_i n a
          obtain ⟨w0, hw0⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial ℤ)) a
          refine ⟨w0.2, ?_, ?_⟩ <;> simp_all [← Polynomial.C_mul_X_pow_eq_monomial]
          refine ⟨Polynomial.C w0.1 * Polynomial.X ^ n, ?_⟩
          simp [← hw0, mul_assoc]
      obtain ⟨w0, hw0, A, hA⟩ := h_clear_denom U
      obtain ⟨w1, hw1, B, hB⟩ := h_clear_denom V
      use w0 * w1
      simp_all
      refine ⟨⟨A * Polynomial.C w1, ?_⟩, ⟨B * Polynomial.C w0, ?_⟩⟩
      · simp [hA, mul_assoc]
      · simp [hB, mul_comm, mul_left_comm]
    obtain ⟨A, B, hA, hB⟩ := hw0.right
    have h_eq :
        Polynomial.map (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ))) (A * s + B * (derivative s)) =
          Polynomial.C (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)) w0) := by
      simp_all [mul_comm, mul_left_comm]
      linear_combination h_bezout * C (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)) w0)
    refine ⟨w0, hw0.1, A, B,
      Polynomial.map_injective (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ)))
        (IsFractionRing.injective _ _) ?_⟩
    aesop
  exact ⟨A, B, w0, hw0ne, hAB⟩

/-- The radical has the same roots as `P` under every complex specialisation. -/
lemma roots_radical_iff (P : Polynomial (Polynomial ℤ)) (hP0 : P ≠ 0) (z w : ℂ) :
    ((radical P).map (evalIntPolyComplex z)).eval w = 0 ↔
      (P.map (evalIntPolyComplex z)).eval w = 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := radical_dvd_self (a := P)
    rw [hk, Polynomial.map_mul, Polynomial.eval_mul, h, zero_mul]
  · intro h
    obtain ⟨m, hm1, k, hk⟩ := dvd_radical_pow_int hP0
    have hh := congrArg (fun q ↦ (q.map (evalIntPolyComplex z)).eval w) hk
    simp only [Polynomial.map_pow, Polynomial.map_mul, Polynomial.eval_pow,
      Polynomial.eval_mul, h, zero_mul] at hh
    have hm0 : m ≠ 0 := by omega
    exact (pow_eq_zero_iff hm0).mp hh

/-
**Separable radical reduction of the integer family (complex specialisation).**

For `P : ℤ[x][Y]` monic in `Y` of positive `Y`-degree, its radical `Q := radical P` is a
monic divisor of `P` with the same roots under every complex specialisation, and there is a
radius `B ≥ 1` such that for every `z` with `B < ‖z‖` the complex specialisation
`Q.map (evalIntPolyComplex z)` is separable.
-/
theorem exists_complex_separable_reduction
    (P : Polynomial (Polynomial ℤ)) (hP_monic : P.Monic) (hP_deg : 1 ≤ P.natDegree) :
    ∃ (Q : Polynomial (Polynomial ℤ)) (B : ℝ), Q.Monic ∧ Q ∣ P ∧ 1 ≤ B ∧
      (∀ z : ℂ, B < ‖z‖ → (Q.map (evalIntPolyComplex z)).Separable) ∧
      (∀ z w : ℂ, (Q.map (evalIntPolyComplex z)).eval w = 0 ↔
        (P.map (evalIntPolyComplex z)).eval w = 0) := by
  obtain ⟨A, B, w0, hw0ne, hbez⟩ := exists_bezout_of_squarefree_int squarefree_radical (radical_monic_int hP_monic)
  refine ⟨radical P, 1 + ∑ r ∈ (w0.map (Int.castRingHom ℂ) |> Polynomial.roots |> Multiset.toFinset), ‖r‖,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact radical_monic_int hP_monic
  · exact radical_dvd_self
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  · intro z hz
    have h_eval : Polynomial.eval z (Polynomial.map (Int.castRingHom ℂ) w0) ≠ 0 := by
      contrapose! hz
      refine le_add_of_nonneg_of_le zero_le_one (Finset.single_le_sum (fun x _ ↦ norm_nonneg x) ?_)
      simp_all [Polynomial.ext_iff]
    have h_bezout :
        (Polynomial.map (evalIntPolyComplex z) A) * (Polynomial.map (evalIntPolyComplex z) (radical P)) +
          (Polynomial.map (evalIntPolyComplex z) B) *
            (Polynomial.derivative (Polynomial.map (evalIntPolyComplex z) (radical P))) =
          Polynomial.C (Polynomial.eval z (Polynomial.map (Int.castRingHom ℂ) w0)) := by
      convert congr_arg (Polynomial.map (evalIntPolyComplex z)) hbez using 1 <;> norm_num [Polynomial.derivative_map]
      unfold evalIntPolyComplex
      aesop
    refine ⟨Polynomial.C (Polynomial.eval z (Polynomial.map (Int.castRingHom ℂ) w0)) ⁻¹ *
        Polynomial.map (evalIntPolyComplex z) A,
      Polynomial.C (Polynomial.eval z (Polynomial.map (Int.castRingHom ℂ) w0)) ⁻¹ *
        Polynomial.map (evalIntPolyComplex z) B, ?_⟩
    convert congr_arg
        (fun p ↦ Polynomial.C (Polynomial.eval z (Polynomial.map (Int.castRingHom ℂ) w0)) ⁻¹ * p) h_bezout
      using 1 <;> ring_nf
    rw [← Polynomial.C_mul, inv_mul_cancel₀ h_eval, Polynomial.C_1]
  · have hP0 : P ≠ 0 := by aesop
    exact roots_radical_iff P hP0

end ComplexSeparableReduction
