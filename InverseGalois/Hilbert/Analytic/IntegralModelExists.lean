/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.IntegralModel
import InverseGalois.Hilbert.Analytic.IntegralModelConstruction

/-!
# Integral model for Hilbert's Irreducibility Theorem

The construction is entirely elementary (Tschirnhaus scaling `X ↦ D·X` to clear
denominators, plus Gauss's lemma). -/

open Polynomial

noncomputable section

/-

For a monic irreducible `f ∈ ℚ[T][X]`, there exists a monic irreducible `F ∈ ℤ[T][X]`
of the same degree, such that ℚ-factors of `f(t, X)` give rise to ℤ-factors of `F(t, X)`.

**Absolute irreducibility is preserved by the integral model.**

If `F ∈ ℤ[T][X]` lifts the scaled polynomial `f.scaleRoots (C D)` (i.e.
`F.map (Int → ℚ) = f.scaleRoots (C D)`) and `f` is absolutely irreducible
(irreducible after base change `ℚ → ℚ̄`), then `F` is absolutely irreducible
(irreducible after base change `ℤ → ℚ̄`). -/
lemma integral_model_absIrr
    (f : Polynomial (Polynomial ℚ)) (hf_monic : f.Monic)
    (F : Polynomial (Polynomial ℤ)) (D : ℕ) (hD : 0 < D)
    (hF_map : F.map (mapRingHom (Int.castRingHom ℚ)) = f.scaleRoots (Polynomial.C (D : ℚ)))
    (hf_abs_irr :
      Irreducible (f.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))))) :
    Irreducible (F.map (mapRingHom (algebraMap ℤ (AlgebraicClosure ℚ)))) := by
  convert scaleRoots_unit_irreducible
    (map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))) f)
    (C (D : AlgebraicClosure ℚ))
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hD.ne')))
    hf_abs_irr using 1
  convert congr_arg (map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) hF_map using 1
  · ext
    simp [coeff_map]
  · ext
    simp [coeff_scaleRoots]
    rw [natDegree_map_of_leadingCoeff_ne_zero]
    aesop

set_option maxHeartbeats 800000 in
theorem integral_model_exists
    (f : Polynomial (Polynomial ℚ))
    (hf_irr : Irreducible f) (hf_monic : f.Monic)
    (hf_abs_irr :
      Irreducible (f.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))))) :
    ∃ (F : Polynomial (Polynomial ℤ)),
      F.Monic ∧ F.natDegree = f.natDegree ∧ Irreducible F ∧
      Irreducible (F.map (mapRingHom (algebraMap ℤ (AlgebraicClosure ℚ)))) ∧
      ∀ (t : ℤ) (k : ℕ), 1 ≤ k →
        (∃ g : Polynomial ℚ, g.natDegree = k ∧ g.Monic ∧
          g ∣ f.map (evalRingHom (↑t : ℚ))) →
        (∃ g : Polynomial ℤ, g.natDegree = k ∧ g.Monic ∧
          g ∣ F.map (evalRingHom t)) := by
  by_contra h_contra
  -- Use the scaleRoots construction with helpers from IntegralModelConstruction.lean.
  obtain ⟨D, hD_pos, hD_clears⟩ := exists_common_denominator f
  set g := f.scaleRoots (C (D : ℚ)) with hg_def
  have hg_monic : g.Monic := by
    rw [Monic, leadingCoeff, natDegree_scaleRoots]
    aesop
  have hg_integral : ∀ i, ∃ b : Polynomial ℤ, g.coeff i = b.map (Int.castRingHom ℚ) := by
    exact scaleRoots_integral_coeffs f hf_monic D hD_pos hD_clears
  have hg_irreducible : Irreducible g := by
    exact scaleRoots_unit_irreducible f (C (D : ℚ))
      (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hD_pos.ne'))) hf_irr
  obtain ⟨F, hF_map⟩ := lift_integral_poly g hg_integral
  have hF_monic : F.Monic := by
    rw [Monic, leadingCoeff, natDegree_eq_of_degree_eq_some]
    any_goals exact F.natDegree
    · have hF_leading_coeff : (F.coeff F.natDegree).map (Int.castRingHom ℚ) = 1 := by
        convert hg_monic.leadingCoeff using 1
        rw [← hF_map, leadingCoeff_map_of_leadingCoeff_ne_zero]
        · aesop
        · intro h
          simp_all [ext_iff]
          have hF_leading_coeff : F.leadingCoeff = 0 := by
            exact ext h
          specialize hF_map (natDegree f) 0
          simp_all [coeff_natDegree]
      exact map_injective (Int.castRingHom ℚ) Int.cast_injective <| by
        simpa using hF_leading_coeff
    · rw [degree_eq_natDegree]
      rw [eq_comm] at hF_map
      aesop
  have hF_irreducible : Irreducible F :=
    hF_monic.irreducible_of_irreducible_map (mapRingHom (Int.castRingHom ℚ)) F
      (by rwa [hF_map])
  have hF_deg : F.natDegree = f.natDegree := by
    have hF_deg : F.natDegree = g.natDegree := by
      rw [← hF_map, natDegree_map_of_leadingCoeff_ne_zero]
      aesop
    rw [hF_deg, natDegree_scaleRoots]
  have hF_factor : ∀ t : ℤ, ∀ k : ℕ, 1 ≤ k →
      (∃ g : Polynomial ℚ, g.natDegree = k ∧ g.Monic ∧ g ∣ (f.map (evalRingHom (t : ℚ)))) →
      ∃ g : Polynomial ℤ, g.natDegree = k ∧ g.Monic ∧ g ∣ F.map (evalRingHom t) := by
    intros t k hk h_factor
    obtain ⟨g_factor, hg_factor_deg, hg_factor_monic, hg_factor_dvd⟩ := h_factor
    have hg_factor_scale : g_factor.scaleRoots (D : ℚ) ∣ (F.map (evalRingHom t)).map (Int.castRingHom ℚ) := by
      have hg_factor_scale : g_factor.scaleRoots (D : ℚ) ∣ (f.map (evalRingHom (t : ℚ))).scaleRoots (D : ℚ) := by
        obtain ⟨q, hq⟩ := hg_factor_dvd
        refine ⟨q.scaleRoots (D : ℚ), ?_⟩
        rw [hq]
        exact mul_scaleRoots_of_noZeroDivisors _ _ _
      convert hg_factor_scale using 1
      convert specialize_scaleRoots_comm f hf_monic (D : ℚ) t using 1
      exact lift_specialize_comm F g hF_map t
    have := monic_int_factor_of_monic_int_dvd'
      (show (F.map (evalRingHom t)).Monic from ?_)
      (show (g_factor.scaleRoots (D : ℚ)).Monic from ?_) hg_factor_scale
    · obtain ⟨g', hg'_monic, hg'_map, hg'_deg⟩ := this
      refine ⟨g', ?_, hg'_monic, ?_⟩
      · rw [hg'_deg, natDegree_scaleRoots, hg_factor_deg]
      · rw [← map_dvd_map (Int.castRingHom ℚ)]
        · aesop
        · exact Int.cast_injective
        · exact hg'_monic
    · exact hF_monic.map _
    · rw [Monic, leadingCoeff_scaleRoots]
      aesop
  have hF_abs_irr_out :
      Irreducible (F.map (mapRingHom (algebraMap ℤ (AlgebraicClosure ℚ)))) :=
    integral_model_absIrr f hf_monic F D hD_pos (hF_map.trans hg_def) hf_abs_irr
  exact h_contra ⟨F, hF_monic, hF_deg, hF_irreducible, hF_abs_irr_out, hF_factor⟩

end
