/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.NormValued

/-!
# The Gauss norm of a power basis with irreducible reduction

Let `K` be a field complete for a rank one valuation with values in the integers and let `L` be
generated over `K` by a single element whose minimal polynomial has coefficients in the valuation
ring and stays irreducible after reduction modulo the maximal ideal.  Writing an element of `L` in
the power basis, the largest absolute value of a coordinate is an absolute value of `L` extending
that of `K`.

Multiplicativity is the only point.  A product of two representatives of degree less than the
degree of the minimal polynomial, reduced modulo that polynomial, again has coefficients in the
valuation ring, so the Gauss norm of a product is at most the product of the Gauss norms; and it is
not smaller, because the reduction of the product is a nonzero element of the quotient of the
polynomial ring over the residue field by an irreducible polynomial, which is a field.

By the uniqueness of an absolute value extending a complete nonarchimedean one, the Gauss norm is
the spectral norm.  Its values are absolute values of coordinates, hence absolute values of scalars,
and so the extension is unramified.

## Main definitions

* `InverseGalois.CFT.repPoly`: the polynomial of degree less than the dimension representing an
  element in a power basis.
* `InverseGalois.CFT.coordNorm`: **the Gauss norm of an element**, the largest absolute value of a
  coordinate.
* `InverseGalois.CFT.coordAbsoluteValue`: the Gauss norm as an absolute value.

## Main results

* `InverseGalois.CFT.coordNorm_mul`: **the Gauss norm is multiplicative** when the reduction of the
  minimal polynomial is irreducible.
* `InverseGalois.CFT.spectralNorm_eq_coordNorm`: **the Gauss norm is the spectral norm.**
* `InverseGalois.CFT.exists_norm_eq_spectralNorm`: every absolute value of the extension is an
  absolute value of a scalar.
* `InverseGalois.CFT.exists_valued_of_residue_irreducible`: **such an extension is an unramified
  extension of local fields.**

## Tags

Gauss norm, spectral norm, unramified extension, local field, power basis, residue field
-/

namespace InverseGalois.CFT

open Module Polynomial

open scoped Valued WithZero NNReal

/-! ### The sup norm of a polynomial -/

section SupNorm

variable {K : Type*} [NormedField K]

/-- The sup norm of a polynomial is bounded by a real number exactly when every coefficient is. -/
theorem supNorm_le_iff {P : K[X]} {r : ℝ} : P.supNorm ≤ r ↔ ∀ i, ‖P.coeff i‖ ≤ r := by
  refine ⟨fun h i => (P.le_supNorm i).trans h, fun h => ?_⟩
  obtain ⟨i, hi⟩ := P.exists_eq_supNorm
  rw [hi]
  exact h i

/-- The sup norm is homogeneous for multiplication by a constant. -/
theorem supNorm_C_mul (a : K) (P : K[X]) : (C a * P).supNorm = ‖a‖ * P.supNorm := by
  refine le_antisymm (supNorm_le_iff.2 fun i => ?_) ?_
  · rw [coeff_C_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (P.le_supNorm i) (norm_nonneg a)
  · obtain ⟨j, hj⟩ := P.exists_eq_supNorm
    rw [hj, ← norm_mul, ← coeff_C_mul]
    exact (C a * P).le_supNorm j

/-- The sup norm of a sum is at most the larger of the two sup norms. -/
theorem supNorm_add_le [IsUltrametricDist K] (P Q : K[X]) :
    (P + Q).supNorm ≤ max P.supNorm Q.supNorm := by
  refine supNorm_le_iff.2 fun i => ?_
  rw [coeff_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (P.le_supNorm i) (Q.le_supNorm i))

end SupNorm

/-! ### Integral polynomials over a valued field -/

section Integer

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)]

/-- An element of a rank one valued field has absolute value one exactly when its value is one. -/
theorem norm_eq_one_iff_valued (x : K) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  have hx : ‖x‖ = ((Valuation.RankOne.hom (Valued.v : Valuation K ℤᵐ⁰) (Valued.v x) : ℝ≥0) : ℝ) :=
    rfl
  constructor
  · intro h
    refine (Valuation.RankOne.strictMono (Valued.v : Valuation K ℤᵐ⁰)).injective ?_
    rw [map_one]
    rw [hx] at h
    exact_mod_cast h
  · intro h
    rw [hx, h, map_one, NNReal.coe_one]

/-- The elements of absolute value at most one are the integers of the valuation. -/
theorem norm_le_one_iff_mem_integer (x : K) : ‖x‖ ≤ 1 ↔ x ∈ 𝒪[K] := by
  show ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1
  have h := norm_le_rankOneHom_iff (A := K) 1 x
  rwa [map_one, NNReal.coe_one] at h

/-- An integer of the valuation has absolute value one exactly when it survives the reduction to
the residue field. -/
theorem norm_eq_one_iff_residue_ne_zero (y : ↥(𝒪[K])) :
    ‖(y : K)‖ = 1 ↔ IsLocalRing.residue ↥(𝒪[K]) y ≠ 0 := by
  have h1 : IsUnit y ↔ Valued.v (y : K) = 1 :=
    Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)
  have h2 : IsLocalRing.residue ↥(𝒪[K]) y = 0 ↔ ¬ IsUnit y := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [norm_eq_one_iff_valued, ← h1, ne_eq, h2, not_not]

/-- A polynomial all of whose coefficients have absolute value at most one comes from the valuation
ring. -/
theorem exists_map_subtype_eq {P : K[X]} (hP : P.supNorm ≤ 1) :
    ∃ P₀ : Polynomial ↥(𝒪[K]), P₀.map (Subring.subtype 𝒪[K]) = P := by
  refine ⟨P.toSubring 𝒪[K] ?_, Polynomial.map_toSubring _ _ _⟩
  intro a ha
  rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at ha
  obtain ⟨n, -, rfl⟩ := ha
  exact (norm_le_one_iff_mem_integer _).1 (supNorm_le_iff.1 hP n)

/-- Every coefficient of an integral polynomial has absolute value at most one. -/
theorem supNorm_map_subtype_le_one (P₀ : Polynomial ↥(𝒪[K])) :
    (P₀.map (Subring.subtype 𝒪[K])).supNorm ≤ 1 := by
  refine supNorm_le_iff.2 fun i => ?_
  rw [coeff_map]
  exact (norm_le_one_iff_mem_integer _).2 (P₀.coeff i).2

/-- An integral polynomial has a coefficient of absolute value one exactly when its reduction to
the residue field is nonzero. -/
theorem supNorm_map_subtype_eq_one_iff (P₀ : Polynomial ↥(𝒪[K])) :
    (P₀.map (Subring.subtype 𝒪[K])).supNorm = 1
      ↔ P₀.map (IsLocalRing.residue ↥(𝒪[K])) ≠ 0 := by
  constructor
  · intro h hzero
    obtain ⟨i, hi⟩ := (P₀.map (Subring.subtype 𝒪[K])).exists_eq_supNorm
    rw [h, coeff_map] at hi
    refine (norm_eq_one_iff_residue_ne_zero (P₀.coeff i)).1 hi.symm ?_
    rw [← coeff_map, hzero, coeff_zero]
  · intro h
    refine le_antisymm (supNorm_map_subtype_le_one P₀) ?_
    have hex : ∃ i, IsLocalRing.residue ↥(𝒪[K]) (P₀.coeff i) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h (Polynomial.ext fun i => by rw [coeff_map, hc i, coeff_zero])
    obtain ⟨i, hi⟩ := hex
    calc (1 : ℝ) = ‖(P₀.map (Subring.subtype 𝒪[K])).coeff i‖ := by
          rw [coeff_map]
          exact ((norm_eq_one_iff_residue_ne_zero _).2 hi).symm
      _ ≤ _ := (P₀.map (Subring.subtype 𝒪[K])).le_supNorm i

end Integer

/-! ### Reduction of a product modulo a polynomial with irreducible reduction -/

section Residue

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- **The reduction of a product stays nonzero.**  If the reduction of a monic polynomial is
irreducible, then the product of two polynomials of smaller degree with nonzero reduction still has
nonzero reduction after division with remainder. -/
theorem map_residue_modByMonic_ne_zero {F P Q : R[X]} (hF : F.Monic)
    (hirr : Irreducible (F.map (IsLocalRing.residue R)))
    (hP : P.map (IsLocalRing.residue R) ≠ 0) (hQ : Q.map (IsLocalRing.residue R) ≠ 0)
    (hPd : P.degree < F.degree) (hQd : Q.degree < F.degree) :
    ((P * Q) %ₘ F).map (IsLocalRing.residue R) ≠ 0 := by
  have hFb : (F.map (IsLocalRing.residue R)).Monic := hF.map _
  have hdF : (F.map (IsLocalRing.residue R)).degree = F.degree := hF.degree_map _
  rw [Polynomial.map_modByMonic _ hF, Polynomial.map_mul]
  intro hzero
  rw [Polynomial.modByMonic_eq_zero_iff_dvd hFb] at hzero
  rcases hirr.prime.2.2 _ _ hzero with h1 | h1
  · exact hP (Polynomial.eq_zero_of_dvd_of_degree_lt h1
      ((Polynomial.degree_map_le).trans_lt (hdF ▸ hPd)))
  · exact hQ (Polynomial.eq_zero_of_dvd_of_degree_lt h1
      ((Polynomial.degree_map_le).trans_lt (hdF ▸ hQd)))

end Residue

/-! ### The representative polynomial of a power basis -/

section Rep

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (pb : PowerBasis K L)

/-- The polynomial of degree less than the dimension which represents an element in a power
basis. -/
noncomputable def repPoly (z : L) : K[X] :=
  ∑ i : Fin pb.dim, Polynomial.monomial (i : ℕ) (pb.basis.repr z i)

theorem degree_repPoly_lt (z : L) : (repPoly pb z).degree < (pb.dim : ℕ) := by
  rw [repPoly]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial]
  exact Polynomial.degree_sum_fin_lt _

theorem aeval_repPoly (z : L) : Polynomial.aeval pb.gen (repPoly pb z) = z := by
  rw [repPoly, map_sum]
  conv_rhs => rw [← pb.basis.sum_repr z]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.aeval_monomial, PowerBasis.coe_basis, Algebra.smul_def]

/-- The representative polynomial is the unique polynomial of degree less than the dimension with
the given value. -/
theorem repPoly_unique {z : L} {P : K[X]} (hdeg : P.degree < (pb.dim : ℕ))
    (hz : Polynomial.aeval pb.gen P = z) : repPoly pb z = P := by
  by_contra hne
  have h0 : repPoly pb z - P ≠ 0 := sub_ne_zero.mpr hne
  have hdlt : (repPoly pb z - P).degree < (pb.dim : ℕ) :=
    (Polynomial.degree_sub_le _ _).trans_lt (max_lt (degree_repPoly_lt pb z) hdeg)
  have hroot : Polynomial.aeval pb.gen (repPoly pb z - P) = 0 := by
    rw [map_sub, aeval_repPoly, hz, sub_self]
  exact absurd (pb.dim_le_degree_of_root h0 hroot) (not_le.2 hdlt)

theorem repPoly_eq_zero_iff (z : L) : repPoly pb z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← aeval_repPoly pb z, h, map_zero]
  · rw [h, repPoly]
    simp

theorem repPoly_add (z w : L) : repPoly pb (z + w) = repPoly pb z + repPoly pb w := by
  simp only [repPoly, map_add, Finsupp.add_apply, ← Finset.sum_add_distrib]

theorem repPoly_smul (c : K) (z : L) : repPoly pb (c • z) = Polynomial.C c * repPoly pb z := by
  simp only [repPoly, map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum,
    Polynomial.C_mul_monomial]

theorem repPoly_algebraMap (c : K) : repPoly pb (algebraMap K L c) = Polynomial.C c := by
  refine repPoly_unique pb ((Polynomial.degree_C_le).trans_lt ?_) (Polynomial.aeval_C _ _)
  exact_mod_cast pb.dim_pos

end Rep

/-! ### The Gauss norm -/

section CoordNorm

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [Field L] [Algebra K L]

/-- **The Gauss norm of an element** relative to a power basis: the largest absolute value of a
coordinate. -/
noncomputable def coordNorm (pb : PowerBasis K L) (z : L) : ℝ := (repPoly pb z).supNorm

theorem coordNorm_nonneg (pb : PowerBasis K L) (z : L) : 0 ≤ coordNorm pb z :=
  Polynomial.supNorm_nonneg _

theorem coordNorm_eq_zero_iff (pb : PowerBasis K L) (z : L) : coordNorm pb z = 0 ↔ z = 0 := by
  rw [coordNorm, Polynomial.supNorm_eq_zero_iff, repPoly_eq_zero_iff]

theorem coordNorm_add_le (pb : PowerBasis K L) (z w : L) :
    coordNorm pb (z + w) ≤ max (coordNorm pb z) (coordNorm pb w) := by
  rw [coordNorm, repPoly_add]
  exact supNorm_add_le _ _

theorem coordNorm_smul (pb : PowerBasis K L) (c : K) (z : L) :
    coordNorm pb (algebraMap K L c * z) = ‖c‖ * coordNorm pb z := by
  rw [← Algebra.smul_def, coordNorm, repPoly_smul, supNorm_C_mul, coordNorm]

theorem coordNorm_algebraMap (pb : PowerBasis K L) (c : K) :
    coordNorm pb (algebraMap K L c) = ‖c‖ := by
  rw [coordNorm, repPoly_algebraMap, Polynomial.supNorm_C]

end CoordNorm

/-! ### Multiplicativity -/

section Mul

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [Field L] [Algebra K L]
  [FiniteDimensional K L]

/-- **The Gauss norm of a product of two elements of Gauss norm one is one.**  The two
representatives lift to the valuation ring, their product reduced modulo the minimal polynomial
still lifts, and its reduction to the residue field is nonzero because the reduction of the minimal
polynomial is irreducible. -/
theorem coordNorm_mul_of_eq_one (pb : PowerBasis K L) {F : Polynomial ↥(𝒪[K])} (hF : F.Monic)
    (hFmin : F.map (Subring.subtype 𝒪[K]) = minpoly K pb.gen)
    (hirr : Irreducible (F.map (IsLocalRing.residue ↥(𝒪[K])))) {z w : L}
    (hz : coordNorm pb z = 1) (hw : coordNorm pb w = 1) : coordNorm pb (z * w) = 1 := by
  have hmon : (minpoly K pb.gen).Monic := minpoly.monic (IsIntegral.of_finite K pb.gen)
  have hdegm : (minpoly K pb.gen).degree = (pb.dim : ℕ) := by
    rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero_of_finite K pb.gen), pb.natDegree_minpoly]
  have hdegF : F.degree = (pb.dim : ℕ) := by rw [← hdegm, ← hFmin, hF.degree_map]
  have hinj : Function.Injective (Subring.subtype 𝒪[K]) := Subtype.val_injective
  obtain ⟨P, hP⟩ := exists_map_subtype_eq (P := repPoly pb z) hz.le
  obtain ⟨Q, hQ⟩ := exists_map_subtype_eq (P := repPoly pb w) hw.le
  have hPres : P.map (IsLocalRing.residue ↥(𝒪[K])) ≠ 0 :=
    (supNorm_map_subtype_eq_one_iff P).1 (by rw [hP]; exact hz)
  have hQres : Q.map (IsLocalRing.residue ↥(𝒪[K])) ≠ 0 :=
    (supNorm_map_subtype_eq_one_iff Q).1 (by rw [hQ]; exact hw)
  have hPdeg : P.degree < F.degree := by
    rw [hdegF, ← Polynomial.degree_map_eq_of_injective hinj P, hP]
    exact degree_repPoly_lt pb z
  have hQdeg : Q.degree < F.degree := by
    rw [hdegF, ← Polynomial.degree_map_eq_of_injective hinj Q, hQ]
    exact degree_repPoly_lt pb w
  have hmodmap : ((P * Q) %ₘ F).map (Subring.subtype 𝒪[K])
      = (repPoly pb z * repPoly pb w) %ₘ minpoly K pb.gen := by
    rw [Polynomial.map_modByMonic _ hF, Polynomial.map_mul, hP, hQ, hFmin]
  have hrep : repPoly pb (z * w) = ((P * Q) %ₘ F).map (Subring.subtype 𝒪[K]) := by
    refine repPoly_unique pb ?_ ?_
    · rw [hmodmap, ← hdegm]
      exact Polynomial.degree_modByMonic_lt _ hmon
    · rw [hmodmap]
      have hkey : Polynomial.aeval pb.gen
          ((repPoly pb z * repPoly pb w) %ₘ minpoly K pb.gen)
            = Polynomial.aeval pb.gen (repPoly pb z * repPoly pb w) := by
        conv_rhs => rw [← Polynomial.modByMonic_add_div (repPoly pb z * repPoly pb w) hmon]
        rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero]
      rw [hkey, map_mul, aeval_repPoly, aeval_repPoly]
  rw [coordNorm, hrep]
  exact (supNorm_map_subtype_eq_one_iff _).2
    (map_residue_modByMonic_ne_zero hF hirr hPres hQres hPdeg hQdeg)

/-- **The Gauss norm is multiplicative** as soon as the reduction of the minimal polynomial of the
generator is irreducible. -/
theorem coordNorm_mul (pb : PowerBasis K L) {F : Polynomial ↥(𝒪[K])} (hF : F.Monic)
    (hFmin : F.map (Subring.subtype 𝒪[K]) = minpoly K pb.gen)
    (hirr : Irreducible (F.map (IsLocalRing.residue ↥(𝒪[K])))) (z w : L) :
    coordNorm pb (z * w) = coordNorm pb z * coordNorm pb w := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [zero_mul, (coordNorm_eq_zero_iff pb 0).2 rfl, zero_mul]
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [mul_zero, (coordNorm_eq_zero_iff pb 0).2 rfl, mul_zero]
  obtain ⟨i, hi⟩ := (repPoly pb z).exists_eq_supNorm
  obtain ⟨j, hj⟩ := (repPoly pb w).exists_eq_supNorm
  have hi' : coordNorm pb z = ‖(repPoly pb z).coeff i‖ := hi
  have hj' : coordNorm pb w = ‖(repPoly pb w).coeff j‖ := hj
  have ha0 : (repPoly pb z).coeff i ≠ 0 := fun h =>
    hz0 ((coordNorm_eq_zero_iff pb z).1 (by rw [hi', h, norm_zero]))
  have hb0 : (repPoly pb w).coeff j ≠ 0 := fun h =>
    hw0 ((coordNorm_eq_zero_iff pb w).1 (by rw [hj', h, norm_zero]))
  set a := (repPoly pb z).coeff i with hadef
  set b := (repPoly pb w).coeff j with hbdef
  have hza : coordNorm pb (algebraMap K L a⁻¹ * z) = 1 := by
    rw [coordNorm_smul, hi', norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.2 ha0)]
  have hwb : coordNorm pb (algebraMap K L b⁻¹ * w) = 1 := by
    rw [coordNorm_smul, hj', norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.2 hb0)]
  have hzw : z * w = algebraMap K L (a * b) *
      (algebraMap K L a⁻¹ * z * (algebraMap K L b⁻¹ * w)) := by
    rw [map_mul, show algebraMap K L a * algebraMap K L b *
        (algebraMap K L a⁻¹ * z * (algebraMap K L b⁻¹ * w))
      = algebraMap K L a * algebraMap K L a⁻¹ *
        (algebraMap K L b * algebraMap K L b⁻¹) * (z * w) from by ring,
      ← map_mul, ← map_mul, mul_inv_cancel₀ ha0, mul_inv_cancel₀ hb0, map_one, one_mul, one_mul]
  rw [hzw, coordNorm_smul, coordNorm_mul_of_eq_one pb hF hFmin hirr hza hwb, mul_one, norm_mul,
    hi', hj']

/-- **The Gauss norm as an absolute value** on the extension. -/
noncomputable def coordAbsoluteValue (pb : PowerBasis K L) {F : Polynomial ↥(𝒪[K])} (hF : F.Monic)
    (hFmin : F.map (Subring.subtype 𝒪[K]) = minpoly K pb.gen)
    (hirr : Irreducible (F.map (IsLocalRing.residue ↥(𝒪[K])))) : AbsoluteValue L ℝ where
  toFun := coordNorm pb
  map_mul' := coordNorm_mul pb hF hFmin hirr
  nonneg' := coordNorm_nonneg pb
  eq_zero' := coordNorm_eq_zero_iff pb
  add_le' z w := (coordNorm_add_le pb z w).trans
    (max_le_add_of_nonneg (coordNorm_nonneg pb z) (coordNorm_nonneg pb w))

end Mul

/-! ### Identification with the spectral norm -/

section Spectral

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

/-- **The Gauss norm is the spectral norm**, because a complete nonarchimedean absolute value
extends to a finite extension in only one way. -/
theorem spectralNorm_eq_coordNorm (pb : PowerBasis K L) {F : Polynomial ↥(𝒪[K])} (hF : F.Monic)
    (hFmin : F.map (Subring.subtype 𝒪[K]) = minpoly K pb.gen)
    (hirr : Irreducible (F.map (IsLocalRing.residue ↥(𝒪[K])))) (z : L) :
    spectralNorm K L z = coordNorm pb z := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  exact (spectralNorm_unique_field_norm_ext (f := coordAbsoluteValue pb hF hFmin hirr)
    (fun c => coordNorm_algebraMap pb c) z).symm

/-- **Every absolute value of the extension is an absolute value of a scalar**: the spectral norm
of an element is the absolute value of one of its coordinates. -/
theorem exists_norm_eq_spectralNorm (pb : PowerBasis K L) {F : Polynomial ↥(𝒪[K])} (hF : F.Monic)
    (hFmin : F.map (Subring.subtype 𝒪[K]) = minpoly K pb.gen)
    (hirr : Irreducible (F.map (IsLocalRing.residue ↥(𝒪[K])))) (z : L) (hz : z ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ spectralNorm K L z = ‖c‖ := by
  obtain ⟨i, hi⟩ := (repPoly pb z).exists_eq_supNorm
  have hi' : coordNorm pb z = ‖(repPoly pb z).coeff i‖ := hi
  refine ⟨(repPoly pb z).coeff i, fun h0 =>
    hz ((coordNorm_eq_zero_iff pb z).1 (by rw [hi', h0, norm_zero])), ?_⟩
  rw [spectralNorm_eq_coordNorm pb hF hFmin hirr, hi']

/-- **A generator whose minimal polynomial reduces to an irreducible polynomial generates an
unramified extension of local fields.** -/
theorem exists_valued_of_residue_irreducible [ProperSpace K] (pb : PowerBasis K L)
    {F : Polynomial ↥(𝒪[K])} (hF : F.Monic)
    (hFmin : F.map (Subring.subtype 𝒪[K]) = minpoly K pb.gen)
    (hirr : Irreducible (F.map (IsLocalRing.residue ↥(𝒪[K])))) {p e : ℕ}
    (hres : HasResidueChar K p e) :
    ∃ (_ : Valued L ℤᵐ⁰) (_ : CompleteSpace L) (m : ℤ) (e' : ℕ),
      (∀ y : L, Valued.v y = Valued.v (Algebra.norm K y)) ∧
      (∀ (σ : L ≃ₐ[K] L) (x : L), Valued.v (σ x) = Valued.v x) ∧
        HasResidueChar L p e' ∧ (∀ k : ℤ, Finite (gradedAdd L k)) ∧
          IsUnramifiedValued K L ∧ IsUnitValGen L m := by
  obtain ⟨u, hu0, hu1⟩ := Valuation.RankOne.nontrivial (Valued.v : Valuation K ℤᵐ⁰)
  have hnt : ∃ x : Kˣ, Valued.v (x : K) ≠ 1 :=
    ⟨Units.mk0 u fun h => hu0 (by rw [h, map_zero]), hu1⟩
  exact exists_valued_of_spectralNorm K L hres hnt (exists_norm_eq_spectralNorm pb hF hFmin hirr)

end Spectral

end InverseGalois.CFT
