import Mathlib

/-!
# The spectral norm is the field norm, up to the degree

Over a field `K` complete with respect to a nontrivial nonarchimedean absolute value, a finite
extension `L / K` carries a unique absolute value extending that of `K`; in Mathlib it is
`spectralNorm K L`.  This file identifies it with the field norm: for every `x` in `L`,

`‖N_{L/K}(x)‖ = spectralNorm K L x ^ [L : K]`.

Both sides are read off the constant coefficient `a₀` of the minimal polynomial of `x`.  The
spectral norm is `‖a₀‖ ^ (1 / d)` with `d` the degree of that polynomial
(`spectralNorm_eq_norm_coeff_zero_rpow`), the norm of `x` is `(± a₀) ^ m` with `m = [L : K(x)]`
(`Algebra.norm_eq_norm_adjoin` together with
`Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`), and `[L : K] = d * m`.

The point of the identity is that the left-hand side makes sense for an element of a
noncommutative division algebra over `K`, where the right-hand side does not; the ultrametric
inequality for the field norm therefore transfers to division algebras one commutative subfield at
a time.

## Main results

* `InverseGalois.CFT.norm_algebraNorm_eq_spectralNorm_pow`: `‖N_{L/K}(x)‖ = spectralNorm K L x ^ n`
  for `n = [L : K]`.
* `InverseGalois.CFT.spectralNorm_eq_norm_algebraNorm_rpow`: the same identity solved for the
  spectral norm.

## Tags

spectral norm, field norm, complete valued field
-/

open Module Polynomial IntermediateField

namespace InverseGalois.CFT

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The field norm computes the spectral norm.** Over a complete nonarchimedean base, the norm
of `N_{L/K}(x)` is the `[L : K]`-th power of the spectral norm of `x`. -/
theorem norm_algebraNorm_eq_spectralNorm_pow (x : L) :
    ‖Algebra.norm K x‖ = spectralNorm K L x ^ finrank K L := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hx : IsIntegral K x := IsIntegral.of_finite K x
  set d := (minpoly K x).natDegree with hd
  set m := finrank K⟮x⟯ L with hm
  have hd0 : 0 < d := minpoly.natDegree_pos hx
  have hfin : finrank K L = d * m := by
    rw [hd, ← IntermediateField.adjoin.finrank hx, hm]
    exact (Module.finrank_mul_finrank K K⟮x⟯ L).symm
  have hgen : Algebra.norm K (IntermediateField.AdjoinSimple.gen K x)
      = (-1) ^ d * (minpoly K x).coeff 0 := by
    have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
      (IntermediateField.adjoin.powerBasis hx)
    rwa [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen,
      IntermediateField.adjoin.powerBasis_dim] at h
  have hnorm : ‖Algebra.norm K x‖ = ‖(minpoly K x).coeff 0‖ ^ m := by
    rw [Algebra.norm_eq_norm_adjoin K x, hgen, ← hm, norm_pow, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul]
  rw [hnorm, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K L x, ← hd, hfin,
    ← Real.rpow_natCast (‖(minpoly K x).coeff 0‖ ^ (1 / (d : ℝ))) (d * m),
    ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast ‖(minpoly K x).coeff 0‖ m]
  congr 1
  have : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd0.ne'
  push_cast
  field_simp

/-- The spectral norm of `x` is the `[L : K]`-th root of the norm of `N_{L/K}(x)`. -/
theorem spectralNorm_eq_norm_algebraNorm_rpow (x : L) :
    spectralNorm K L x = ‖Algebra.norm K x‖ ^ (1 / finrank K L : ℝ) := by
  have hpos : 0 < finrank K L := Module.finrank_pos
  rw [norm_algebraNorm_eq_spectralNorm_pow, ← Real.rpow_natCast (spectralNorm K L x) (finrank K L),
    ← Real.rpow_mul (spectralNorm_nonneg x)]
  have : ((finrank K L : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  rw [mul_one_div, div_self this, Real.rpow_one]

end InverseGalois.CFT
