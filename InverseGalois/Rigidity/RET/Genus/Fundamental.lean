/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.Degree

/-!
# The fundamental identity, in absolute degrees

Above a point of the base line, a cover has several points, each carrying two numbers: how many
times the cover winds there, and how large the field of values there is.  The fundamental identity
of ramification theory says that the winding numbers weighted by the sizes of the residue fields
add up to the degree of the cover.

Mathlib states the identity with the residue degrees measured relative to the base point.  Measured
instead against a fixed field of constants sitting underneath everything, the identity acquires the
degree of the base point as a factor, since each residue field of the cover is an extension of the
residue field of the base point.  This absolute form is the one that computes the degree of the
divisor of zeros of a function: the winding number at a point of the cover is the order of vanishing
there, so the identity says that the zeros of a function of the base, counted with multiplicity and
with the size of their residue fields, number the degree of the cover times the degree of the base
point.

## Main results

* `Rigidity.RET.finrank_quotient_eq_inertiaDeg_mul` — the degree of a point of the cover is the
  residue degree times the degree of the point below.
* `Rigidity.RET.sum_ramificationIdx_mul_finrank` — the fundamental identity in absolute degrees.
* `Rigidity.RET.ord_algebraMap_eq_ramificationIdx` — the order of vanishing of a generator of the
  base point is the ramification index.
-/

open IsDedekindDomain Ideal Module

noncomputable section


namespace Rigidity.RET

variable {k : Type*} [Field k]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra k R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra k B]
variable (F : Type*) [Field F] [Algebra B F] [IsFractionRing B F]
variable [Algebra R B] [IsScalarTower k R B]
variable [Algebra K F] [Algebra R F] [IsScalarTower R B F] [IsScalarTower R K F]

/-! ## Absolute and relative residue degrees -/

attribute [local instance] Ideal.Quotient.field

omit [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [IsDedekindDomain B] [Algebra B F]
  [IsFractionRing B F] [Algebra K F] [Algebra R F] [IsScalarTower R B F] [IsScalarTower R K F] in
/-- **The degree of a point of the cover is the residue degree over the point below it, times the
degree of that point.** -/
theorem finrank_quotient_eq_inertiaDeg_mul (p : Ideal R) [p.IsMaximal] (P : Ideal B) [P.IsPrime]
    [P.LiesOver p] :
    finrank k (B ⧸ P) = inertiaDeg p P * finrank k (R ⧸ p) := by
  rw [inertiaDeg_algebraMap, mul_comm]
  exact (Module.finrank_mul_finrank k (R ⧸ p) (B ⧸ P)).symm

/-! ## The fundamental identity -/

open scoped Classical in
/-- **The fundamental identity, in absolute degrees**: over a point of the base, the winding
numbers of the cover weighted by the degrees of the points above add up to the degree of the cover
times the degree of the point below. -/
theorem sum_ramificationIdx_mul_finrank [Module.Finite R B] (p : Ideal R) [p.IsMaximal]
    (hp0 : p ≠ ⊥) :
    ∑ P ∈ primesOverFinset p B, ramificationIdx (algebraMap R B) p P * finrank k (B ⧸ P)
      = finrank K F * finrank k (R ⧸ p) := by
  rw [← Ideal.sum_ramification_inertia (S := B) K F hp0, Finset.sum_mul,
    ← Finset.sum_attach (primesOverFinset p B)
      (fun P => ramificationIdx (algebraMap R B) p P * finrank k (B ⧸ P)),
    ← Finset.sum_attach (primesOverFinset p B)
      (fun P => ramificationIdx (algebraMap R B) p P * inertiaDeg p P * finrank k (R ⧸ p))]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [finrank_quotient_eq_inertiaDeg_mul (k := k) p (P : Ideal B), mul_assoc]

/-! ## Winding numbers are orders of vanishing -/

omit [IsDedekindDomain R] in
/-- **The order of vanishing at a point of the cover of a generator of the point below is the
ramification index there.**  Both count the exponent of the point in the factorization of the ideal
the generator spans. -/
theorem ord_algebraMap_eq_ramificationIdx (p : Ideal R) (P : HeightOneSpectrum B) {x : R}
    (hx : Ideal.span {x} = p) (hmap0 : Ideal.map (algebraMap R B) p ≠ ⊥) :
    ord F P (algebraMap R F x) = (ramificationIdx (algebraMap R B) p P.asIdeal : ℤ) := by
  classical
  have hxB : algebraMap R F x = algebraMap B F (algebraMap R B x) :=
    IsScalarTower.algebraMap_apply R B F x
  have hspan : Ideal.span {algebraMap R B x} = Ideal.map (algebraMap R B) p := by
    rw [← hx, Ideal.map_span, Set.image_singleton]
  have hspan0 : (Ideal.span {algebraMap R B x} : Ideal B) ≠ 0 := by
    rw [hspan]; exact hmap0
  rw [hxB, ord_algebraMap P, FractionalIdeal.count_coe F P hspan0, hspan,
    IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hmap0 P.isPrime P.ne_bot,
    count_associates_factors_eq hmap0 P.isPrime P.ne_bot]

end Rigidity.RET
