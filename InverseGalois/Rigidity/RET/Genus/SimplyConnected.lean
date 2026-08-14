/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.ChartIntegral
import InverseGalois.Rigidity.RET.Genus.PoleBound
import InverseGalois.Rigidity.RET.Genus.Filtration
import InverseGalois.Rigidity.RET.Genus.DerivKernel
import InverseGalois.Rigidity.RET.Genus.InftyOrd

/-!
# A cover of the line unbranched everywhere is trivial

A finite cover of the projective line, unbranched over the affine line and unbranched at the far
end as well, has degree one.  The proof compares two counts of the same spaces of functions.

The functions regular over the first chart with a pole of order at most `m` at the far end form a
space over the constants, and differentiating along the coordinate maps the space for `m + 1` into
the space for `m`.  Unbranchedness is what makes differentiation preserve regularity over each
chart, and the kernel of differentiation consists of constants, so each space is at most one
dimension larger than the previous one: the dimensions grow at most like `1 + m`.

On the other hand a basis of the cover over the line can be taken to consist of functions regular
over the first chart, and each of them has a pole of bounded order at the far end; multiplying such
a basis by the powers `1, x, …, x^m` of the coordinate produces `(m + 1) · d` functions in the space
for a shifted index, and they are independent over the constants because the powers of the
coordinate are independent over the constants and the basis is independent over the line.  So the
dimensions grow at least like `(m + 1) · d`, and comparing the two for large `m` forces `d = 1`.

## Main definitions

* `Rigidity.RET.lineIntegers`, `Rigidity.RET.inftyIntegers` — the functions on the cover regular
  over each of the two charts.
* `Rigidity.RET.inftyDeriv` — differentiation along the coordinate at the far end of the line.

## Main results

* `Rigidity.RET.finrank_eq_one_of_logDeriv_mem_inftyIntegers` — a cover unbranched over the affine
  line, along which the logarithmic derivation preserves the functions regular at the far end, has
  degree one.
* `Rigidity.RET.finrank_eq_one_of_unramified` — a cover of the line unbranched everywhere has
  degree one.
-/

open Polynomial Module

noncomputable section


namespace Rigidity.RET

/-! ## Powers of a transcendental element -/

section Powers

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **The powers of a transcendental element are independent over the base.** -/
theorem linearIndependent_pow_of_transcendental {t : A} (ht : Transcendental R t) :
    LinearIndependent R fun n : ℕ => t ^ n := by
  have hinj : Function.Injective (Polynomial.aeval t : R[X] →ₐ[R] A) :=
    transcendental_iff_injective.1 ht
  have hb : LinearIndependent R fun n : ℕ => (Polynomial.X ^ n : R[X]) := by
    have h := (Polynomial.basisMonomials R).linearIndependent
    rw [Polynomial.coe_basisMonomials] at h
    simpa [Polynomial.X_pow_eq_monomial] using h
  have hmap := hb.map' (Polynomial.aeval t : R[X] →ₐ[R] A).toLinearMap
    (LinearMap.ker_eq_bot.2 hinj)
  simpa [Function.comp_def] using hmap

end Powers

/-! ## The functions regular over each chart -/

section Charts

variable (k F : Type*) [Field k] [Field F] [Algebra k F] [Algebra k[X] F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [IsScalarTower k k[X] F]
  [IsScalarTower k[X] (RatFunc k) F]

/-- **The functions on the cover regular over the first chart.** -/
def lineIntegers : Subalgebra k F := Subalgebra.restrictScalars k (integralClosure k[X] F)

/-- **The functions on the cover regular over the second chart.** -/
def inftyIntegers : Subalgebra k F :=
  Subalgebra.restrictScalars k (integralClosure ↥(inftyChart k) F)

variable {k F}

omit [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [IsScalarTower k[X] (RatFunc k) F] in
theorem mem_lineIntegers {y : F} : y ∈ lineIntegers k F ↔ IsIntegral k[X] y := Iff.rfl

omit [Algebra k[X] F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] in
theorem mem_inftyIntegers {y : F} :
    y ∈ inftyIntegers k F ↔ IsIntegral ↥(inftyChart k) y := Iff.rfl

omit [IsScalarTower k (RatFunc k) F] in
/-- Reading a polynomial in the cover is substituting the coordinate into it. -/
theorem algebraMap_polynomial_eq_aeval (p : k[X]) :
    algebraMap k[X] F p = Polynomial.aeval (coord k F) p := by
  have h : (IsScalarTower.toAlgHom k k[X] F : k[X] →ₐ[k] F) = Polynomial.aeval (coord k F) := by
    refine Polynomial.algHom_ext ?_
    show algebraMap k[X] F Polynomial.X = _
    rw [Polynomial.aeval_X, coord, IsScalarTower.algebraMap_apply k[X] (RatFunc k) F,
      RatFunc.algebraMap_X]
  exact congrArg (fun φ => φ p) h

omit [IsScalarTower k (RatFunc k) F] in
/-- The coordinate is regular over the first chart. -/
theorem coord_mem_lineIntegers : coord k F ∈ lineIntegers k F := by
  have hc : coord k F = algebraMap k[X] F Polynomial.X := by
    rw [algebraMap_polynomial_eq_aeval, Polynomial.aeval_X]
  show IsIntegral k[X] (coord k F)
  rw [hc]
  exact isIntegral_algebraMap

omit [IsScalarTower k (RatFunc k) F] in
theorem adjoin_coord_le_lineIntegers : Algebra.adjoin k {coord k F} ≤ lineIntegers k F :=
  Algebra.adjoin_le (Set.singleton_subset_iff.2 coord_mem_lineIntegers)

omit [Algebra k[X] F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] in
/-- The inverse coordinate is regular over the second chart. -/
theorem inv_coord_mem_inftyIntegers : (coord k F)⁻¹ ∈ inftyIntegers k F := by
  have hmem : (RatFunc.X : RatFunc k)⁻¹ ∈ inftyChart k := Algebra.subset_adjoin rfl
  have h : (coord k F)⁻¹ = algebraMap ↥(inftyChart k) F ⟨(RatFunc.X : RatFunc k)⁻¹, hmem⟩ := by
    rw [IsScalarTower.algebraMap_apply ↥(inftyChart k) (RatFunc k) F, coord, ← map_inv₀]
    rfl
  show IsIntegral ↥(inftyChart k) ((coord k F)⁻¹)
  rw [h]
  exact isIntegral_algebraMap

omit [Algebra k[X] F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] in
/-- Reading the second chart in the cover gives the polynomials in the inverse coordinate. -/
theorem algebraMap_inftyChart_mem_adjoin (a : ↥(inftyChart k)) :
    algebraMap ↥(inftyChart k) F a ∈ Algebra.adjoin k {(coord k F)⁻¹} := by
  let f : RatFunc k →ₐ[k] F := IsScalarTower.toAlgHom k (RatFunc k) F
  have hmap : Subalgebra.map f (Algebra.adjoin k {(RatFunc.X : RatFunc k)⁻¹})
      = Algebra.adjoin k {(coord k F)⁻¹} := by
    rw [AlgHom.map_adjoin_singleton, map_inv₀]
    rfl
  have ha : algebraMap ↥(inftyChart k) F a = f (a : RatFunc k) := by
    rw [IsScalarTower.algebraMap_apply ↥(inftyChart k) (RatFunc k) F]
    rfl
  rw [ha, ← hmap]
  exact ⟨(a : RatFunc k), a.2, rfl⟩

omit [Algebra k[X] F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] in
/-- Raising the power by which the coordinate is divided keeps a function regular at the far end
of the line. -/
theorem isIntegral_inftyChart_inv_pow_mul_of_le {y : F} {M M' : ℕ} (hMM : M ≤ M')
    (h : IsIntegral ↥(inftyChart k) ((coord k F)⁻¹ ^ M * y)) :
    IsIntegral ↥(inftyChart k) ((coord k F)⁻¹ ^ M' * y) := by
  have hu : IsIntegral ↥(inftyChart k) ((coord k F)⁻¹) := inv_coord_mem_inftyIntegers
  have hsplit : (coord k F)⁻¹ ^ M' * y = (coord k F)⁻¹ ^ (M' - M) * ((coord k F)⁻¹ ^ M * y) := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hsplit]
  exact (hu.pow _).mul h

end Charts

/-! ## Differentiating over each chart -/

section Derivations

variable (k F : Type*) [Field k] [CharZero k] [Field F] [Algebra k F] [Algebra k[X] F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [IsScalarTower k k[X] F]
  [IsScalarTower k[X] (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

attribute [local instance] Algebra.FormallyEtale.of_isSeparable

/-- **Differentiation along the coordinate at the far end of the line.** -/
def inftyDeriv : Derivation k F F := (coord k F ^ 2) • lineDeriv k F

variable {k F}

omit [Algebra k[X] F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] in
theorem inftyDeriv_apply (y : F) : inftyDeriv k F y = coord k F ^ 2 * lineDeriv k F y := rfl

omit [Algebra k[X] F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] in
theorem inftyDeriv_inv_coord : inftyDeriv k F (coord k F)⁻¹ = -1 := by
  have hx : coord k F ≠ 0 := coord_ne_zero k F
  rw [inftyDeriv_apply, Derivation.leibniz_inv, lineDeriv_coord, smul_eq_mul, mul_one]
  field_simp

/-- **Differentiating preserves the functions regular over the first chart**, the cover being
unbranched over that chart. -/
theorem lineDeriv_mem_lineIntegers [Algebra.FormallyUnramified k[X] ↥(integralClosure k[X] F)]
    {y : F} (hy : y ∈ lineIntegers k F) : lineDeriv k F y ∈ lineIntegers k F := by
  have hA : ∀ a : k[X], lineDeriv k F (algebraMap k[X] F a) ∈ integralClosure k[X] F := by
    intro a
    have hmem : algebraMap k[X] F a ∈ Algebra.adjoin k {coord k F} := by
      rw [algebraMap_polynomial_eq_aeval]
      exact Polynomial.aeval_mem_adjoin_singleton k _
    have hd : lineDeriv k F (coord k F) ∈ Algebra.adjoin k {coord k F} := by
      rw [lineDeriv_coord]
      exact one_mem _
    exact adjoin_coord_le_lineIntegers (deriv_mem_adjoin hd hmem)
  exact deriv_mem_integralClosure (lineDeriv k F) hA ⟨y, hy⟩

omit [Algebra k[X] F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] in
/-- **Differentiating preserves the functions regular over the second chart**, the cover being
unbranched at the far end of the line. -/
theorem inftyDeriv_mem_inftyIntegers
    [Algebra.FormallyUnramified ↥(inftyChart k) ↥(integralClosure ↥(inftyChart k) F)]
    {y : F} (hy : y ∈ inftyIntegers k F) : inftyDeriv k F y ∈ inftyIntegers k F := by
  have hadj : Algebra.adjoin k {(coord k F)⁻¹} ≤ inftyIntegers k F :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 inv_coord_mem_inftyIntegers)
  have hA : ∀ a : ↥(inftyChart k),
      inftyDeriv k F (algebraMap ↥(inftyChart k) F a) ∈ integralClosure ↥(inftyChart k) F := by
    intro a
    have hd : inftyDeriv k F (coord k F)⁻¹ ∈ Algebra.adjoin k {(coord k F)⁻¹} := by
      rw [inftyDeriv_inv_coord]
      exact neg_mem (one_mem _)
    exact hadj (deriv_mem_adjoin hd (algebraMap_inftyChart_mem_adjoin a))
  exact deriv_mem_integralClosure (inftyDeriv k F) hA ⟨y, hy⟩

end Derivations

/-! ## A cover unbranched everywhere is trivial -/

section Trivial

variable (k F : Type*) [Field k] [CharZero k] [IsAlgClosed k] [Field F] [Algebra k F]
  [Algebra k[X] F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

attribute [local instance] Algebra.FormallyEtale.of_isSeparable

variable {k F}

omit [CharZero k] [IsScalarTower k k[X] F] in
/-- A function regular over both charts is a constant. -/
theorem mem_one_of_isIntegral_charts {y : F} (h₁ : IsIntegral k[X] y)
    (h₂ : IsIntegral ↥(inftyChart k) y) : y ∈ (1 : Submodule k F) :=
  mem_one_of_coeff_minpoly_mem_range fun j =>
    exists_const_of_isIntegral_charts k (isIntegral_coeff_minpoly (A := k[X]) h₁ j)
      (isIntegral_coeff_minpoly (A := ↥(inftyChart k)) h₂ j)

omit [CharZero k] in
theorem filt_zero_le_one :
    filt (coord k F) (lineIntegers k F) (inftyIntegers k F) 0 ≤ (1 : Submodule k F) := by
  intro y hy
  obtain ⟨hy₁, hy₂⟩ := mem_filt.1 hy
  rw [pow_zero, one_mul] at hy₂
  exact mem_one_of_isIntegral_charts (mem_lineIntegers.1 hy₁) (mem_inftyIntegers.1 hy₂)

instance finiteDimensional_filt_zero :
    FiniteDimensional k ↥(filt (coord k F) (lineIntegers k F) (inftyIntegers k F) 0) := by
  haveI := finiteDimensional_one_submodule (k := k) (F := F)
  exact Submodule.finiteDimensional_of_le filt_zero_le_one

omit [CharZero k] in
theorem finrank_filt_zero_le_one :
    finrank k ↥(filt (coord k F) (lineIntegers k F) (inftyIntegers k F) 0) ≤ 1 := by
  haveI := finiteDimensional_one_submodule (k := k) (F := F)
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := Submodule.inclusion (filt_zero_le_one (k := k) (F := F)))
    (Submodule.inclusion_injective _)
  rwa [finrank_one_submodule] at h

set_option maxHeartbeats 400000 in
/-- **A cover of the line unbranched over the affine line, along which the logarithmic derivation
at the far end preserves the functions regular there, has degree one.**

The hypothesis on the far end is weaker than unbranchedness: what the comparison of dimensions
needs is only that multiplying by the coordinate cancel whatever pole differentiation creates at
the far end, and that is what the logarithmic derivation does at a tame branch point. -/
theorem finrank_eq_one_of_logDeriv_mem_inftyIntegers
    [Algebra.FormallyUnramified k[X] ↥(integralClosure k[X] F)]
    (hlog : ∀ y ∈ inftyIntegers k F, coord k F * lineDeriv k F y ∈ inftyIntegers k F) :
    finrank (RatFunc k) F = 1 := by
  classical
  set x : F := coord k F with hxdef
  set B₁ : Subalgebra k F := lineIntegers k F with hB₁
  set B₂ : Subalgebra k F := inftyIntegers k F with hB₂
  have hx0 : x ≠ 0 := coord_ne_zero k F
  -- the hypotheses of the filtration argument
  have hx1 : lineDeriv k F x = 1 := lineDeriv_coord k F
  have hD₁ : ∀ y ∈ B₁, lineDeriv k F y ∈ B₁ := fun _ hy => lineDeriv_mem_lineIntegers hy
  have hD₂ : ∀ y ∈ B₂, x * lineDeriv k F y ∈ B₂ := hlog
  have hker : ∀ y ∈ B₁, lineDeriv k F y = 0 → y ∈ (1 : Submodule k F) :=
    fun _ _ h => mem_one_of_lineDeriv_eq_zero h
  -- the filtration grows at most linearly
  have hub : ∀ m : ℕ, finrank k ↥(filt x B₁ B₂ m) ≤ 1 + m := by
    intro m
    have h := finrank_filt_le (lineDeriv k F) hx1 hD₁ hD₂ hker m
    have h0 : finrank k ↥(filt x B₁ B₂ 0) ≤ 1 := finrank_filt_zero_le_one
    omega
  -- a basis of integral elements, and a bound for the poles of its members
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral k[X] (RatFunc k) F
  have hcard : finrank (RatFunc k) F = Fintype.card ↥s := Module.finrank_eq_card_basis b
  choose N hN using fun i : ↥s => exists_isIntegral_inftyChart_inv_pow_mul (hb i)
  set N₀ : ℕ := Finset.univ.sup N with hN₀
  set m : ℕ := N₀ + 1 with hm
  -- the functions obtained by multiplying the basis by the powers of the coordinate
  have hmem : ∀ (j : Fin (m + 1)) (i : ↥s), x ^ (j : ℕ) * b i ∈ filt x B₁ B₂ (N₀ + m) := by
    intro j i
    refine mem_filt.2 ⟨?_, ?_⟩
    · exact mul_mem (pow_mem coord_mem_lineIntegers _) (hb i)
    · have hrw : x⁻¹ ^ (N₀ + m) * (x ^ (j : ℕ) * b i) = x⁻¹ ^ (N₀ + m - (j : ℕ)) * b i := by
        have hsplit : x⁻¹ ^ (N₀ + m) = x⁻¹ ^ (N₀ + m - (j : ℕ)) * x⁻¹ ^ (j : ℕ) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hsplit, mul_assoc, ← mul_assoc (x⁻¹ ^ (j : ℕ)), ← mul_pow,
          inv_mul_cancel₀ hx0, one_pow, one_mul]
      rw [hrw]
      refine isIntegral_inftyChart_inv_pow_mul_of_le ?_ (hN i)
      have hle : N i ≤ N₀ := Finset.le_sup (Finset.mem_univ i)
      omega
  -- they are independent over the constants
  have hpow : LinearIndependent k fun j : Fin (m + 1) => (RatFunc.X : RatFunc k) ^ (j : ℕ) :=
    (linearIndependent_pow_of_transcendental RatFunc.transcendental_X).comp _ Fin.val_injective
  have hind : LinearIndependent k fun p : Fin (m + 1) × ↥s =>
      ((RatFunc.X : RatFunc k) ^ (p.1 : ℕ)) • b p.2 :=
    linearIndependent_smul hpow b.linearIndependent
  have hv : ∀ p : Fin (m + 1) × ↥s,
      ((RatFunc.X : RatFunc k) ^ (p.1 : ℕ)) • b p.2 = x ^ (p.1 : ℕ) * b p.2 := by
    intro p
    rw [Algebra.smul_def, map_pow, hxdef, coord]
  -- so the filtration is at least as large as their number
  set W : Submodule k F := filt x B₁ B₂ (N₀ + m) with hW
  haveI : FiniteDimensional k ↥W := (finite_and_finrank_filt_le (lineDeriv k F) hx1 hD₁ hD₂
    hker (N₀ + m)).1
  let w : Fin (m + 1) × ↥s → ↥W := fun p =>
    ⟨((RatFunc.X : RatFunc k) ^ (p.1 : ℕ)) • b p.2, by rw [hv p]; exact hmem p.1 p.2⟩
  have hwind : LinearIndependent k w := LinearIndependent.of_comp W.subtype hind
  have hcardle : Fintype.card (Fin (m + 1) × ↥s) ≤ finrank k ↥W := hwind.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin] at hcardle
  -- comparing the two bounds
  have hupper : finrank k ↥W ≤ 1 + (N₀ + m) := hub (N₀ + m)
  have hkey : (m + 1) * Fintype.card ↥s ≤ 1 + (N₀ + m) := le_trans hcardle hupper
  have hle1 : Fintype.card ↥s ≤ 1 := by
    by_contra hlt
    have h2 : 2 ≤ Fintype.card ↥s := by omega
    have := Nat.mul_le_mul_left (m + 1) h2
    omega
  have hpos : 0 < finrank (RatFunc k) F := Module.finrank_pos
  omega

/-- **A cover of the line unbranched everywhere has degree one.**  Unbranchedness at the far end
makes even the plain derivation at the far end preserve the functions regular there, so the
logarithmic one does too. -/
theorem finrank_eq_one_of_unramified
    [Algebra.FormallyUnramified k[X] ↥(integralClosure k[X] F)]
    [Algebra.FormallyUnramified ↥(inftyChart k) ↥(integralClosure ↥(inftyChart k) F)] :
    finrank (RatFunc k) F = 1 := by
  refine finrank_eq_one_of_logDeriv_mem_inftyIntegers fun y hy => ?_
  have h : coord k F ^ 2 * lineDeriv k F y ∈ inftyIntegers k F := by
    have h' := inftyDeriv_mem_inftyIntegers hy
    rwa [inftyDeriv_apply] at h'
  have hx0 : coord k F ≠ 0 := coord_ne_zero k F
  have hrw : coord k F * lineDeriv k F y
      = (coord k F)⁻¹ * (coord k F ^ 2 * lineDeriv k F y) := by
    field_simp
  rw [hrw]
  exact mul_mem inv_coord_mem_inftyIntegers h

end Trivial

end Rigidity.RET
