/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.Exp
import InverseGalois.CFT.Local.SpectralNorm
import InverseGalois.CFT.Local.UnramifiedNormValue
import InverseGalois.CFT.Local.ValuedTopology

/-!
# A finite extension of a local field is a local field

A field `K` which is complete for a rank one valuation with values in the integers carries a unique
absolute value extending to any finite extension `L`, the spectral norm, and that absolute value is
the degree-th root of the absolute value of the field norm.  So the field norm transports the
valuation of `K` to a valuation of `L`, and the topology it defines is the topology of the spectral
norm, for which `L` is complete because it is finite dimensional over a complete field.

Local compactness passes to `L` for the same reason, and a locally compact valued field has finite
graded pieces: a step of the additive filtration is a closed ball, hence compact, and the next step
is an open subgroup of it, so the quotient is discrete and compact.

Everything an unramified extension of local fields is asked for is therefore available on `L`: a
valuation, completeness, a residue characteristic, finite graded pieces, a generator of the value
group, and invariance under the automorphisms of `L` over `K` — the last for free, because the norm
does not see an automorphism.

## Main definitions

* `InverseGalois.CFT.normValuation`: **the valuation of a finite extension given by the field
  norm.**
* `InverseGalois.CFT.normValued`: **the valued structure it defines**, carried on the uniformity of
  the spectral norm.

## Main results

* `InverseGalois.CFT.finite_gradedAdd_of_properSpace`: **the graded pieces of a locally compact
  valued field are finite.**
* `InverseGalois.CFT.mem_nhds_zero_iff_valuation_lt`: a valuation which reads off a power of the
  norm defines the norm topology.
* `InverseGalois.CFT.exists_valued_of_spectralNorm`: **a finite extension of a complete, discretely
  valued, locally compact field carries all the structure of a local field.**

## Tags

local field, valuation, spectral norm, complete valued field, unramified extension
-/

namespace InverseGalois.CFT

open Module Filter Topology

open scoped Valued WithZero NNReal

/-! ### The graded pieces of a locally compact valued field -/

section Graded

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation A ℤᵐ⁰)]

/-- The absolute value of an element is at most the image of a value exactly when its value is at
most that value: the comparison map of a rank one valuation reflects the order. -/
theorem norm_le_rankOneHom_iff (γ : ℤᵐ⁰) (x : A) :
    ‖x‖ ≤ ((Valuation.RankOne.hom (Valued.v : Valuation A ℤᵐ⁰) γ : ℝ≥0) : ℝ) ↔ Valued.v x ≤ γ := by
  rw [show ‖x‖ = ((Valuation.RankOne.hom (Valued.v : Valuation A ℤᵐ⁰) (Valued.v x) : ℝ≥0) : ℝ) from
      rfl, NNReal.coe_le_coe]
  exact (Valuation.RankOne.strictMono (Valued.v : Valuation A ℤᵐ⁰)).le_iff_le

/-- **A step of the additive filtration is a closed ball.** -/
theorem coe_valAddSubgroup_eq_closedBall (j : ℤ) :
    ((valAddSubgroup A j : AddSubgroup A) : Set A)
      = Metric.closedBall (0 : A)
        ((Valuation.RankOne.hom (Valued.v : Valuation A ℤᵐ⁰) (WithZero.exp (-j)) : ℝ≥0) : ℝ) := by
  ext x
  rw [SetLike.mem_coe, mem_valAddSubgroup, Metric.mem_closedBall, dist_zero_right,
    norm_le_rankOneHom_iff]

/-- **A step of the additive filtration of a locally compact valued field is compact.** -/
theorem isCompact_valAddSubgroup [ProperSpace A] (j : ℤ) :
    IsCompact ((valAddSubgroup A j : AddSubgroup A) : Set A) := by
  rw [coe_valAddSubgroup_eq_closedBall]
  exact isCompact_closedBall _ _

/-- **The graded pieces of a locally compact valued field are finite.**  A step of the additive
filtration is a compact subgroup and the next step is an open subgroup of it, so the quotient is
both discrete and compact. -/
theorem finite_gradedAdd_of_properSpace [ProperSpace A] (j : ℤ) : Finite (gradedAdd A j) := by
  haveI : CompactSpace ↥(valAddSubgroup A j) :=
    isCompact_iff_compactSpace.mp (isCompact_valAddSubgroup j)
  refine AddSubgroup.quotient_finite_of_isOpen _ ?_
  rw [AddSubgroup.coe_addSubgroupOf]
  exact (isOpen_valAddSubgroup (j + 1)).preimage continuous_subtype_val

end Graded

/-! ### Powers in the value group -/

/-- The value group of a discrete valuation is torsion free: a positive power of a value other than
zero and one is again other than one. -/
theorem exp_pow_ne_one {m : ℤ} (hm : m ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    (WithZero.exp m) ^ n ≠ (1 : ℤᵐ⁰) := by
  rw [← WithZero.exp_nsmul, ne_eq, WithZero.exp_eq_one, nsmul_eq_mul]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hn) hm

/-- The value group of a discrete valuation has more than one element. -/
theorem nontrivial_units_intWithZero : Nontrivial (ℤᵐ⁰)ˣ :=
  ⟨⟨1, Units.mk0 (WithZero.exp (1 : ℤ)) WithZero.exp_ne_zero, fun hcon =>
    one_ne_zero (WithZero.exp_eq_one.mp (congrArg Units.val hcon).symm)⟩⟩

/-! ### A valuation which reads off a power of the norm -/

section NhdsZero

variable {M Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Nontrivial Γ₀ˣ] [NormedField M]
  {f : Γ₀ →*₀ ℝ≥0} {v : Valuation M Γ₀} {n : ℕ}

/-- **A valuation which reads off a power of the norm defines the norm topology.**  The sets it
cuts out are preimages of half lines under the continuous map sending an element to that power of
its norm, and conversely a ball contains such a set because the comparison map takes values below
any positive real. -/
theorem mem_nhds_zero_iff_valuation_lt (hf : StrictMono f) (hn : n ≠ 0)
    (h : ∀ y : M, ((f (v y) : ℝ≥0) : ℝ) = ‖y‖ ^ n) (s : Set M) :
    s ∈ 𝓝 (0 : M) ↔ ∃ γ : Γ₀ˣ, {x : M | v x < γ} ⊆ s := by
  have hset : ∀ γ : Γ₀ˣ,
      {x : M | v x < (γ : Γ₀)} = {x : M | ‖x‖ ^ n < ((f (γ : Γ₀) : ℝ≥0) : ℝ)} := by
    intro γ
    ext x
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← h x, NNReal.coe_lt_coe, hf.lt_iff_lt]
  constructor
  · intro hs
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 hs
    obtain ⟨γ, hγ⟩ := Real.exists_lt_of_strictMono hf (r := ε ^ n) (by positivity)
    refine ⟨γ, ?_⟩
    rw [hset γ]
    intro x hx
    refine hsub (mem_ball_zero_iff.2 ?_)
    have hlt : ‖x‖ ^ n < ε ^ n := lt_trans hx hγ
    by_contra hcon
    exact absurd (pow_le_pow_left₀ hε.le (not_lt.1 hcon) n) (not_le.2 hlt)
  · rintro ⟨γ, hγ⟩
    refine Filter.mem_of_superset ?_ hγ
    rw [hset γ]
    refine IsOpen.mem_nhds (isOpen_lt (continuous_norm.pow n) continuous_const) ?_
    have hpos : (0 : ℝ≥0) < f (γ : Γ₀) := by
      have hlt := hf (Units.zero_lt γ)
      rwa [map_zero] at hlt
    simp only [Set.mem_setOf_eq, norm_zero, zero_pow hn]
    exact_mod_cast hpos

end NhdsZero

/-! ### The valuation of a finite extension -/

section NormValuation

variable (K L : Type) [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K]
  [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The valuation of a finite extension given by the field norm.** -/
noncomputable def normValuation : Valuation L ℤᵐ⁰ where
  toFun y := Valued.v (Algebra.norm K y)
  map_zero' := by
    show Valued.v (Algebra.norm K (0 : L)) = 0
    rw [show Algebra.norm K (0 : L) = 0 from Algebra.norm_eq_zero_iff.mpr rfl, map_zero]
  map_one' := by
    show Valued.v (Algebra.norm K (1 : L)) = 1
    rw [map_one, map_one]
  map_mul' x y := by
    show Valued.v (Algebra.norm K (x * y)) = Valued.v (Algebra.norm K x) * _
    rw [map_mul, map_mul]
  map_add_le_max' x y := by
    haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    have key : ∀ a b : L, spectralNorm K L a ≤ spectralNorm K L b →
        Valued.v (Algebra.norm K a) ≤ Valued.v (Algebra.norm K b) := by
      intro a b hab
      refine Valued.toNormedField.norm_le_iff.1 ?_
      rw [norm_algebraNorm_eq_spectralNorm_pow, norm_algebraNorm_eq_spectralNorm_pow]
      exact pow_le_pow_left₀ (spectralNorm_nonneg a) hab _
    have hsp := isNonarchimedean_spectralNorm (K := K) (L := L) x y
    rcases le_total (spectralNorm K L x) (spectralNorm K L y) with hle | hle
    · rw [max_eq_right hle] at hsp
      exact le_max_of_le_right (key _ _ hsp)
    · rw [max_eq_left hle] at hsp
      exact le_max_of_le_left (key _ _ hsp)

theorem normValuation_apply (y : L) : normValuation K L y = Valued.v (Algebra.norm K y) := rfl

/-- The comparison map of the base field turns the value of a norm into the degree-th power of the
spectral norm. -/
theorem rankOneHom_normValuation (y : L) :
    ((Valuation.RankOne.hom (Valued.v : Valuation K ℤᵐ⁰) (normValuation K L y) : ℝ≥0) : ℝ)
      = spectralNorm K L y ^ finrank K L := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  exact norm_algebraNorm_eq_spectralNorm_pow (K := K) (L := L) y

/-- **A finite extension of a locally compact complete field is locally compact** for the spectral
norm, being a finite dimensional normed space over a locally compact field. -/
theorem weaklyLocallyCompactSpace_spectral [ProperSpace K] :
    @WeaklyLocallyCompactSpace L (spectralNorm.uniformSpace K L).toTopologicalSpace := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI := spectralNorm.normedAddCommGroup K L
  letI := spectralNorm.normedSpace K L
  haveI := FiniteDimensional.proper K L
  infer_instance

/-- **The valued structure of a finite extension of a complete valued field**, carried on the
uniformity of the spectral norm. -/
noncomputable def normValued : Valued L ℤᵐ⁰ :=
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NormedField L := spectralNorm.normedField K L
  { toUniformSpace := spectralNorm.uniformSpace K L
    toIsUniformAddGroup := inferInstance
    v := normValuation K L
    is_topological_valuation := by
      haveI : Nontrivial (ℤᵐ⁰)ˣ := nontrivial_units_intWithZero
      exact mem_nhds_zero_iff_valuation_lt
        (Valuation.RankOne.strictMono (Valued.v : Valuation K ℤᵐ⁰))
        (Module.finrank_pos (R := K) (M := L)).ne' (rankOneHom_normValuation K L) }

end NormValuation

/-! ### The structure a finite extension inherits -/

section Transfer

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [Valued L ℤᵐ⁰]
  (hvL : ∀ y : L, Valued.v y = Valued.v (Algebra.norm K y)) {p e : ℕ}

include hvL

omit [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K]
  [FiniteDimensional K L] in
/-- **An automorphism does not change the value of an element**, because it does not change its
norm. -/
theorem valued_algEquiv_of_norm (σ : L ≃ₐ[K] L) (x : L) : Valued.v (σ x) = Valued.v x := by
  rw [hvL, hvL, Algebra.norm_eq_of_algEquiv]

omit [CompleteSpace K] in
/-- **The residue characteristic of a finite extension** is that of the base field, with the
valuation of the prime multiplied by the degree. -/
theorem hasResidueChar_of_norm (hres : HasResidueChar K p e) :
    HasResidueChar L p (finrank K L * e) where
  prime := hres.prime
  pos := Nat.mul_pos Module.finrank_pos hres.pos
  val_p := by
    rw [hvL, show ((p : ℕ) : L) = algebraMap K L ((p : ℕ) : K) from (map_natCast _ p).symm,
      Algebra.norm_algebraMap, map_pow, hres.val_p, ← WithZero.exp_nsmul, nsmul_eq_mul]
    push_cast
    ring_nf

omit [CompleteSpace K] in
/-- **A finite extension has a unit of nontrivial value** as soon as the base field does. -/
theorem exists_units_val_ne_one_of_norm (h : ∃ x : Kˣ, Valued.v (x : K) ≠ 1) :
    ∃ x : Lˣ, Valued.v (x : L) ≠ 1 := by
  obtain ⟨x, hx⟩ := h
  refine ⟨Units.map (algebraMap K L : K →* L) x, ?_⟩
  have hval : Valued.v ((Units.map (algebraMap K L : K →* L) x : Lˣ) : L)
      = Valued.v ((x : K)) ^ finrank K L := by
    rw [hvL]
    show Valued.v (Algebra.norm K (algebraMap K L (x : K))) = _
    rw [Algebra.norm_algebraMap, map_pow]
  rw [hval, ← WithZero.exp_log (valued_unit_ne_zero x)]
  refine exp_pow_ne_one ?_ Module.finrank_pos.ne'
  intro h0
  exact hx (by rw [← WithZero.exp_log (valued_unit_ne_zero x), h0, WithZero.exp_zero])

/-- **The unramifiedness of a finite extension, read from the spectral norm.**  If every nonzero
element has the absolute value of a scalar, then every value of the extension is a value of the
base field. -/
theorem isUnramifiedValued_of_norm
    (hval : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ spectralNorm K L z = ‖c‖) :
    IsUnramifiedValued K L := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  intro x
  obtain ⟨c, hc0, hc⟩ := hval (x : L) (Units.ne_zero x)
  refine ⟨Units.mk0 c hc0, ?_⟩
  have hn : ‖(c : K) ^ finrank K L‖ = ‖Algebra.norm K (x : L)‖ := by
    rw [norm_pow, ← hc, norm_algebraNorm_eq_spectralNorm_pow]
  have hvk : Valued.v ((c : K) ^ finrank K L) = Valued.v (Algebra.norm K (x : L)) :=
    le_antisymm (Valued.toNormedField.norm_le_iff.1 hn.le)
      (Valued.toNormedField.norm_le_iff.1 hn.ge)
  rw [hvL, hvL]
  show Valued.v (Algebra.norm K (algebraMap K L ((Units.mk0 c hc0 : Kˣ) : K))) = _
  rw [Algebra.norm_algebraMap]
  exact hvk

end Transfer

/-! ### A finite extension of a local field -/

section Package

variable (K L : Type) [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [Field L] [Algebra K L] [FiniteDimensional K L] {p e : ℕ}

/-- **A finite extension of a complete, discretely valued, locally compact field carries all the
structure of a local field**: a valuation extending that of the base field, completeness, a residue
characteristic, finite graded pieces, invariance under the automorphisms over the base field, and a
generator of the value group.  The valuation is the value of the field norm.  When every absolute
value of the extension is an absolute value of a scalar, the extension is moreover unramified. -/
theorem exists_valued_of_spectralNorm (hres : HasResidueChar K p e)
    (hnt : ∃ x : Kˣ, Valued.v (x : K) ≠ 1)
    (hval : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ spectralNorm K L z = ‖c‖) :
    ∃ (_ : Valued L ℤᵐ⁰) (_ : CompleteSpace L) (m : ℤ) (e' : ℕ),
      (∀ y : L, Valued.v y = Valued.v (Algebra.norm K y)) ∧
      (∀ (σ : L ≃ₐ[K] L) (x : L), Valued.v (σ x) = Valued.v x) ∧
        HasResidueChar L p e' ∧ (∀ k : ℤ, Finite (gradedAdd L k)) ∧
        IsUnramifiedValued K L ∧ IsUnitValGen L m := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : Valued L ℤᵐ⁰ := normValued K L
  have hvL : ∀ y : L, Valued.v y = Valued.v (Algebra.norm K y) := fun _ => rfl
  haveI : CompleteSpace L := spectralNorm.completeSpace K L
  letI : Valuation.RankOne (Valued.v : Valuation L ℤᵐ⁰) :=
    { hom := Valuation.RankOne.hom (Valued.v : Valuation K ℤᵐ⁰)
      strictMono' := Valuation.RankOne.strictMono (Valued.v : Valuation K ℤᵐ⁰)
      exists_val_nontrivial := by
        obtain ⟨x, hx⟩ := exists_units_val_ne_one_of_norm hvL hnt
        exact ⟨(x : L), valued_unit_ne_zero x, hx⟩ }
  haveI : WeaklyLocallyCompactSpace L := weaklyLocallyCompactSpace_spectral K L
  haveI : ProperSpace L :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace L
  obtain ⟨m, hm⟩ := exists_isUnitValGen (exists_units_val_ne_one_of_norm hvL hnt)
  exact ⟨inferInstance, inferInstance, m, finrank K L * e, hvL, valued_algEquiv_of_norm hvL,
    hasResidueChar_of_norm hvL hres, fun k => finite_gradedAdd_of_properSpace k,
    isUnramifiedValued_of_norm hvL hval, hm⟩

end Package

end InverseGalois.CFT
