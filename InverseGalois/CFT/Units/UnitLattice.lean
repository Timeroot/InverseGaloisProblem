/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.GaloisAction

/-!
# The unit lattice at all the infinite places

Mathlib's logarithmic embedding of the units of a number field discards one distinguished infinite
place, which is harmless for the Dirichlet unit theorem but destroys the symmetry needed to see the
Galois action.  Here the units are embedded into the space of real valued functions on *all* the
infinite places, by `u ↦ (mult w * log (w u))_w`.  The Galois group then acts by permuting the
places, the embedding is equivariant, and the kernel is still the finite group of roots of unity.

The image is a lattice of rank `rank K`, isomorphic to Mathlib's `unitLattice` by forgetting the
distinguished place; the fundamental system therefore provides a basis of it, and the units and the
lattice have the same Herbrand quotient.

## Main definitions

* `InverseGalois.CFT.fullLog`: the logarithmic embedding at all the infinite places.
* `InverseGalois.CFT.unitLatticeFull`: its image, the unit lattice at all the infinite places.
* `InverseGalois.CFT.basisUnitLatticeFull`: the basis of the lattice given by a fundamental system.
* `InverseGalois.CFT.unitLatticeFullAut`: the action of a field automorphism on the lattice.

## Main results

* `InverseGalois.CFT.fullLog_equivariant`: **the embedding is equivariant**, the Galois group acting
  on the target by permuting the infinite places.
* `InverseGalois.CFT.fullLog_eq_zero_iff`: the kernel is the group of roots of unity.
* `InverseGalois.CFT.herbrand_unitsAutHom`: **the units and the unit lattice have the same Herbrand
  quotient.**

## Tags

number field, unit group, unit lattice, logarithmic embedding, Herbrand quotient
-/

namespace InverseGalois.CFT

open MulAction NumberField NumberField.Units NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]

/-! ### The logarithmic embedding at all the infinite places -/

variable (K) in
/-- **The logarithmic embedding of the units into the real valued functions on all the infinite
places.** -/
noncomputable def fullLog : Additive (𝓞 K)ˣ →+ (InfinitePlace K → ℝ) where
  toFun u w := mult w * Real.log (w ((u.toMul : (𝓞 K)ˣ) : K))
  map_zero' := by ext w; simp
  map_add' u v := by ext w; simp [Real.log_mul, mul_add]

omit [NumberField K] in
@[simp]
theorem fullLog_apply (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    fullLog K (Additive.ofMul u) w = mult w * Real.log (w (u : K)) := rfl

/-- The logarithmic embedding at all the places refines Mathlib's. -/
theorem logEmbedding_eq_fullLog (u : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w ≠ w₀}) :
    logEmbedding K (Additive.ofMul u) w = fullLog K (Additive.ofMul u) w.1 := rfl

/-- **The kernel of the logarithmic embedding is the group of roots of unity.** -/
theorem fullLog_eq_zero_iff {u : (𝓞 K)ˣ} : fullLog K (Additive.ofMul u) = 0 ↔ u ∈ torsion K := by
  rw [← logEmbedding_eq_zero_iff]
  refine ⟨fun h => funext fun w => ?_, fun h => funext fun w => ?_⟩
  · rw [logEmbedding_eq_fullLog, h, Pi.zero_apply, Pi.zero_apply]
  · rw [fullLog_apply, mult_log_place_eq_zero.mpr, Pi.zero_apply]
    exact (NumberField.Units.mem_torsion K).mp (logEmbedding_eq_zero_iff.mp h) w

/-! ### The equivariance -/

omit [NumberField K] in
/-- The multiplicity of a place is unchanged by the Galois action. -/
theorem mult_smul (σ : Gal(K/k)) (w : InfinitePlace K) : mult (σ • w) = mult w := by
  by_cases h : w.IsReal
  · rw [mult, mult, if_pos (isReal_smul_iff.mpr h), if_pos h]
  · rw [mult, mult, if_neg fun hc => h (isReal_smul_iff.mp hc), if_neg h]

omit [NumberField K] in
/-- **The logarithmic embedding is equivariant**, the Galois group acting on the target by
permuting the infinite places. -/
theorem fullLog_equivariant (σ : Gal(K/k)) (u : Additive (𝓞 K)ˣ) (w : InfinitePlace K) :
    fullLog K (unitsAutHom σ u) w = fullLog K u (σ⁻¹ • w) := by
  show mult w * Real.log (w ((unitsMulEquiv σ u.toMul : (𝓞 K)ˣ) : K))
    = mult (σ⁻¹ • w) * Real.log ((σ⁻¹ • w) ((u.toMul : (𝓞 K)ˣ) : K))
  rw [mult_smul, coe_unitsMulEquiv_apply, InfinitePlace.smul_apply]
  rfl

/-! ### The unit lattice -/

variable (K) in
/-- **The unit lattice at all the infinite places**, the image of the logarithmic embedding. -/
noncomputable def unitLatticeFull : Submodule ℤ (InfinitePlace K → ℝ) :=
  LinearMap.range (fullLog K).toIntLinearMap

omit [NumberField K] in
theorem mem_unitLatticeFull {x : InfinitePlace K → ℝ} :
    x ∈ unitLatticeFull K ↔ ∃ u, fullLog K u = x := Iff.rfl

omit [NumberField K] in
theorem fullLog_mem_unitLatticeFull (u : Additive (𝓞 K)ˣ) : fullLog K u ∈ unitLatticeFull K :=
  ⟨u, rfl⟩

/-- Forgetting the distinguished place carries the unit lattice at all the places onto Mathlib's
unit lattice. -/
theorem logSpaceRestrict_mem (u : Additive (𝓞 K)ˣ) :
    (fun w : {w : InfinitePlace K // w ≠ w₀} => fullLog K u w.1) ∈ unitLattice K :=
  ⟨u, trivial, rfl⟩

variable (K) in
/-- Forgetting the distinguished place, as a map of the unit lattice at all the infinite places to
Mathlib's unit lattice. -/
noncomputable def unitLatticeRestrict : unitLatticeFull K →ₗ[ℤ] unitLattice K where
  toFun x := ⟨fun w => (x : InfinitePlace K → ℝ) w.1, by
    obtain ⟨u, hu⟩ := x.2
    exact hu ▸ logSpaceRestrict_mem u⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem unitLatticeRestrict_bijective : Function.Bijective (unitLatticeRestrict K) := by
  constructor
  · refine fun x y hxy => Subtype.ext ?_
    obtain ⟨u, hu⟩ := x.2
    obtain ⟨v, hv⟩ := y.2
    have h : logEmbedding K (u - v) = 0 := by
      funext w
      have := congrFun (Subtype.ext_iff.mp hxy) w
      simpa [unitLatticeRestrict, ← hu, ← hv, logEmbedding_eq_fullLog, sub_eq_zero,
        AddMonoidHom.map_sub] using this
    have : fullLog K (u - v) = 0 := by
      rw [← ofMul_toMul (u - v)] at h ⊢
      exact fullLog_eq_zero_iff.mpr (logEmbedding_eq_zero_iff.mp h)
    rw [← hu, ← hv, ← sub_eq_zero, ← map_sub]
    exact this
  · rintro ⟨y, u, -, rfl⟩
    exact ⟨⟨fullLog K u, fullLog_mem_unitLatticeFull u⟩, rfl⟩

variable (K) in
/-- **Forgetting the distinguished place is an isomorphism** of the unit lattice at all the
infinite places with Mathlib's unit lattice. -/
noncomputable def unitLatticeFullEquiv : unitLatticeFull K ≃ₗ[ℤ] unitLattice K :=
  LinearEquiv.ofBijective _ unitLatticeRestrict_bijective

variable (K) in
/-- **The basis of the unit lattice given by a fundamental system of units.** -/
noncomputable def basisUnitLatticeFull : Module.Basis (Fin (rank K)) ℤ (unitLatticeFull K) :=
  (basisUnitLattice K).map (unitLatticeFullEquiv K).symm

theorem coe_basisUnitLatticeFull (j : Fin (rank K)) :
    (basisUnitLatticeFull K j : InfinitePlace K → ℝ)
      = fullLog K (Additive.ofMul (fundSystem K j)) := by
  have h : unitLatticeFullEquiv K ⟨fullLog K (Additive.ofMul (fundSystem K j)),
      fullLog_mem_unitLatticeFull _⟩ = basisUnitLattice K j := by
    refine Subtype.ext ?_
    rw [← logEmbedding_fundSystem]
    rfl
  have h2 : (basisUnitLatticeFull K j) = ⟨fullLog K (Additive.ofMul (fundSystem K j)),
      fullLog_mem_unitLatticeFull _⟩ := by
    rw [basisUnitLatticeFull, Module.Basis.map_apply, ← h, LinearEquiv.symm_apply_apply]
  rw [h2]

noncomputable instance : Module.Free ℤ (unitLatticeFull K) :=
  Module.Free.of_basis (basisUnitLatticeFull K)

instance : Module.Finite ℤ (unitLatticeFull K) :=
  Module.Finite.of_basis (basisUnitLatticeFull K)

/-! ### The action on the unit lattice -/

omit [NumberField K] in
theorem smul_mem_unitLatticeFull (σ : Gal(K/k)) {x : InfinitePlace K → ℝ}
    (hx : x ∈ unitLatticeFull K) :
    (fun w => x (σ⁻¹ • w)) ∈ unitLatticeFull K := by
  obtain ⟨u, rfl⟩ := hx
  exact ⟨unitsAutHom σ u, funext fun w => fullLog_equivariant σ u w⟩

/-- **The action of a field automorphism on the unit lattice.** -/
noncomputable def unitLatticeFullAut (σ : Gal(K/k)) : unitLatticeFull K ≃+ unitLatticeFull K where
  toFun x := ⟨fun w => (x : InfinitePlace K → ℝ) (σ⁻¹ • w), smul_mem_unitLatticeFull σ x.2⟩
  invFun x := ⟨fun w => (x : InfinitePlace K → ℝ) (σ • w), by
    simpa using smul_mem_unitLatticeFull σ⁻¹ x.2⟩
  left_inv x := Subtype.ext (funext fun w => by simp)
  right_inv x := Subtype.ext (funext fun w => by simp)
  map_add' _ _ := rfl

omit [NumberField K] in
@[simp]
theorem coe_unitLatticeFullAut_apply (σ : Gal(K/k)) (x : unitLatticeFull K)
    (w : InfinitePlace K) :
    ((unitLatticeFullAut σ x : unitLatticeFull K) : InfinitePlace K → ℝ) w
      = (x : InfinitePlace K → ℝ) (σ⁻¹ • w) := rfl

omit [NumberField K] in
theorem coe_pow_unitLatticeFullAut_apply (σ : Gal(K/k)) (m : ℕ) (x : unitLatticeFull K)
    (w : InfinitePlace K) :
    (((unitLatticeFullAut σ ^ m) x : unitLatticeFull K) : InfinitePlace K → ℝ) w
      = (x : InfinitePlace K → ℝ) ((σ⁻¹ ^ m) • w) := by
  induction m generalizing w with
  | zero => rfl
  | succ m ih => rw [pow_succ_apply, coe_unitLatticeFullAut_apply, ih, pow_succ, mul_smul]

omit [NumberField K] in
/-- **The action on the unit lattice inherits the order of the automorphism.** -/
theorem unitLatticeFullAut_pow_eq_one {σ : Gal(K/k)} {n : ℕ} (hσ : σ ^ n = 1) :
    (unitLatticeFullAut σ) ^ n = 1 := by
  refine AddEquiv.ext fun x => Subtype.ext (funext fun w => ?_)
  rw [coe_pow_unitLatticeFullAut_apply, inv_pow, hσ, inv_one, one_smul]
  rfl

/-! ### The Herbrand quotient -/

variable (K) in
/-- The logarithmic embedding, viewed as a map onto the unit lattice. -/
noncomputable def fullLogSurj : Additive (𝓞 K)ˣ →+ unitLatticeFull K :=
  AddMonoidHom.codRestrict (fullLog K) (unitLatticeFull K).toAddSubgroup
    fullLog_mem_unitLatticeFull

theorem fullLogSurj_surjective : Function.Surjective (fullLogSurj K) := by
  rintro ⟨x, u, rfl⟩
  exact ⟨u, rfl⟩

theorem fullLogSurj_equivariant (σ : Gal(K/k)) (u : Additive (𝓞 K)ˣ) :
    fullLogSurj K (unitsAutHom σ u) = unitLatticeFullAut σ (fullLogSurj K u) :=
  Subtype.ext (funext fun w => fullLog_equivariant σ u w)

instance instFiniteKerFullLogSurj : Finite (fullLogSurj K).ker := by
  have hset : ((fullLogSurj K).ker : Set (Additive (𝓞 K)ˣ)) = (torsion K : Set (𝓞 K)ˣ) := by
    ext u
    show fullLogSurj K u = 0 ↔ _
    rw [Subtype.ext_iff]
    exact fullLog_eq_zero_iff (u := u.toMul)
  have hfin : ((fullLogSurj K).ker : Set (Additive (𝓞 K)ˣ)).Finite := by
    rw [hset]
    exact Set.finite_coe_iff.mp (inferInstanceAs (Finite (torsion K)))
  exact hfin.to_subtype

/-- **The units and the unit lattice have the same Herbrand quotient.** -/
theorem herbrand_unitsAutHom {σ : Gal(K/k)} {n : ℕ} [NeZero n] (hσ : σ ^ n = 1) :
    herbrand (unitsAutHom σ) n = herbrand (unitLatticeFullAut σ) n :=
  herbrand_eq_of_finite_ker (fullLogSurj_equivariant σ) (unitsAutHom_pow_eq_one hσ)
    (unitLatticeFullAut_pow_eq_one hσ) fullLogSurj_surjective

end InverseGalois.CFT
