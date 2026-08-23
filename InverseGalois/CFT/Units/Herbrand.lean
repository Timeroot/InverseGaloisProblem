/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.InfinitePlaces
import InverseGalois.CFT.Tate.Prod
import InverseGalois.CFT.Tate.RealBasis
import InverseGalois.CFT.Tate.Trivial
import InverseGalois.CFT.Units.UnitLattice

/-!
# The Herbrand quotient of the unit group of a number field

For a cyclic extension of number fields the Herbrand quotient of the group of units of the ring of
integers of the top field is computed by the infinite places alone.  The logarithmic embedding
identifies the units, up to the finite group of roots of unity, with a lattice inside the space of
real valued functions on the infinite places; adjoining the invariant vector of multiplicities
turns it into a lattice of full rank, spanning the same real space as the free lattice on the
infinite places.  Two lattices spanning one real space with actions induced by one endomorphism
have the same Herbrand quotient, and the free lattice on the infinite places is a permutation
representation whose Herbrand quotient is the product of the orders of the decomposition groups.

The outcome is the classical formula: the Herbrand quotient of the units is the product over the
infinite places of the base field of the order of a decomposition group, divided by the degree.

## Main definitions

* `InverseGalois.CFT.multVec`: the vector of multiplicities of the infinite places.
* `InverseGalois.CFT.unitsIdx`: the indexing of the infinite places by a fundamental system of
  units together with the distinguished place.
* `InverseGalois.CFT.unitEmbed`: the embedding of the unit lattice and the multiplicity vector.

## Main results

* `InverseGalois.CFT.herbrand_unitLatticeFull_mul`: the unit lattice and the free lattice on the
  infinite places have Herbrand quotients differing by the degree.
* `InverseGalois.CFT.herbrand_unitsAutHom_mul`: **the Herbrand quotient of the units of a cyclic
  extension, times the degree, is the product of the orders of the decomposition groups at the
  infinite places.**
* `InverseGalois.CFT.herbrand_unitsAutHom_ramified`: the same product written as a power of two.

## Tags

number field, unit group, Herbrand quotient, infinite place, decomposition group
-/

namespace InverseGalois.CFT

open Module (Basis)
open MulAction NumberField NumberField.Units NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone

variable {K : Type*} [Field K] [NumberField K]

/-! ### The two lattices in the real space of the infinite places -/

variable (K) in
/-- **The vector of the multiplicities of the infinite places.** -/
noncomputable def multVec : InfinitePlace K → ℝ := fun w => (mult w : ℝ)

open scoped Classical in
variable (K) in
/-- **The indexing of the infinite places** by a fundamental system of units together with the
distinguished place. -/
noncomputable def unitsIdx : Option (Fin (rank K)) ≃ InfinitePlace K :=
  (Equiv.optionCongr equivFinRank).trans (Equiv.optionSubtypeNe w₀)

@[simp]
theorem unitsIdx_none : unitsIdx K none = w₀ := by simp [unitsIdx]

@[simp]
theorem unitsIdx_some (j : Fin (rank K)) :
    unitsIdx K (some j) = (equivFinRank j : InfinitePlace K) := by simp [unitsIdx]

variable (K) in
/-- The free lattice on the infinite places, inside the real valued functions on them. -/
noncomputable def intCastVec : (InfinitePlace K → ℤ) →+ (InfinitePlace K → ℝ) where
  toFun f w := (f w : ℝ)
  map_zero' := by ext w; simp
  map_add' f g := by ext w; simp

variable (K) in
/-- **The unit lattice together with the multiplicity vector**, inside the real valued functions on
the infinite places. -/
noncomputable def unitEmbed : (unitLatticeFull K × ℤ) →+ (InfinitePlace K → ℝ) where
  toFun z := (z.1 : InfinitePlace K → ℝ) + z.2 • multVec K
  map_zero' := by simp
  map_add' z z' := by
    show ((z.1 + z'.1 : unitLatticeFull K) : InfinitePlace K → ℝ) + (z.2 + z'.2) • multVec K = _
    rw [Submodule.coe_add, add_zsmul]
    abel

/-! ### The four bases -/

variable (K) in
/-- The basis of the free lattice on the infinite places. -/
noncomputable def basisPlaces : Basis (Option (Fin (rank K))) ℤ (InfinitePlace K → ℤ) :=
  (Pi.basisFun ℤ (InfinitePlace K)).reindex (unitsIdx K).symm

variable (K) in
/-- The basis of the real space given by the infinite places. -/
noncomputable def basisPlacesReal : Basis (Option (Fin (rank K))) ℝ (InfinitePlace K → ℝ) :=
  (Pi.basisFun ℝ (InfinitePlace K)).reindex (unitsIdx K).symm

variable (K) in
/-- The basis of the unit lattice together with the multiplicity vector. -/
noncomputable def basisUnits : Basis (Option (Fin (rank K))) ℤ (unitLatticeFull K × ℤ) :=
  ((basisUnitLatticeFull K).prod (Basis.singleton Unit ℤ)).reindex
    (Equiv.optionEquivSumPUnit.{0} (Fin (rank K))).symm

variable (K) in
/-- The basis of the real space given by a fundamental system of units and the multiplicity
vector. -/
noncomputable def basisUnitsReal : Basis (Option (Fin (rank K))) ℝ (InfinitePlace K → ℝ) :=
  (completeBasis K).reindex (unitsIdx K).symm

theorem basisPlacesReal_eq (i : Option (Fin (rank K))) :
    basisPlacesReal K i = intCastVec K (basisPlaces K i) := by
  classical
  funext w
  simp only [basisPlacesReal, basisPlaces, Basis.reindex_apply, Equiv.symm_symm,
    Pi.basisFun_apply, intCastVec, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.single_apply]
  split <;> simp

theorem basisUnitsReal_eq (i : Option (Fin (rank K))) :
    basisUnitsReal K i = unitEmbed K (basisUnits K i) := by
  cases i with
  | none =>
    have h1 : (basisUnits K none).1 = 0 := by
      simp only [basisUnits, Basis.reindex_apply, Equiv.symm_symm, Equiv.optionEquivSumPUnit_none]
      exact Basis.prod_apply_inr_fst _ _ _
    have h2 : (basisUnits K none).2 = 1 := by
      simp only [basisUnits, Basis.reindex_apply, Equiv.symm_symm, Equiv.optionEquivSumPUnit_none]
      rw [Basis.prod_apply_inr_snd, Basis.singleton_apply]
    funext w
    simp only [basisUnitsReal, Basis.reindex_apply, Equiv.symm_symm, unitsIdx_none,
      completeBasis_apply_of_eq, unitEmbed, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h1, h2,
      Submodule.coe_zero, Pi.add_apply, Pi.zero_apply, zero_add, one_zsmul, multVec]
  | some j =>
    have h1 : (basisUnits K (some j)).1 = basisUnitLatticeFull K j := by
      simp only [basisUnits, Basis.reindex_apply, Equiv.symm_symm, Equiv.optionEquivSumPUnit_some]
      exact Basis.prod_apply_inl_fst _ _ _
    have h2 : (basisUnits K (some j)).2 = 0 := by
      simp only [basisUnits, Basis.reindex_apply, Equiv.symm_symm, Equiv.optionEquivSumPUnit_some]
      exact Basis.prod_apply_inl_snd _ _ _
    funext w
    rw [basisUnitsReal, Basis.reindex_apply, Equiv.symm_symm, unitsIdx_some,
      completeBasis_apply_of_ne K (equivFinRank j), Equiv.symm_apply_apply, expMap_symm_apply,
      normAtAllPlaces_mixedEmbedding]
    show _ = (basisUnits K (some j)).1.1 w + (basisUnits K (some j)).2 • multVec K w
    rw [h1, h2, coe_basisUnitLatticeFull, fullLog_apply, zero_zsmul, add_zero]

/-! ### The intertwining endomorphism -/

variable {k : Type*} [Field k] [Algebra k K]

/-- **The action of a field automorphism on the real valued functions on the infinite places.** -/
noncomputable def placeAct (σ : Gal(K/k)) :
    (InfinitePlace K → ℝ) →ₗ[ℝ] (InfinitePlace K → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun w => σ⁻¹ • w)

omit [NumberField K] in
@[simp]
theorem placeAct_apply (σ : Gal(K/k)) (f : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    placeAct σ f w = f (σ⁻¹ • w) := rfl

omit [NumberField K] in
theorem intCastVec_equivariant (σ : Gal(K/k)) (a : InfinitePlace K → ℤ) :
    intCastVec K (permLatticeAut (toPerm σ⁻¹ : Equiv.Perm (InfinitePlace K)) a)
      = placeAct σ (intCastVec K a) := rfl

theorem unitEmbed_equivariant (σ : Gal(K/k)) (b : unitLatticeFull K × ℤ) :
    unitEmbed K (prodAut (unitLatticeFullAut σ) 1 b) = placeAct σ (unitEmbed K b) := by
  funext w
  show ((unitLatticeFullAut σ b.1 : unitLatticeFull K) : InfinitePlace K → ℝ) w
      + b.2 • multVec K w
    = (b.1 : InfinitePlace K → ℝ) (σ⁻¹ • w) + b.2 • multVec K (σ⁻¹ • w)
  rw [coe_unitLatticeFullAut_apply, multVec, multVec, mult_smul]

/-! ### The comparison of the two lattices -/

/-- **The unit lattice and the free lattice on the infinite places have Herbrand quotients
differing by the degree.** -/
theorem herbrand_unitLatticeFull_mul {σ : Gal(K/k)} {n : ℕ} (hn : n ≠ 0) (hσ : σ ^ n = 1) :
    herbrand (unitLatticeFullAut σ) n * n
      = herbrand (permLatticeAut (toPerm σ⁻¹ : Equiv.Perm (InfinitePlace K))) n := by
  have hperm : (toPerm σ⁻¹ : Equiv.Perm (InfinitePlace K)) ^ n = 1 := by
    show (MulAction.toPermHom Gal(K/k) (InfinitePlace K) σ⁻¹) ^ n = 1
    rw [← map_pow, inv_pow, hσ, inv_one, map_one]
  have key := herbrand_eq_of_real_basis (A := InfinitePlace K → ℤ)
    (B := unitLatticeFull K × ℤ) hn (permLatticeAut_pow_eq_one hperm)
    (prodAut_pow_eq_one (unitLatticeFullAut_pow_eq_one hσ) (one_pow n))
    (basisPlaces K) (basisUnits K) (basisPlacesReal K) (basisUnitsReal K)
    (placeAct σ) (intCastVec K) (unitEmbed K) (intCastVec_equivariant σ)
    (unitEmbed_equivariant σ) (basisPlacesReal_eq (K := K)) (basisUnitsReal_eq (K := K))
  rw [herbrand_prodAut, herbrand_int n hn] at key
  exact key.symm

/-! ### The Herbrand quotient of the units -/

variable [NumberField k] [IsGalois k K]

/-- **The Herbrand quotient of the units of a cyclic extension of number fields**, times the
degree, is the product of the orders of the decomposition groups at the infinite places. -/
theorem herbrand_unitsAutHom_mul {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ)
    {n : ℕ} [NeZero n] (hn : Nat.card Gal(K/k) = n) :
    herbrand (unitsAutHom σ) n * n
      = ∏ v : InfinitePlace k, (Nat.card (stabilizer Gal(K/k) (placeAbove k K v)) : ℚ) := by
  have hσ : σ ^ n = 1 := by rw [← hn]; exact pow_card_eq_one'
  rw [herbrand_unitsAutHom hσ, herbrand_unitLatticeFull_mul (NeZero.ne n) hσ]
  refine herbrand_permLatticeAut_infinitePlace (σ := σ⁻¹) (fun g => ?_) hn
  rw [Subgroup.zpowers_inv]
  exact hgen g

open scoped Classical in
/-- **The Herbrand quotient of the units of a cyclic extension of number fields**, times the
degree, is a power of two, one factor for each ramified infinite place of the base field. -/
theorem herbrand_unitsAutHom_ramified {σ : Gal(K/k)}
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ} [NeZero n]
    (hn : Nat.card Gal(K/k) = n) :
    herbrand (unitsAutHom σ) n * n
      = ∏ v : InfinitePlace k, if (placeAbove k K v).IsUnramified k then (1 : ℚ) else 2 := by
  have hσ : σ ^ n = 1 := by rw [← hn]; exact pow_card_eq_one'
  rw [herbrand_unitsAutHom hσ, herbrand_unitLatticeFull_mul (NeZero.ne n) hσ]
  refine herbrand_permLatticeAut_infinitePlace_ramified (σ := σ⁻¹) (fun g => ?_) hn
  rw [Subgroup.zpowers_inv]
  exact hgen g

end InverseGalois.CFT
