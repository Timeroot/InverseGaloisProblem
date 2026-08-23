import Mathlib
import InverseGalois.CFT.Brauer.CrossedProduct

/-!
# Crossed products are central simple algebras

Let `L / K` be a finite Galois extension of fields with group `G = Gal(L/K)` and let
`f : G × G → Lˣ` be a multiplicative `2`-cocycle.  This file shows that the crossed product
`InverseGalois.CFT.CrossedProduct hf` is a simple ring, and bundles it as an object of `CSA K`,
the category of finite-dimensional central simple `K`-algebras.

The argument is the classical one.  Each symbol `u g` is invertible, so an element `a * u g`
with `a ≠ 0` is a unit.  Given a nonzero two-sided ideal `I`, pick `x ∈ I` nonzero whose
support (as a finitely supported function on `G`) has minimal cardinality, and pick `g₀` in that
support.  For every `c : L` the element `x * incl c - incl (g₀ c) * x` again lies in `I`, has
support contained in the support of `x` with `g₀` removed, and is therefore zero.  Hence every
`g` in the support of `x` agrees with `g₀` on all of `L`, so `x = a * u g₀` is a unit and
`I = ⊤`.

## Main results

* `InverseGalois.CFT.CrossedProduct.isUnit_single`: `a * u g` is a unit whenever `a ≠ 0`.
* `InverseGalois.CFT.CrossedProduct.instIsSimpleRing`: the crossed product is a simple ring.
* `InverseGalois.CFT.CrossedProduct.instFiniteDimensional`: the crossed product is a
  finite-dimensional `K`-algebra.
* `InverseGalois.CFT.CrossedProduct.csa`: the crossed product as an object of `CSA K`.
-/

universe u v

namespace InverseGalois.CFT

open groupCohomology

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  {f : Gal(L/K) × Gal(L/K) → Lˣ}

namespace CrossedProduct

variable {hf : IsMulCocycle₂ f}

/-- The element `c * u 1` is the image under `incl` of `c * f (1, 1)`. -/
theorem single_one_eq_incl (c : L) :
    single hf 1 c = incl hf (c * ((f (1, 1) : Lˣ) : L)) := by
  rw [incl_eq_single]
  refine single_congr ?_
  linear_combination (-c) * val_mul_inv_val (f := f)

/-- Every element `a * u g` factors as the image of `a` times the symbol `u g`. -/
theorem single_eq_incl_mul (g : Gal(L/K)) (a : L) :
    single hf g a = incl hf a * single hf g 1 := by
  rw [incl_mul, smul_single, mul_one]

/-- The image of a nonzero element of `L` in the crossed product is a unit. -/
theorem isUnit_incl {a : L} (ha : a ≠ 0) : IsUnit (incl hf a) :=
  (incl hf).isUnit_map ha.isUnit

/-- Applying `g` after `g⁻¹` is the identity on `L`. -/
theorem apply_inv_apply (g : Gal(L/K)) (c : L) : g (g⁻¹ c) = c := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

/-- The symbol `u g` is a unit of the crossed product. -/
theorem isUnit_single_one (hf : IsMulCocycle₂ f) (g : Gal(L/K)) :
    IsUnit (single hf g 1) := by
  set w : CrossedProduct hf :=
    single hf g⁻¹ (g⁻¹ ((((f (g, g⁻¹))⁻¹ : Lˣ) : L) * (((f (1, 1))⁻¹ : Lˣ) : L))) with hw
  set z : CrossedProduct hf :=
    single hf g⁻¹ ((((f (g⁻¹, g))⁻¹ : Lˣ) : L) * (((f (1, 1))⁻¹ : Lˣ) : L)) with hz
  have hvw : single hf g 1 * w = 1 := by
    rw [hw, single_mul_single, mul_inv_cancel, apply_inv_apply, one_def]
    refine single_congr ?_
    linear_combination (((f (1, 1))⁻¹ : Lˣ) : L) * Units.inv_mul (f (g, g⁻¹))
  have hzv : z * single hf g 1 = 1 := by
    rw [hz, single_mul_single, inv_mul_cancel, map_one, one_def]
    refine single_congr ?_
    linear_combination (((f (1, 1))⁻¹ : Lˣ) : L) * Units.inv_mul (f (g⁻¹, g))
  have hwz : w = z := by rw [← one_mul w, ← hzv, mul_assoc, hvw, mul_one]
  exact ⟨⟨single hf g 1, w, hvw, by rw [hwz]; exact hzv⟩, rfl⟩

/-- An element `a * u g` of the crossed product with `a ≠ 0` is a unit. -/
theorem isUnit_single {g : Gal(L/K)} {a : L} (ha : a ≠ 0) : IsUnit (single hf g a) := by
  rw [single_eq_incl_mul]
  exact (isUnit_incl ha).mul (isUnit_single_one hf g)

/-- The crossed product is a nontrivial ring. -/
instance instNontrivial : Nontrivial (CrossedProduct hf) := by
  refine ⟨1, 0, fun h => ?_⟩
  have h' := congrArg (fun z : CrossedProduct hf => toFinsupp z (1 : Gal(L/K))) h
  simp [one_def] at h'

/-- Coordinates of a difference are the differences of the coordinates. -/
theorem toFinsupp_sub (x y : CrossedProduct hf) (g : Gal(L/K)) :
    toFinsupp (x - y) g = toFinsupp x g - toFinsupp y g := rfl

/-- The commutator of an element with the image of `c : L`, read off in the coordinate `g`. -/
theorem toFinsupp_commutator (x : CrossedProduct hf) (c : L) (g₀ g : Gal(L/K)) :
    toFinsupp (x * incl hf c - incl hf (g₀ c) * x) g = (g c - g₀ c) * toFinsupp x g := by
  rw [toFinsupp_sub, toFinsupp_mul_incl, toFinsupp_incl_mul, sub_mul]

/-- A crossed product algebra over a field is a simple ring. -/
instance instIsSimpleRing : IsSimpleRing (CrossedProduct hf) := by
  classical
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  rw [or_iff_not_imp_left, ← I.one_mem_iff]
  intro hI
  obtain ⟨x₀, hx₀I, hx₀⟩ : ∃ y ∈ I, y ≠ 0 :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : (⊥ : TwoSidedIdeal (CrossedProduct hf)) < I)
  have hex : ∃ n : ℕ, ∃ y, y ∈ I ∧ y ≠ 0 ∧ (toFinsupp y).support.card = n :=
    ⟨_, x₀, hx₀I, hx₀, rfl⟩
  obtain ⟨x, hxI, hx0, hxcard⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ I, y ≠ 0 → Nat.find hex ≤ (toFinsupp y).support.card :=
    fun y hy hy0 => Nat.find_min' hex ⟨y, hy, hy0, rfl⟩
  have hsne : (toFinsupp x).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact fun h => hx0 (toFinsupp_injective (h.trans toFinsupp_zero.symm))
  obtain ⟨g₀, hg₀⟩ := hsne
  have hg₀ne : toFinsupp x g₀ ≠ 0 := Finsupp.mem_support_iff.1 hg₀
  have key : ∀ g ∈ (toFinsupp x).support, g = g₀ := by
    intro g hg
    have hgne : toFinsupp x g ≠ 0 := Finsupp.mem_support_iff.1 hg
    refine AlgEquiv.ext fun c => ?_
    have hyI : x * incl hf c - incl hf (g₀ c) * x ∈ I :=
      I.sub_mem (I.mul_mem_right _ _ hxI) (I.mul_mem_left _ _ hxI)
    have hysupp : (toFinsupp (x * incl hf c - incl hf (g₀ c) * x)).support ⊆
        (toFinsupp x).support.erase g₀ := by
      intro j hj
      rw [Finsupp.mem_support_iff, toFinsupp_commutator] at hj
      refine Finset.mem_erase.2 ⟨?_, Finsupp.mem_support_iff.2 fun h => hj (by rw [h, mul_zero])⟩
      rintro rfl
      exact hj (by rw [sub_self, zero_mul])
    have hycard : (toFinsupp (x * incl hf c - incl hf (g₀ c) * x)).support.card < Nat.find hex :=
      lt_of_le_of_lt (Finset.card_le_card hysupp)
        (hxcard ▸ Finset.card_erase_lt_of_mem hg₀)
    have hy0 : x * incl hf c - incl hf (g₀ c) * x = 0 := by
      by_contra h
      exact absurd (hmin _ hyI h) (not_le.2 hycard)
    have hcoord := toFinsupp_commutator x c g₀ g
    rw [hy0] at hcoord
    simp only [toFinsupp_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoord
    rcases mul_eq_zero.1 hcoord.symm with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hgne
  have hxeq : x = single hf g₀ (toFinsupp x g₀) := by
    refine toFinsupp_injective ?_
    rw [toFinsupp_single]
    ext j
    by_cases h : j = g₀
    · subst h
      rw [Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne h]
      by_contra hne
      exact h (key j (Finsupp.mem_support_iff.2 hne))
  obtain ⟨y, hy⟩ := isUnit_single (hf := hf) (g := g₀) hg₀ne
  have hmem : (↑y⁻¹ * x : CrossedProduct hf) ∈ I := I.mul_mem_left _ _ hxI
  rwa [hxeq, ← hy, y.inv_mul] at hmem

/-- A crossed product for a finite extension is finite-dimensional over the base field. -/
instance instFiniteDimensional [FiniteDimensional K L] :
    FiniteDimensional K (CrossedProduct hf) :=
  haveI : Module.Finite L (CrossedProduct hf) := Module.Finite.of_basis (basisUnits hf)
  Module.Finite.trans L (CrossedProduct hf)

/-- The crossed product of a finite Galois extension by a multiplicative `2`-cocycle, as a
finite-dimensional central simple algebra over the base field. -/
noncomputable def csa (hf : IsMulCocycle₂ f) [FiniteDimensional K L] [IsGalois K L] :
    CSA.{u, v} K where
  toAlgCat := AlgCat.of K (CrossedProduct hf)

end CrossedProduct

end InverseGalois.CFT
