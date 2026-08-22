import Mathlib

/-!
# `ℚ_[p]` is a nonarchimedean local field

Mathlib's `IsNonarchimedeanLocalField` packages, for a topological field `K` carrying a
`ValuativeRel`, the three requirements that the topology be the valuation topology, that `K` be
locally compact, and that the valuation be nontrivial.  This file supplies the first instance of
that class, namely the field `ℚ_[p]` of `p`-adic numbers.

Two of the three requirements are already available in Mathlib: `Padic.instIsNontrivial` records
the nontriviality of the `p`-adic valuation, and `ProperSpace ℚ_[p]` gives local compactness.  The
content here is the comparison of the metric topology of `ℚ_[p]` with the topology defined by the
valuative relation.  The comparison is obtained by exhibiting the `ℝ≥0`-valued valuation
`NormedField.valuation`, which is literally `‖·‖₊`, as a valuation compatible with the valuative
relation of `ℚ_[p]`; the canonical valuation is then equivalent to the norm, so that valuation
balls and metric balls around `0` coincide.

Once the class is available, its consequences specialise to `ℚ_[p]`: the valuation ring is a
discrete valuation ring, it is compact, and the residue field is finite.  The valuation ring is
moreover the ring `ℤ_[p]` of `p`-adic integers.

## Main results

* `InverseGalois.CFT.Local.padicNormedFieldValuationCompatible`: the norm of `ℚ_[p]`, viewed as an
  `ℝ≥0`-valued valuation, is compatible with the valuative relation of `ℚ_[p]`.
* `InverseGalois.CFT.Local.padic_valuation_lt_iff_norm_lt`,
  `InverseGalois.CFT.Local.padic_valuation_le_one_iff_norm_le_one`: the dictionary between the
  canonical valuation of `ℚ_[p]` and the `p`-adic norm.
* `InverseGalois.CFT.Local.padicIsValuativeTopology`: the metric topology of `ℚ_[p]` is the
  valuation topology.
* `InverseGalois.CFT.Local.padicIsNonarchimedeanLocalField`: `ℚ_[p]` is a nonarchimedean local
  field.
* `InverseGalois.CFT.Local.padicIntegerRingEquiv`: the valuation ring `𝒪[ℚ_[p]]` is the ring
  `ℤ_[p]` of `p`-adic integers.
* `InverseGalois.CFT.Local.padic_isDiscreteValuationRing_integer`,
  `InverseGalois.CFT.Local.padic_compactSpace_integer`,
  `InverseGalois.CFT.Local.padic_completeSpace_integer`,
  `InverseGalois.CFT.Local.padic_finite_residueField`: the standard properties of `𝒪[ℚ_[p]]` that
  come with the class.

## Tags

p-adic, local field, valuation, valuative relation
-/

open ValuativeRel WithZero

variable {p : ℕ} [hp : Fact p.Prime]

namespace InverseGalois.CFT.Local

/-- The `p`-adic norm, viewed as an `ℝ≥0`-valued valuation on `ℚ_[p]` through
`NormedField.valuation`, is compatible with the valuative relation of `ℚ_[p]`: one `p`-adic
number is valuatively below another exactly when its norm is smaller. -/
instance padicNormedFieldValuationCompatible :
    (NormedField.valuation (K := ℚ_[p])).Compatible where
  vle_iff_le x y := by
    rw [Valuation.vle_iff_le (Padic.mulValuation (p := p))]
    simp only [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm,
      Padic.mulValuation_toFun]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp [hx]
    · have h1p : (1 : ℝ) < p := mod_cast hp.out.one_lt
      rw [if_neg hx, if_neg hy, Padic.norm_eq_zpow_neg_valuation hx,
        Padic.norm_eq_zpow_neg_valuation hy, exp_le_exp, zpow_le_zpow_iff_right₀ h1p]

/-- The canonical valuation of `ℚ_[p]` orders `p`-adic numbers exactly as the `p`-adic norm
does. -/
theorem padic_valuation_lt_iff_norm_lt {x y : ℚ_[p]} :
    valuation ℚ_[p] x < valuation ℚ_[p] y ↔ ‖x‖ < ‖y‖ := by
  rw [(ValuativeRel.isEquiv (valuation ℚ_[p]) NormedField.valuation).lt_iff_lt]
  simp [← NNReal.coe_lt_coe]

/-- A `p`-adic number lies in the valuation ring of `ℚ_[p]` exactly when its norm is at most
one, that is, exactly when it is a `p`-adic integer. -/
theorem padic_valuation_le_one_iff_norm_le_one {x : ℚ_[p]} :
    valuation ℚ_[p] x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  have h := ValuativeRel.isEquiv (valuation ℚ_[p]) NormedField.valuation x 1
  simpa [← NNReal.coe_le_coe] using h

/-- The metric topology of `ℚ_[p]` is the topology defined by its valuative relation: the metric
balls around `0` are exactly the valuation balls around `0`. -/
instance padicIsValuativeTopology : IsValuativeTopology ℚ_[p] := by
  refine IsValuativeTopology.of_zero fun s => ⟨fun hs => ?_, ?_⟩
  · obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨a, ha0, haε⟩ := NormedField.exists_norm_lt ℚ_[p] hε
    have ha : a ≠ 0 := norm_pos_iff.mp ha0
    refine ⟨Units.mk0 (valuation ℚ_[p] a) (by simpa using ha), fun z hz => ?_⟩
    simp only [Units.val_mk0, Set.mem_setOf_eq, padic_valuation_lt_iff_norm_lt] at hz
    exact hεs (mem_ball_zero_iff.mpr (hz.trans haε))
  · rintro ⟨γ, hγ⟩
    obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero ℚ_[p])
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact γ.ne_zero (by simpa using ha.symm)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 (norm_pos_iff.mpr ha0)) fun z hz => ?_
    refine hγ ?_
    simp only [Set.mem_setOf_eq, ← ha, padic_valuation_lt_iff_norm_lt]
    exact mem_ball_zero_iff.mp hz

/-- The field `ℚ_[p]` of `p`-adic numbers is a nonarchimedean local field. -/
instance padicIsNonarchimedeanLocalField : IsNonarchimedeanLocalField ℚ_[p] := {}

/-- The valuation ring of `ℚ_[p]` is a discrete valuation ring. -/
theorem padic_isDiscreteValuationRing_integer : IsDiscreteValuationRing 𝒪[ℚ_[p]] := inferInstance

/-- The valuation ring of `ℚ_[p]` is compact. -/
theorem padic_compactSpace_integer : CompactSpace 𝒪[ℚ_[p]] := inferInstance

/-- The valuation ring of `ℚ_[p]` is complete. -/
theorem padic_completeSpace_integer : CompleteSpace 𝒪[ℚ_[p]] := inferInstance

/-- The residue field of `ℚ_[p]` is finite. -/
theorem padic_finite_residueField : Finite 𝓀[ℚ_[p]] := inferInstance

/-- The valuation of `ℚ_[p]` is discrete. -/
theorem padic_isDiscrete : ValuativeRel.IsDiscrete ℚ_[p] := inferInstance

/-- The valuation ring of `ℚ_[p]` is the ring `ℤ_[p]` of `p`-adic integers: both are the subring
of elements of norm at most one. -/
def padicIntegerRingEquiv : 𝒪[ℚ_[p]] ≃+* ℤ_[p] where
  toFun x := ⟨x.1, padic_valuation_le_one_iff_norm_le_one.mp x.2⟩
  invFun x := ⟨x.1, padic_valuation_le_one_iff_norm_le_one.mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The identification of `𝒪[ℚ_[p]]` with `ℤ_[p]` does not move elements of `ℚ_[p]`. -/
@[simp]
theorem coe_padicIntegerRingEquiv (x : 𝒪[ℚ_[p]]) : (padicIntegerRingEquiv x : ℚ_[p]) = x := rfl

end InverseGalois.CFT.Local
