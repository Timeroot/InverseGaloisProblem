/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.Place

/-!
# Charts covering the places of a field

A place of `F` containing a Dedekind chart is the place of a unique prime of that chart.  To use
the correspondence one has to know that a place contains a chart in the first place, and that is
what integrality supplies: a valuation subring is integrally closed, so it contains everything
integral over any subring it contains.  Since a chart is by construction the integral closure of a
polynomial subring, containing the polynomial subring is enough.

Which polynomial subring a given place contains is decided by the defining property of a valuation
subring: of a function and its reciprocal, at least one is regular at the place.  So of the two
charts cut out by a parameter `x` and by its reciprocal, at least one is contained in any given
place of `F` over the constants — the two charts cover the places, as the two affine charts of the
projective line cover its points.

## Main results

* `Rigidity.RET.mem_of_isIntegral` — a valuation subring contains everything integral over a
  subring it contains.
* `Rigidity.RET.existsUnique_place` — a proper place containing a chart is the place of exactly one
  prime of the chart.
* `Rigidity.RET.isIntegral_mem_or` — the charts of a parameter and of its reciprocal cover the
  places over the constants.
-/

open IsDedekindDomain

noncomputable section


namespace Rigidity.RET

variable {F : Type*} [Field F]

/-! ## A valuation subring is integrally closed -/

/-- **A valuation subring is the ring of integers of its own valuation.** -/
theorem valuationSubring_integers (A : ValuationSubring F) : A.valuation.Integers A where
  hom_inj := Subtype.coe_injective
  map_le_one := A.valuation_le_one
  exists_of_le_one := fun r hr => ⟨⟨r, A.mem_of_valuation_le_one r hr⟩, rfl⟩

/-- **A valuation subring contains everything integral over a subring it contains.**

A monic equation with coefficients of valuation at most one forces its root to have valuation at
most one: were the valuation larger, the leading term would dominate every other term of the
equation, so the sum could not vanish. -/
theorem mem_of_isIntegral {A : ValuationSubring F} {R : Subring F} (hR : R ≤ A.toSubring) {x : F}
    (hx : IsIntegral R x) : x ∈ A := by
  letI : Algebra R A := (Subring.inclusion hR).toAlgebra
  haveI : IsScalarTower R A F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact A.mem_of_valuation_le_one x
    ((valuationSubring_integers A).isIntegral_iff_v_le_one.mp hx.tower_top)

/-! ## A chart determines the places containing it -/

variable {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]

/-- **A proper place containing a chart is the place of exactly one prime of the chart.** -/
theorem existsUnique_place (A : ValuationSubring F) (hBA : ∀ b : B, algebraMap B F b ∈ A)
    (hA : A ≠ ⊤) : ∃! v : HeightOneSpectrum B, placeSubring F v = A :=
  ⟨underPlace A hBA hA, placeSubring_underPlace A hBA hA, fun _ hv =>
    placeSubring_injective F (hv.trans (placeSubring_underPlace A hBA hA).symm)⟩

/-- **A chart integral over a subring of a place lies in that place**, so the place is the place of
exactly one of its primes. -/
theorem existsUnique_place_of_isIntegral {A : ValuationSubring F} {R : Subring F}
    (hR : R ≤ A.toSubring) (hA : A ≠ ⊤) (hB : ∀ b : B, IsIntegral R (algebraMap B F b)) :
    ∃! v : HeightOneSpectrum B, placeSubring F v = A :=
  existsUnique_place A (fun b => mem_of_isIntegral hR (hB b)) hA

/-! ## The two charts of a parameter -/

/-- **Of a parameter and its reciprocal, one generates a subring of any given place.** -/
theorem closure_le_or_closure_inv_le (A : ValuationSubring F) {k : Subring F}
    (hk : k ≤ A.toSubring) (x : F) :
    Subring.closure (↑k ∪ {x}) ≤ A.toSubring ∨
      Subring.closure (↑k ∪ {x⁻¹}) ≤ A.toSubring := by
  rcases A.mem_or_inv_mem x with hx | hx
  · exact Or.inl (Subring.closure_le.mpr
      (Set.union_subset (fun _ hy => hk hy) (Set.singleton_subset_iff.mpr hx)))
  · exact Or.inr (Subring.closure_le.mpr
      (Set.union_subset (fun _ hy => hk hy) (Set.singleton_subset_iff.mpr hx)))

/-- **The two charts of a parameter cover the places over the constants**: every place containing
the constants contains everything integral over the constants and the parameter, or everything
integral over the constants and the reciprocal of the parameter. -/
theorem isIntegral_mem_or (A : ValuationSubring F) {k : Subring F} (hk : k ≤ A.toSubring) (x : F) :
    (∀ y : F, IsIntegral (Subring.closure (↑k ∪ {x})) y → y ∈ A) ∨
      (∀ y : F, IsIntegral (Subring.closure (↑k ∪ {x⁻¹})) y → y ∈ A) := by
  rcases closure_le_or_closure_inv_le A hk x with h | h
  · exact Or.inl fun _ hy => mem_of_isIntegral h hy
  · exact Or.inr fun _ hy => mem_of_isIntegral h hy

end Rigidity.RET
