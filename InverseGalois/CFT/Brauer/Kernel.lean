import Mathlib
import InverseGalois.CFT.Brauer.CrossedProductCohomologous
import InverseGalois.CFT.Brauer.CrossedProductSplit
import InverseGalois.CFT.Brauer.CrossedProductSplitting
import InverseGalois.CFT.Brauer.CyclicAlgebra
import InverseGalois.CFT.Brauer.Split
import InverseGalois.CFT.GroupCohomology.Cohomologous

/-!
# The kernel of the crossed product map

Let `L / K` be a finite Galois extension.  Attaching to a multiplicative `2`-cocycle
`f : Gal(L/K) × Gal(L/K) → Lˣ` the class of its crossed product gives a map from cocycles to the
relative Brauer group `Br(L / K)`.  This file computes exactly when that class is trivial: the
Brauer class of a crossed product vanishes if and only if the cocycle is a coboundary, that is, if
and only if its class in `H²(Gal(L/K), Lˣ)` vanishes.

One direction is the statement that a coboundary has a matrix crossed product; the other needs the
uniqueness half of Wedderburn's theorem, which turns a trivial Brauer class into an honest
isomorphism with a matrix algebra over `K`.

Specialising to a cyclic extension computes `Br(L / K)` on the nose in the classical way: the
cyclic algebra of a unit `a` of `K` is trivial in the Brauer group exactly when `a` is a norm from
`L`, so a unit that is not a norm produces a genuinely nontrivial Brauer class.

## Main results

* `InverseGalois.CFT.CrossedProduct.mk_csa_eq_one_iff`: the Brauer class of a crossed product is
  trivial exactly when the cocycle is a coboundary.
* `InverseGalois.CFT.CrossedProduct.mk_csa_eq_one_iff_H2π_eq_zero`: the same, phrased through the
  class of the cocycle in the second cohomology group.
* `InverseGalois.CFT.mk_cyclicAlgebra_eq_one_iff`: a cyclic algebra is trivial in the Brauer group
  exactly when its unit is a norm.
* `InverseGalois.CFT.exists_mk_ne_one_mem_relative_of_not_norm`: a unit of `K` that is not a norm
  from a cyclic extension `L` produces a nontrivial class in the relative Brauer group `Br(L / K)`.
-/

universe u

open Module

namespace InverseGalois.CFT

open groupCohomology

/-! ### The kernel, in terms of coboundaries -/

section Coboundary

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {f : Gal(L/K) × Gal(L/K) → Lˣ}

namespace CrossedProduct

/-- **The Brauer class of a crossed product is trivial exactly when the cocycle is a
coboundary.** -/
theorem mk_csa_eq_one_iff (hf : IsMulCocycle₂ f) :
    (⟦csa hf⟧ : BrauerGroup K) = 1 ↔ IsMulCoboundary₂ f := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨n, -, ⟨e⟩⟩ := BrauerGroup.exists_algEquiv_matrix_of_mk_eq_one (csa hf) h
    exact isMulCoboundary₂_of_algEquivMatrix e
  · obtain ⟨e⟩ := nonempty_algEquivMatrix_of_isMulCoboundary₂ hf h
    exact BrauerGroup.mk_eq_one_of_algEquiv_matrix Module.finrank_pos.ne' e

end CrossedProduct

end Coboundary

/-! ### The kernel, in terms of the second cohomology group -/

section Cohomology

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {f : Gal(L/K) × Gal(L/K) → Lˣ}

namespace CrossedProduct

/-- **The Brauer class of a crossed product is trivial exactly when the class of the cocycle in
`H²(Gal(L/K), Lˣ)` vanishes.** -/
theorem mk_csa_eq_one_iff_H2π_eq_zero (hf : IsMulCocycle₂ f) :
    (⟦csa hf⟧ : BrauerGroup K) = 1 ↔
      H2π (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) (cocyclesOfIsMulCocycle₂ hf) = 0 :=
  (mk_csa_eq_one_iff hf).trans (H2π_eq_zero_iff_isMulCoboundary₂ hf).symm

end CrossedProduct

end Cohomology

/-! ### The cyclic case -/

section Cyclic

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **A cyclic algebra is trivial in the Brauer group exactly when its unit is a norm.**  This is
the concrete form of the isomorphism `Br(L / K) ≅ Kˣ / N(Lˣ)` for a cyclic extension. -/
theorem mk_cyclicAlgebra_eq_one_iff {σ₀ : Gal(L/K)}
    (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) (a : Kˣ) :
    (⟦CrossedProduct.csa (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)⟧ : BrauerGroup K) = 1 ↔
      ∃ b : Lˣ, Algebra.norm K (b : L) = (a : K) :=
  (CrossedProduct.mk_csa_eq_one_iff _).trans (isMulCoboundary₂_cyclicUnitCocycle_iff hσ₀ a)

/-- **A unit that is not a norm gives a nontrivial class in the relative Brauer group.**  For a
cyclic extension `L / K` and a unit `a` of `K` that is not a norm from `L`, the cyclic algebra of
`a` has a nontrivial class in `Br(L / K)`. -/
theorem exists_mk_ne_one_mem_relative_of_not_norm [IsCyclic Gal(L/K)] {a : Kˣ}
    (ha : ¬ ∃ b : Lˣ, Algebra.norm K (b : L) = (a : K)) :
    ∃ A : CSA.{u, u} K, (⟦A⟧ : BrauerGroup K) ∈ BrauerGroup.relative K L ∧
      (⟦A⟧ : BrauerGroup K) ≠ 1 := by
  obtain ⟨σ₀, hσ₀⟩ := exists_generator_of_isCyclic (K := K) (L := L)
  exact ⟨CrossedProduct.csa (isMulCocycle₂_cyclicUnitCocycle hσ₀ a),
    mk_cyclicAlgebra_mem_relative hσ₀ a,
    fun h => ha ((mk_cyclicAlgebra_eq_one_iff hσ₀ a).mp h)⟩

/-- The relative Brauer group of a cyclic extension is nontrivial as soon as some unit of the base
field fails to be a norm. -/
theorem nontrivial_relative_of_not_norm [IsCyclic Gal(L/K)] {a : Kˣ}
    (ha : ¬ ∃ b : Lˣ, Algebra.norm K (b : L) = (a : K)) :
    ∃ x ∈ BrauerGroup.relative K L, x ≠ (1 : BrauerGroup K) := by
  obtain ⟨A, hmem, hne⟩ := exists_mk_ne_one_mem_relative_of_not_norm (L := L) ha
  exact ⟨⟦A⟧, hmem, hne⟩

end Cyclic

end InverseGalois.CFT
