import Mathlib
import InverseGalois.CFT.Brauer.MaximalSubfield
import InverseGalois.CFT.Brauer.RealPlace

/-!
# The Brauer group of the reals

The complex numbers form an algebraically closed extension of `ℝ` of degree two, so every
finite extension of `ℝ` inside a fixed algebraic closure admits an `ℝ`-embedding into `ℂ`.
Since every Brauer class is split by some finite extension, and since the relative Brauer group
only grows along an extension, this forces every class over `ℝ` to be split by `ℂ`: the relative
Brauer group `Br(ℂ / ℝ)` is the whole of `Br(ℝ)`.  Combined with the computation of `Br(ℂ / ℝ)`
at the real place, this identifies `Br(ℝ)` with the group of order two, the nontrivial class
being that of the Hamilton quaternions.

The same circle of ideas gives a lower bound over `ℚ`: the rational quaternions are a central
simple `ℚ`-algebra which is not a matrix algebra, so `Br(ℚ)` is nontrivial as well.

## Main results

* `InverseGalois.CFT.relative_le_relative_of_algHom`: the relative Brauer group grows along a
  `K`-algebra map `L →ₐ[K] M`.
* `InverseGalois.CFT.relative_real_complex_eq_top`: **every Brauer class over `ℝ` is split
  by `ℂ`**.
* `InverseGalois.CFT.brauerRealEquiv`: **the Brauer group of the reals is cyclic of order two**,
  with the corollaries `InverseGalois.CFT.card_brauerGroup_real`,
  `InverseGalois.CFT.nontrivial_brauerGroup_real`,
  `InverseGalois.CFT.sq_eq_one_brauerGroup_real` and
  `InverseGalois.CFT.eq_of_ne_one_brauerGroup_real`.
* `InverseGalois.CFT.exists_csa_real_unique_ne_one`: the Hamilton quaternions represent the
  unique nontrivial class of `Br(ℝ)`.
* `InverseGalois.CFT.nontrivial_brauerGroup_rat`: **the Brauer group of the rationals is
  nontrivial**.

## Tags

Brauer group, real place, quaternions, central simple algebra
-/

universe u

namespace InverseGalois.CFT

/-! ### Transporting the relative Brauer group along an algebra map -/

/-- **A class split by `L` is split by any `K`-algebra receiving `L`.**  An algebra map
`L →ₐ[K] M` makes `M` an extension of `L`, so the monotonicity of the relative Brauer group in a
tower applies. -/
theorem relative_le_relative_of_algHom {K L M : Type u} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] (φ : L →ₐ[K] M) :
    BrauerGroup.relative K L ≤ BrauerGroup.relative K M := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  exact BrauerGroup.relative_le_relative K L M

/-! ### Every real Brauer class is split by `ℂ` -/

/-- **The complex numbers split every Brauer class over the reals.**  A class over `ℝ` is split
by some finite extension of `ℝ` inside an algebraic closure; such an extension is algebraic, so
it embeds into the algebraically closed field `ℂ` over `ℝ`, and the splitting is inherited. -/
theorem relative_real_complex_eq_top : BrauerGroup.relative ℝ ℂ = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨F, hF, hx⟩ := exists_intermediateField_mem_relative x
  haveI := hF
  haveI : Algebra.IsAlgebraic ℝ ↥F := Algebra.IsAlgebraic.of_finite ℝ ↥F
  exact relative_le_relative_of_algHom (IsAlgClosed.lift : ↥F →ₐ[ℝ] ℂ) hx

/-! ### The Brauer group of the reals -/

/-- **The Brauer group of the reals is cyclic of order two.**  Every class is split by `ℂ`, so
the Brauer group coincides with the relative Brauer group at the real place. -/
noncomputable def brauerRealEquiv : BrauerGroup ℝ ≃* Multiplicative (ZMod 2) :=
  (Subgroup.topEquiv (G := BrauerGroup ℝ)).symm.trans <|
    (MulEquiv.subgroupCongr relative_real_complex_eq_top.symm).trans brauerRelativeRealEquiv

/-- **The Brauer group of the reals has exactly two elements.** -/
theorem card_brauerGroup_real : Nat.card (BrauerGroup.{0, 0} ℝ) = 2 := by
  rw [Nat.card_congr brauerRealEquiv.toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- **The Brauer group of the reals is nontrivial.** -/
instance nontrivial_brauerGroup_real : Nontrivial (BrauerGroup.{0, 0} ℝ) :=
  brauerRealEquiv.toEquiv.nontrivial

/-- Every Brauer class over the reals has order dividing two. -/
theorem sq_eq_one_brauerGroup_real (x : BrauerGroup.{0, 0} ℝ) : x ^ 2 = 1 :=
  sq_eq_one_of_mem_relative_real x (relative_real_complex_eq_top ▸ Subgroup.mem_top x)

/-- The Brauer group of the reals has a single nontrivial element: any two nontrivial classes
coincide. -/
theorem eq_of_ne_one_brauerGroup_real {x y : BrauerGroup.{0, 0} ℝ} (hx : x ≠ 1) (hy : y ≠ 1) :
    x = y := by
  have h : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by decide
  exact brauerRealEquiv.injective (h _ _ (by simpa using hx) (by simpa using hy))

/-- **The Hamilton quaternions represent the unique nontrivial class of `Br(ℝ)`.**  There is a
central simple `ℝ`-algebra of dimension four whose class is nontrivial, and every nontrivial
class over `ℝ` is that class. -/
theorem exists_csa_real_unique_ne_one :
    ∃ A : CSA.{0, 0} ℝ, Module.finrank ℝ (A : Type) = 4 ∧ (⟦A⟧ : BrauerGroup ℝ) ≠ 1 ∧
      ∀ x : BrauerGroup.{0, 0} ℝ, x ≠ 1 → x = ⟦A⟧ := by
  obtain ⟨A, -, hdim, hmat⟩ := exists_csa_real
  have hne : (⟦A⟧ : BrauerGroup ℝ) ≠ 1 := by
    intro h
    obtain ⟨n, -, he⟩ := (BrauerGroup.mk_eq_one_iff_algEquiv_matrix A).mp h
    exact hmat n he
  exact ⟨A, hdim, hne, fun x hx => eq_of_ne_one_brauerGroup_real hx hne⟩

/-! ### The Brauer group of the rationals -/

/-- **The Brauer group of the rationals is nontrivial.**  The rational quaternions are a central
simple `ℚ`-algebra which is not a matrix algebra over `ℚ`, so their class is not the identity. -/
instance nontrivial_brauerGroup_rat : Nontrivial (BrauerGroup.{0, 0} ℚ) := by
  obtain ⟨A, -, -, hmat⟩ := exists_csa_rat
  refine ⟨⟦A⟧, 1, ?_⟩
  intro h
  obtain ⟨n, -, he⟩ := (BrauerGroup.mk_eq_one_iff_algEquiv_matrix A).mp h
  exact hmat n he

end InverseGalois.CFT
