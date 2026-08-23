import Mathlib
import InverseGalois.CFT.Brauer.MaximalSubfield
import InverseGalois.CFT.Brauer.H2Surjective
import InverseGalois.CFT.Brauer.Tower

/-!
# Every Brauer class over a perfect field is split by a finite Galois extension

Every Brauer class over a field `K` is split by *some* finite extension of `K` inside a fixed
algebraic closure.  When `K` is perfect that extension can be enlarged to a finite **Galois**
extension: replacing a finite intermediate field by its normal closure keeps the extension finite,
makes it normal, and separability is automatic over a perfect field.  Splitting fields only get
better under enlargement, so the normal closure still splits the class.

Combining this with the fact that the relative Brauer group of a finite Galois extension is killed
by the degree of the extension shows that the Brauer group of a perfect field is a torsion group.

## Main results

* `InverseGalois.CFT.exists_isGalois_mem_relative`: every Brauer class over a perfect field lies in
  the relative Brauer group of a finite Galois intermediate field of `AlgebraicClosure K / K`.
* `InverseGalois.CFT.exists_pow_eq_one`: every Brauer class over a perfect field is killed by some
  nonzero natural number.
* `InverseGalois.CFT.isTorsion_brauerGroup`: **the Brauer group of a perfect field is torsion**.
* `InverseGalois.CFT.iSup_relative_isGalois_eq_top`: the Brauer group of a perfect field is the
  union of the relative Brauer groups of the finite Galois intermediate fields of
  `AlgebraicClosure K / K`.

## Tags

Brauer group, splitting field, Galois extension, normal closure, torsion
-/

universe u

open Module

namespace InverseGalois.CFT

/-! ### A finite Galois splitting field -/

/-- **Every Brauer class over a perfect field is split by a finite Galois extension.** The class is
split by some finite intermediate field of `AlgebraicClosure K / K`; the normal closure of that
field is still finite over `K`, is normal by construction and separable because `K` is perfect, and
it splits the class because it contains a splitting field. -/
theorem exists_isGalois_mem_relative {K : Type u} [Field K] [PerfectField K] (x : BrauerGroup K) :
    ∃ L : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K ↥L ∧ IsGalois K ↥L ∧ x ∈ BrauerGroup.relative K ↥L := by
  obtain ⟨F, hF, hx⟩ := exists_intermediateField_mem_relative x
  haveI : FiniteDimensional K ↥F := hF
  set N : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.normalClosure K ↥F (AlgebraicClosure K) with hN
  haveI : FiniteDimensional K ↥N := by rw [hN]; infer_instance
  haveI : Normal K ↥N := by rw [hN]; infer_instance
  haveI : Algebra.IsAlgebraic K ↥N := Algebra.IsAlgebraic.of_finite K _
  exact ⟨N, inferInstance, ⟨⟩, BrauerGroup.relative_mono (IntermediateField.le_normalClosure F) hx⟩

/-! ### The Brauer group of a perfect field is torsion -/

/-- Every Brauer class over a perfect field is killed by a nonzero natural number, namely the
degree of a finite Galois extension splitting it. -/
theorem exists_pow_eq_one {K : Type} [Field K] [PerfectField K] (x : BrauerGroup K) :
    ∃ n : ℕ, n ≠ 0 ∧ x ^ n = 1 := by
  obtain ⟨L, hfin, hgal, hx⟩ := exists_isGalois_mem_relative x
  haveI : FiniteDimensional K ↥L := hfin
  haveI : IsGalois K ↥L := hgal
  exact ⟨finrank K ↥L, Module.finrank_pos.ne', pow_finrank_eq_one_of_mem_relative x hx⟩

/-- **The Brauer group of a perfect field is a torsion group.** -/
theorem isTorsion_brauerGroup {K : Type} [Field K] [PerfectField K] :
    Monoid.IsTorsion (BrauerGroup K) := by
  intro x
  obtain ⟨n, hn, hxn⟩ := exists_pow_eq_one x
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hxn⟩

/-! ### Exhaustion by relative Brauer groups of Galois extensions -/

/-- The Brauer group of a perfect field is exhausted by the relative Brauer groups of the finite
Galois intermediate fields of `AlgebraicClosure K / K`. -/
theorem iSup_relative_isGalois_eq_top {K : Type u} [Field K] [PerfectField K] :
    ⨆ L : {L : IntermediateField K (AlgebraicClosure K) // FiniteDimensional K ↥L ∧ IsGalois K ↥L},
      BrauerGroup.relative K ↥(L : IntermediateField K (AlgebraicClosure K)) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨L, hfin, hgal, hx⟩ := exists_isGalois_mem_relative x
  exact le_iSup
    (fun L : {L : IntermediateField K (AlgebraicClosure K) //
        FiniteDimensional K ↥L ∧ IsGalois K ↥L} =>
      BrauerGroup.relative K ↥(L : IntermediateField K (AlgebraicClosure K))) ⟨L, hfin, hgal⟩ hx

end InverseGalois.CFT
