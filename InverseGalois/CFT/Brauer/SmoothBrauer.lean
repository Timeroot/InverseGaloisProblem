/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.GaloisSplitting
import InverseGalois.CFT.Brauer.InflateTower

/-!
# The Brauer group of a perfect field is a smooth second cohomology group

Every Brauer class over a perfect field is split by a finite Galois subextension of a fixed
algebraic closure, and a class split by a finite Galois extension is the class of a crossed
product of that extension.  Inflating the cocycle to the whole algebraic closure produces a smooth
two cohomology class of the absolute Galois group whose Brauer class is the one we started with,
so the homomorphism of the previous file is surjective.  Together with its injectivity this
identifies the Brauer group of a perfect field with the smooth second cohomology of its absolute
Galois group with coefficients in the units of an algebraic closure.

## Main results

* `InverseGalois.CFT.exists_mk_csa_eq_of_mem_relative`: **every Brauer class split by a finite
  Galois extension is the class of a crossed product of that extension.**
* `InverseGalois.CFT.smoothBrauerHom_surjective`: **the homomorphism from the smooth second
  cohomology to the Brauer group is surjective.**
* `InverseGalois.CFT.smoothBrauerEquiv`: **the Brauer group of a perfect field is the smooth
  second cohomology of its absolute Galois group with coefficients in the units of an algebraic
  closure.**

## Tags

Brauer group, crossed product, Galois cohomology, absolute Galois group, class field theory
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

universe u

namespace InverseGalois.CFT

open groupCohomology Module

/-! ### Surjectivity onto a relative Brauer group -/

section Relative

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Every Brauer class split by a finite Galois extension is the class of a crossed product of
that extension.**  A class of the relative Brauer group is represented by a central simple algebra
of dimension the square of the degree containing a copy of the extension, and such an algebra is a
crossed product. -/
theorem exists_mk_csa_eq_of_mem_relative (x : BrauerGroup K)
    (hx : x ∈ BrauerGroup.relative K L) :
    ∃ (c : Gal(L/K) × Gal(L/K) → Lˣ) (hc : IsMulCocycle₂ c),
      (⟦CrossedProduct.csa hc⟧ : BrauerGroup K) = x := by
  revert hx
  induction x using Quotient.inductionOn with
  | _ A =>
    intro hA
    obtain ⟨B, emb, hB, hrank⟩ := exists_csa_finrank_sq_of_mem_relative (L := L) A hA
    obtain ⟨c, hc, ⟨e⟩⟩ := exists_algEquiv_crossedProduct_of_finrank_sq emb hrank
    refine ⟨c, hc, ?_⟩
    rw [← hB]
    exact Quotient.sound (IsBrauerEquivalent.of_algEquiv e)

end Relative

/-! ### Surjectivity onto the whole Brauer group -/

section Surjective

variable {k : Type u} [Field k] [PerfectField k]

/-- **The homomorphism from the smooth second cohomology of the absolute Galois group to the
Brauer group is surjective.**  A class is split by a finite Galois level, hence is the class of a
crossed product of that level, and the inflation of the cocycle to the algebraic closure is a
smooth cocycle with that Brauer class. -/
theorem smoothBrauerHom_surjective :
    Function.Surjective (smoothBrauerHom (k := k) (K := AlgebraicClosure k)) := by
  intro x
  obtain ⟨E, hfd, hg, hx⟩ := exists_isGalois_mem_relative x
  haveI := hfd
  haveI := hg
  obtain ⟨c, hc, hcx⟩ := exists_mk_csa_eq_of_mem_relative (L := ↥E) x hx
  exact ⟨_, (mk_csa_eq_smoothBrauer (K := AlgebraicClosure k) E hc rfl).symm.trans hcx⟩

variable (k) in
/-- **The Brauer group of a perfect field is the smooth second cohomology of its absolute Galois
group with coefficients in the units of an algebraic closure.** -/
noncomputable def smoothBrauerEquiv :
    SmoothH2 Gal(AlgebraicClosure k/k) (AlgebraicClosure k)ˣ ≃* BrauerGroup k :=
  MulEquiv.ofBijective smoothBrauerHom ⟨smoothBrauerHom_injective, smoothBrauerHom_surjective⟩

@[simp]
theorem smoothBrauerEquiv_apply (z : SmoothH2 Gal(AlgebraicClosure k/k) (AlgebraicClosure k)ˣ) :
    smoothBrauerEquiv k z = smoothBrauer z := rfl

end Surjective

end InverseGalois.CFT
