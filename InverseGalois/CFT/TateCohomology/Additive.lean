/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Functorial

/-!
# The complete cohomology is additive in the map

A sum of two maps of representations induces the sum of the two induced maps on the complete
cohomology.  In the two middle degrees this is read off from the description of the induced map on
the invariants and on the coinvariants; in the other degrees it comes from the additivity of the
complex of cochains and of the complex of chains, together with the additivity of the passage to
homology.

The consequence that matters is the effect of a multiple of the identity: multiplication by a
natural number on a representation induces multiplication by that number on the complete cohomology
in every degree.

## Main results

* `InverseGalois.CFT.Tate.tateMap_add`, `InverseGalois.CFT.Tate.tateMap_zero`: **the map induced on
  the complete cohomology is additive in the map of representations.**
* `InverseGalois.CFT.Tate.tateMap_nsmul_id_apply`: **a multiple of the identity induces that
  multiple on the complete cohomology.**

## Tags

Tate cohomology, additive functor, multiplication by an integer
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-! ### Additivity of the complex of chains -/

omit [Finite G] in
/-- **The complex of inhomogeneous chains is additive in the map of representations.** -/
theorem chainsMap_id_add {A B : Rep k G} (φ ψ : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) (φ + ψ)
      = groupHomology.chainsMap (MonoidHom.id G) φ
        + groupHomology.chainsMap (MonoidHom.id G) ψ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  rw [HomologicalComplex.add_f_apply]
  refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
  simp

/-! ### Additivity of the induced map -/

/-- **The map induced on the complete cohomology is additive in the map of representations.** -/
theorem tateMap_add {A B : Rep k G} (φ ψ : A ⟶ B) (n : ℤ) :
    tateMap (φ + ψ) n = tateMap φ n + tateMap ψ n := by
  match n with
  | .ofNat 0 =>
    ext x
    obtain ⟨y, rfl⟩ := H0mk_surjective A.ρ x
    rfl
  | .ofNat (m + 1) =>
    show HomologicalComplex.homologyMap
      (groupCohomology.cochainsMap (MonoidHom.id G) (φ + ψ)) (m + 1) = _
    rw [show groupCohomology.cochainsMap (MonoidHom.id G) (φ + ψ)
        = (groupCohomology.cochainsFunctor k G).map (φ + ψ) from rfl,
      Functor.map_add, HomologicalComplex.homologyMap_add]
    rfl
  | .negSucc 0 =>
    ext x
    refine Subtype.ext ?_
    obtain ⟨c, hc⟩ := x
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective A.ρ c
    rfl
  | .negSucc (m + 1) =>
    show HomologicalComplex.homologyMap
      (groupHomology.chainsMap (MonoidHom.id G) (φ + ψ)) (m + 1) = _
    rw [chainsMap_id_add, HomologicalComplex.homologyMap_add]
    rfl

/-- **The map induced on the complete cohomology by the zero map vanishes.** -/
theorem tateMap_zero (A B : Rep k G) (n : ℤ) : tateMap (0 : A ⟶ B) n = 0 := by
  have h := tateMap_add (0 : A ⟶ B) 0 n
  rw [add_zero] at h
  exact (add_left_cancel (a := tateMap (0 : A ⟶ B) n) (by rw [add_zero]; exact h)).symm

/-- **The map induced on the complete cohomology by a multiple is that multiple of the induced
map.** -/
theorem tateMap_nsmul {A B : Rep k G} (m : ℕ) (φ : A ⟶ B) (n : ℤ) :
    tateMap (m • φ) n = m • tateMap φ n := by
  induction m with
  | zero => simpa using tateMap_zero A B n
  | succ m ih => rw [succ_nsmul, tateMap_add, ih, succ_nsmul]

/-! ### Multiplication by a natural number -/

/-- **A multiple of the identity induces that multiple on the complete cohomology.** -/
theorem tateMap_nsmul_id (A : Rep k G) (m : ℕ) (n : ℤ) :
    tateMap (m • 𝟙 A) n = m • 𝟙 (tateModule A n) := by
  rw [tateMap_nsmul, tateMap_id]

/-- **A multiple of the identity multiplies a class of the complete cohomology.** -/
theorem tateMap_nsmul_id_apply (A : Rep k G) (m : ℕ) (n : ℤ) (x : tateModule A n) :
    (tateMap (m • 𝟙 A) n).hom x = m • x := by
  rw [tateMap_nsmul_id]
  simp

end

end InverseGalois.CFT.Tate
