/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.PGroupTrivial

/-!
# A representation over the integers killed by a prime

A representation over the integers all of whose vectors are killed by a prime `p` is a
representation over the field with `p` elements in disguise, since the module structure over that
field is determined by the addition.  Its invariants are therefore retracted by a map which is
additive, hence linear over the integers, and the record of the retracted translates is available.

Both the shift and the coshift of such a representation are again killed by `p`, the first being a
quotient of the functions on the group and the second a subspace of them, so iterating them stays
inside the same world.  For a finite `p`-group this gives the same conclusion as in characteristic
`p`: the complete cohomology vanishes in every degree as soon as it vanishes in one.

## Main definitions

* `InverseGalois.CFT.Tate.intLinear`: an additive map between modules over the integers, read as a
  linear map.

## Main results

* `InverseGalois.CFT.Tate.nsmul_shiftIter_eq_zero`,
  `InverseGalois.CFT.Tate.nsmul_coshiftIter_eq_zero`: **the iterated shift and coshift of a
  representation killed by `p` are killed by `p`.**
* `InverseGalois.CFT.Tate.isZero_tateModule_of_isZero_single_int`: **a representation of a
  `p`-group over the integers killed by `p` with no complete cohomology in one degree has none in
  any degree.**

## Tags

Tate cohomology, cohomologically trivial, p-group, p-torsion
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {p : ℕ}

/-! ### Torsion in a shift and a coshift -/

section Torsion

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

omit [Finite G] in
/-- **The invariants of a representation killed by `p` are killed by `p`.** -/
theorem nsmul_invariants_eq_zero (A : Rep k G) (hp : ∀ v : ↥A.V, p • v = 0)
    (w : ↥(A.ρ.invariants)) : p • w = 0 := by
  refine Subtype.ext ?_
  have h := hp (w : ↥A.V)
  simpa using h

omit [Group G] [Finite G] in
/-- **The functions on the group with values in a module killed by `p` are killed by `p`.** -/
theorem nsmul_pi_eq_zero {M : Type u} [AddCommGroup M] (hp : ∀ v : M, p • v = 0)
    (f : G → M) : p • f = 0 :=
  funext fun x => hp (f x)

omit [Finite G] in
/-- **The shift of a representation killed by `p` is killed by `p`.** -/
theorem nsmul_shiftObj_eq_zero (A : Rep k G) (hp : ∀ v : ↥A.V, p • v = 0)
    (v : ↥(shiftObj A).V) : p • v = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb A.ρ)) v
  have h : (LinearMap.range (coindEmb A.ρ)).mkQ (p • f) = 0 := by
    rw [nsmul_pi_eq_zero hp f, map_zero]
  rwa [map_nsmul] at h

/-- **The coshift of a representation killed by `p` is killed by `p`.** -/
theorem nsmul_coshiftObj_eq_zero (A : Rep k G) (hp : ∀ v : ↥A.V, p • v = 0)
    (v : ↥(coshiftObj A).V) : p • v = 0 := by
  have h : ∀ w : ↥(LinearMap.ker (augMap A.ρ)), p • w = 0 := fun w =>
    Subtype.ext (by simpa using nsmul_pi_eq_zero hp (w : G → ↥A.V))
  exact h v

omit [Finite G] in
/-- **The iterated shift of a representation killed by `p` is killed by `p`.** -/
theorem nsmul_shiftIter_eq_zero (A : Rep k G) (hp : ∀ v : ↥A.V, p • v = 0) (j : ℕ) :
    ∀ v : ↥(shiftIter A j).V, p • v = 0 := by
  induction j with
  | zero => exact hp
  | succ j ih => exact nsmul_shiftObj_eq_zero _ ih

/-- **The iterated coshift of a representation killed by `p` is killed by `p`.** -/
theorem nsmul_coshiftIter_eq_zero (A : Rep k G) (hp : ∀ v : ↥A.V, p • v = 0) (j : ℕ) :
    ∀ v : ↥(coshiftIter A j).V, p • v = 0 := by
  induction j with
  | zero => exact hp
  | succ j ih => exact nsmul_coshiftObj_eq_zero _ ih

end Torsion

/-! ### The retraction over the integers -/

section Int

variable [Fact p.Prime] {G : Type} [Group G] [Finite G]

/-- **An additive map between modules over the integers is linear over the integers.** -/
def intLinear {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
    (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' c v := by simpa using map_intCast_smul f ℤ ℤ c v

/-! ### Cohomological triviality over the integers -/

/-- **A representation of a `p`-group over the integers killed by `p` with no first cohomology has
no complete cohomology in any degree.** -/
theorem isZero_tateModule_of_isZero_H1_int (hG : IsPGroup p G) (A : Rep ℤ G)
    (hp : ∀ v : ↥A.V, p • v = 0) (h1 : Limits.IsZero (groupCohomology A 1)) (n : ℤ) :
    Limits.IsZero (tateModule A n) := by
  letI : Module (ZMod p) ↥A.V := AddCommGroup.zmodModule (n := p) hp
  letI : Module (ZMod p) ↥(A.ρ.invariants) :=
    AddCommGroup.zmodModule (n := p) (nsmul_invariants_eq_zero A hp)
  exact isZero_tateModule_of_isZero_H1 hG A hp
    (@intLinear ↥A.V ↥(A.ρ.invariants) _ _ _ A.ρ.invariants.module
      (A.ρ.invariants.subtype.toAddMonoidHom.toZModLinearMap p).leftInverse.toAddMonoidHom)
    (fun v => LinearMap.leftInverse_apply_of_inj
      (f := A.ρ.invariants.subtype.toAddMonoidHom.toZModLinearMap p)
      (LinearMap.ker_eq_bot.2 fun _ _ h => Subtype.ext h) v) h1 n

/-- **A representation of a `p`-group over the integers killed by `p` with no complete cohomology
in one degree has none in any degree.** -/
theorem isZero_tateModule_of_isZero_single_int (hG : IsPGroup p G) (A : Rep ℤ G)
    (hp : ∀ v : ↥A.V, p • v = 0) {i : ℤ} (hi : Limits.IsZero (tateModule A i)) (n : ℤ) :
    Limits.IsZero (tateModule A n) := by
  rcases le_total i 1 with hle | hle
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = 1 - i := ⟨(1 - i).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hB1 : Limits.IsZero (tateModule (coshiftIter A j) 1) :=
      isZero_tateModule_congr (by omega) (isZero_tateModule_coshiftIter A j i hi)
    exact isZero_tateModule_of_isZero_coshiftIter A j n
      (isZero_tateModule_of_isZero_H1_int hG _ (nsmul_coshiftIter_eq_zero A hp j) hB1 (n + j))
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = i - 1 := ⟨(i - 1).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hB1 : Limits.IsZero (tateModule (shiftIter A j) 1) :=
      isZero_tateModule_shiftIter A j 1 (isZero_tateModule_congr (by omega) hi)
    exact isZero_tateModule_congr (by omega)
      (isZero_tateModule_of_isZero_shiftIter A j (n - j)
        (isZero_tateModule_of_isZero_H1_int hG _ (nsmul_shiftIter_eq_zero A hp j) hB1 (n - j)))

end Int

end

end InverseGalois.CFT.Tate
