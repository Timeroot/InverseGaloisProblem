/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TensorPTorsion
import InverseGalois.CFT.TateCohomology.TorsionInduced

/-!
# The theorem of Tate and Nakayama for coefficients killed by a prime

The theorem of Tate and Nakayama with coefficients killed by a prime carries one hypothesis that is
not a statement about the representation one starts from: the reduction modulo the prime of the
extension attached to the fundamental class must have no first cohomology on a Sylow subgroup for
that prime.  That hypothesis is here traded for one that is.

The extension attached to the fundamental class is cohomologically trivial, so its reduction
modulo the prime has, in every degree, the complete cohomology of the vectors it kills two degrees
higher.  The base ring has no torsion at the prime, so the vectors of the extension killed by the
prime are the vectors of the shift killed by the prime; and the vectors of the shift killed by the
prime have, in every degree, the complete cohomology of the vectors of the representation killed by
the prime one degree higher, because the functions on the group with values in those vectors are
the vectors killed by the prime in the functions on the group.

Altogether the hypothesis becomes **the vanishing, on each Sylow subgroup for the prime, of the
complete cohomology in degree four of the vectors of the representation killed by the prime.**
That is a statement about the coefficients themselves, and for the idele class group it is a
statement about the roots of unity in the completions.

## Main results

* `InverseGalois.CFT.Tate.cocycleNsmulTorsionIso`: the vectors killed by a number in the extension
  attached to a cocycle are the vectors killed by that number in the representation, when the
  number acts without torsion on the base ring.
* `InverseGalois.CFT.Tate.isZero_H1_resObj_modNsmul_cocycleObj`: **the reduction of the extension
  attached to the fundamental class has no first cohomology on a Sylow subgroup once the vectors
  killed by the prime have none in degree four.**
* `InverseGalois.CFT.Tate.tateNakayamaTorsionEquiv`: **the theorem of Tate and Nakayama for
  coefficients killed by a prime**, with the hypothesis carried by the vectors of the
  representation killed by that prime.

## Tags

Tate-Nakayama, Tate cohomology, torsion, dimension shifting, Sylow subgroup
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### The torsion of the extension attached to a cocycle -/

section Cocycle

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G)
  (b : groupCohomology.cocycles₁ A) (m : ℕ)

omit [Finite G] in
/-- The first component of a vector of the extension killed by a number is killed by it. -/
theorem nsmul_fst_eq_zero (z : ↥(nsmulTorsion (cocycleObj A b) m).V) : m • z.1.1 = 0 :=
  congrArg Prod.fst (LinearMap.mem_ker.mp z.2)

omit [Finite G] in
/-- The second component of a vector of the extension killed by a number is killed by it. -/
theorem nsmul_snd_eq_zero (z : ↥(nsmulTorsion (cocycleObj A b) m).V) : m • z.1.2 = 0 :=
  congrArg Prod.snd (LinearMap.mem_ker.mp z.2)

variable (hm : ∀ c : k, m • c = 0 → c = 0)

include hm

/-- The vectors killed by a number in the extension attached to a cocycle, as the vectors killed by
that number in the representation. -/
def cocycleNsmulTorsionLinear :
    ↥(nsmulTorsion A m).V ≃ₗ[k] ↥(nsmulTorsion (cocycleObj A b) m).V where
  toFun v := ⟨(v.1, 0), by
    refine LinearMap.mem_ker.mpr (Prod.ext ?_ ?_)
    · exact LinearMap.mem_ker.mp v.2
    · exact smul_zero m⟩
  map_add' _ _ := Subtype.ext (Prod.ext rfl (add_zero (0 : k)).symm)
  map_smul' _ _ := Subtype.ext (Prod.ext rfl (smul_zero _).symm)
  invFun z := ⟨z.1.1, LinearMap.mem_ker.mpr (nsmul_fst_eq_zero A b m z)⟩
  left_inv _ := rfl
  right_inv z := Subtype.ext (Prod.ext rfl (hm z.1.2 (nsmul_snd_eq_zero A b m z)).symm)

omit [Finite G] in
theorem cocycleNsmulTorsionLinear_equivariant (g : G) :
    (cocycleNsmulTorsionLinear A b m hm).toLinearMap ∘ₗ (nsmulTorsion A m).ρ g
      = (nsmulTorsion (cocycleObj A b) m).ρ g
          ∘ₗ (cocycleNsmulTorsionLinear A b m hm).toLinearMap :=
  LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun (cocycleInl_equivariant A b g) v.1)

/-- **The vectors killed by a number in the extension attached to a cocycle are the vectors killed
by that number in the representation**, when the number acts without torsion on the base ring. -/
def cocycleNsmulTorsionIso : nsmulTorsion A m ≅ nsmulTorsion (cocycleObj A b) m :=
  Action.mkIso (cocycleNsmulTorsionLinear A b m hm).toModuleIso fun g =>
    ModuleCat.hom_ext (cocycleNsmulTorsionLinear_equivariant A b m hm g)

end Cocycle

/-! ### The hypothesis of Tate and Nakayama at a prime -/

section PTorsion

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

/-- A prime acts on the integers without torsion. -/
theorem eq_zero_of_nsmul_eq_zero_int (c : ℤ) (h : p • c = 0) : c = 0 := by
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.1 h with h0 | h0
  · exact absurd (Nat.cast_eq_zero.1 h0) (Fact.out : p.Prime).pos.ne'
  · exact h0

variable (A : Rep ℤ G) (α : tateModule A 2)

/-- **The extension attached to the fundamental class has no complete cohomology on a Sylow
subgroup.** -/
theorem isZero_tateModule_resObj_cocycleObj_shiftObj
    (hT : ∀ q : ℕ, q.Prime → ∀ P : Sylow q G, IsTateClassTwo (P : Subgroup G) A α)
    (q : ℕ) (hq : q.Prime) (P : Sylow q G) (n : ℤ) :
    Limits.IsZero (tateModule (resObj (P : Subgroup G)
      (cocycleObj (shiftObj A) (tateTwoCocycle A α))) n) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hTc : IsTateClass (P : Subgroup G) (shiftObj A) (tateTwoCocycle A α) :=
    isTateClass_shiftObj (by
      rw [tateTwoCocycle_spec]
      exact hT q hq P)
  refine isZero_tateModule_of_isZero_two P.isPGroup' _ (i := 0) ?_ ?_ n
  · rw [resObj_cocycleObj]
    exact isZero_tateModule_cocycleObj_res_zero hTc
  · rw [resObj_cocycleObj]
    exact isZero_tateModule_cocycleObj_res_one hTc

/-- **The reduction modulo a prime of the extension attached to the fundamental class has no first
cohomology on a Sylow subgroup for that prime**, as soon as the vectors of the representation
killed by the prime have no complete cohomology there in degree four. -/
theorem isZero_H1_resObj_modNsmul_cocycleObj
    (hT : ∀ q : ℕ, q.Prime → ∀ P : Sylow q G, IsTateClassTwo (P : Subgroup G) A α)
    (hA : ∀ P : Sylow p G,
      Limits.IsZero (tateModule (resObj (P : Subgroup G) (nsmulTorsion A p)) 4))
    (P : Sylow p G) :
    Limits.IsZero (groupCohomology (resObj (P : Subgroup G)
      (modNsmul (cocycleObj (shiftObj A) (tateTwoCocycle A α)) p)) 1) := by
  have hp : p.Prime := Fact.out
  rw [resObj_modNsmul]
  refine isZero_groupCohomology_one_modNsmul
    (resObj (P : Subgroup G) (cocycleObj (shiftObj A) (tateTwoCocycle A α))) p
    (isZero_tateModule_resObj_cocycleObj_shiftObj A α hT p hp P) ?_
  refine isZero_tateModule_resObj_of_iso (P : Subgroup G)
    (cocycleNsmulTorsionIso (shiftObj A) (tateTwoCocycle A α) p
      (eq_zero_of_nsmul_eq_zero_int (p := p))).symm 3 ?_
  exact isZero_tateModule_resObj_nsmulTorsion_shiftObj A p (P : Subgroup G) 3 (hA P)

/-- **The theorem of Tate and Nakayama for coefficients killed by a prime**: the complete cohomology
of a representation killed by the prime in a degree is the complete cohomology of its tensor
product with a representation carrying the classical hypotheses two degrees higher, as soon as the
vectors of that representation killed by the prime have no complete cohomology in degree four on
each Sylow subgroup for the prime. -/
def tateNakayamaTorsionEquiv
    (hT : ∀ q : ℕ, q.Prime → ∀ P : Sylow q G, IsTateClassTwo (P : Subgroup G) A α)
    (hA : ∀ P : Sylow p G,
      Limits.IsZero (tateModule (resObj (P : Subgroup G) (nsmulTorsion A p)) 4))
    (M : Rep ℤ G) (hM : ∀ v : ↥M.V, p • v = 0) (n : ℤ) :
    tateModule M n ≃ₗ[ℤ] tateModule (tensorObj A M) (n + 1 + 1) :=
  tateNakayamaPTorsionEquiv A α M hM (isZero_H1_resObj_modNsmul_cocycleObj A α hT hA) n

end PTorsion

end

end InverseGalois.CFT.Tate
