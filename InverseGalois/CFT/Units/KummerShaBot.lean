/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.KummerIdele
import InverseGalois.CFT.Units.NakayamaSpan

/-!
# The everywhere locally trivial classes of a level all vanish

An everywhere locally trivial class of the transgression of a lifting problem is, read over the
Galois group of the level, a class of the first cohomology of the units of the level tensored with
the homomorphisms of the roots of unity into the kernel; and being locally trivial it dies in the
ideles.  The comparison of Tate and Nakayama then produces it out of the complete cohomology of the
coefficients three degrees lower, provided the comparison spans together with the classes coming
from the ideles.  So if the coefficients have no complete cohomology in degree minus two, there is
nothing for the class to come from and the class is trivial.

That is the whole local-global content of the second cohomological obstruction: **the everywhere
locally trivial classes of a level vanish**, once the coefficients have been arranged to have no
complete cohomology two degrees below zero.  The arrangement is a statement about the group alone,
and the span is a statement about the extension alone; neither mentions the lifting problem.

## Main results

* `InverseGalois.CFT.kummerFiniteH1Equiv_eq_one_of_span`: **the reading of an everywhere locally
  trivial class over the Galois group of the level is trivial**, when the comparison spans and the
  coefficients have no complete cohomology in degree minus two.
* `InverseGalois.CFT.sha1Level_eq_bot_of_span`: **the everywhere locally trivial classes of a level
  are all trivial** under the same two conditions.

## Tags

number field, idele, Kummer theory, Tate-Nakayama, locally trivial, embedding problem
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

open scoped Pointwise TensorProduct

noncomputable section

/-! ### The vanishing -/

section Vanish

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω} [NumberField ↥K] [K.fixingSubgroup.Normal] [Normal k ↥K]
variable [IsGalois k ↥K]
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/k) M] {ιK : M →* (↥K)ˣ}
variable {p d dW : ℕ} [Fact p.Prime] [NeZero p] [IsCyclic M]
variable {E : Type} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
variable (hK : IsKummerData ↥K Ω M ιK p)
variable (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivEK : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable {J : Type} [Fintype J] [DecidableEq J] (α : E ≃* (J → M)) (hEp : ∀ e : E, e ^ p = 1)
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m))
variable [ActsTrivially K.fixingSubgroup (M →* E)] [Finite Gal(↥K/k)]
variable (W : Rep ℤ Gal(↥K/k))
  (φ : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E) ≃+ ↥(tensorObj (globalUnitsRep k ↥K) W).V)
  (hφ : ∀ (g : Gal(Ω/k) ⧸ K.fixingSubgroup) (t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)),
    φ (g • t)
      = (tensorObj (globalUnitsRep k ↥K) W).ρ (quotientFixingSubgroupEquiv K g) (φ t))
variable {ρ : Additive (M →* E) →ₗ[ℤ] ↥W.V}
  (hφmap : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
    φ t = TensorProduct.map LinearMap.id ρ t)
variable (eM : Additive (M →* E) ≃+ (Fin d → ZMod p))
variable (hroot : ∀ x : Ωˣ, ∃ y : Ωˣ, y ^ p = x)
variable (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k)))

include hφmap eM hroot in
/-- **The reading of an everywhere locally trivial class over the Galois group of the level is
trivial**, as soon as the comparison of Tate and Nakayama over a Sylow subgroup spans together with
the classes coming from the ideles and the coefficients have no complete cohomology in degree minus
two.  The class dies in the ideles, so the comparison produces it; but there is nothing for it to be
produced from. -/
theorem kummerFiniteH1Equiv_eq_one_of_span
    (eW : ↥W.V ≃+ (Fin dW → ZMod p)) (hWp : ∀ w : ↥W.V, p • w = 0)
    (hspan : HasIdeleClassNakayamaSpan k ↥K p)
    (hzero : ∀ y : ↥(tateModule W (-2)), y = 0)
    {z : SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E)}
    (hz : z ∈ sha1Level E K.fixingSubgroup hop (decompositionSubgroups k Ω)) :
    kummerFiniteH1Equiv hK htriv htrivEK α hEp hfix
      (tensorObj (globalUnitsRep k ↥K) W) φ hφ hop z = 1 := by
  obtain ⟨y, hy⟩ := exists_shaTorusPTorsionMap_one_of_span hspan W hWp _
    (tateMap_globalUnitsToIdele_kummerFiniteH1Equiv_eq_zero hK htriv htrivEK α hEp hfix W φ hφ
      hφmap eM hroot hop eW hz)
  rw [hzero y, _root_.map_zero] at hy
  exact hy.symm

include hK htriv htrivEK α hEp hfix φ hφ hφmap eM hroot in
/-- **The everywhere locally trivial classes of a level are all trivial**, as soon as the comparison
of Tate and Nakayama over a Sylow subgroup spans together with the classes coming from the ideles
and the coefficients have no complete cohomology in degree minus two.  The reading over the Galois
group of the level is injective, so it is enough that every class read there is trivial. -/
theorem sha1Level_eq_bot_of_span
    (eW : ↥W.V ≃+ (Fin dW → ZMod p)) (hWp : ∀ w : ↥W.V, p • w = 0)
    (hspan : HasIdeleClassNakayamaSpan k ↥K p)
    (hzero : ∀ y : ↥(tateModule W (-2)), y = 0) :
    sha1Level E K.fixingSubgroup hop (decompositionSubgroups k Ω) = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  refine Subgroup.mem_bot.2 ((MulEquiv.map_eq_one_iff (kummerFiniteH1Equiv hK htriv htrivEK α hEp
    hfix (tensorObj (globalUnitsRep k ↥K) W) φ hφ hop)).1 ?_)
  exact kummerFiniteH1Equiv_eq_one_of_span hK htriv htrivEK α hEp hfix W φ hφ hφmap eM hroot hop
    eW hWp hspan hzero hz

end Vanish

end

end InverseGalois.CFT
