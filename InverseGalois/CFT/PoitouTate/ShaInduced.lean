/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ShaInflateLevel
import InverseGalois.CFT.Profinite.CoindVanish

/-!
# A kernel which is the functions on a finite Galois group has no locally trivial classes

The classes of the second cohomology of the absolute Galois group of a number field which die on
every decomposition subgroup are inflated from the Galois group of a finite Kummer extension, once
three complete cohomology groups of subgroups of that finite group vanish.  All three vanish at
once when the coefficients are the functions on the finite group, and in that case there is nothing
left at the finite level either: a module which is the functions on the group has no second
cohomology at all.  So the two halves fit together and the everywhere locally trivial classes are
not merely inflated from somewhere, they are trivial.

The hypothesis is a single map out of the kernel whose translates separate and exhaust: the record
of the values of that map at all the translates of an element is asked to be a bijection onto the
functions on the finite Galois group.  From it the homomorphisms of the roots of unity into the
kernel inherit the same shape, because the homomorphisms into the functions on a group are the
functions on the group with values in the homomorphisms, and those homomorphisms are exactly the
representation the vanishing criterion is stated about.

## Main definitions

* `InverseGalois.CFT.kummerHomEval`: the reading of the homomorphisms of the roots of unity into
  the kernel given by a map of the kernel.

## Main results

* `InverseGalois.CFT.kummerHomAutLevel_toMul_apply`: the Galois group of the level acts on the
  homomorphisms of the roots of unity through the values.
* `InverseGalois.CFT.bijective_repEval_kummerHomEval`: **the homomorphisms of the roots of unity
  into a kernel which is the functions on the level are the functions on the level.**
* `InverseGalois.CFT.sha2_eq_bot_of_bijective_translateEval`: **a kernel which is the functions on
  the Galois group of a finite Kummer extension has no everywhere locally trivial class in the
  second cohomology.**

## Tags

number field, Galois cohomology, local-global principle, induced module, Kummer theory
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory MulAction NumberField Tate

noncomputable section

/-! ### The homomorphisms of the roots of unity, read as functions on the level -/

section Level

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable (K : IntermediateField k Ω) [IsGalois k ↥K]
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M]
variable {E : Type} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
  [MulDistribMulAction (↥K ≃ₐ[k] ↥K) E]
variable (hπ : ∀ (g : Gal(Ω/k)) (e : E), g • e = AlgEquiv.restrictNormalHom ↥K g • e)
variable (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable [ActsTrivially K.fixingSubgroup (M →* E)]

include hπ htriv in
/-- **The Galois group of the level acts on the homomorphisms of the roots of unity into the kernel
through the values**, because the roots of unity are fixed. -/
theorem kummerHomAutLevel_toMul_apply (σ : Gal(↥K/k)) (w : Additive (M →* E)) (m : M) :
    (kummerHomAutLevel M E (K := K) σ w).toMul m = σ • w.toMul m := by
  obtain ⟨τ, rfl⟩ := restrictNormalHom_surjective_level K σ
  rw [kummerHomAutLevel_restrictNormalHom, kummerHomAut_apply]
  show homSMul τ w.toMul m = _
  rw [homSMul_apply, htriv, ← hπ]

variable {X : Type} [CommGroup X]

variable (M) in
/-- **The reading of the homomorphisms of the roots of unity into the kernel** given by a map of
the kernel: compose with that map. -/
def kummerHomEval (π : E →* X) :
    ↥(kummerHomRep M E (K := K)).V →ₗ[ℤ] Additive (M →* X) :=
  (MonoidHom.toAdditive (homCompHom π)).toIntLinearMap

include hπ htriv in
/-- The reading of the homomorphisms of the roots of unity as functions on the level is the reading
of the kernel itself, taken at each value. -/
theorem repEval_kummerHomEval_apply (π : E →* X) (w : Additive (M →* E)) (σ : Gal(↥K/k))
    (m : M) : (repEval (kummerHomEval K M π) w σ).toMul m = translateEval π (w.toMul m) σ := by
  show π ((kummerHomAutLevel M E (K := K) σ w).toMul m) = translateEval π (w.toMul m) σ
  rw [kummerHomAutLevel_toMul_apply K hπ htriv, translateEval_apply]

include hπ htriv in
/-- **The homomorphisms of the roots of unity into a kernel which is the functions on the Galois
group of the level are again the functions on that group.**  The values of a homomorphism are read
one at a time, and the reading of the kernel turns each of them into a function on the group; the
inverse reassembles a homomorphism out of a family of homomorphisms into the values. -/
theorem bijective_repEval_kummerHomEval (π : E →* X)
    (hbij : Function.Bijective (translateEval (G := Gal(↥K/k)) π)) :
    Function.Bijective (repEval (kummerHomEval K M π)) := by
  constructor
  · intro w w' h
    refine Additive.toMul.injective (MonoidHom.ext fun m => hbij.1 (funext fun σ => ?_))
    have e1 := repEval_kummerHomEval_apply K hπ htriv π w σ m
    have e2 := repEval_kummerHomEval_apply K hπ htriv π w' σ m
    exact e1.symm.trans
      ((congrArg (fun u : Gal(↥K/k) → Additive (M →* X) => (u σ).toMul m) h).trans e2)
  · intro F
    obtain ⟨v, hv⟩ := (bijective_homTranslate (M := M) (translateEvalEquiv π hbij)).2
      fun σ => (F σ).toMul
    refine ⟨Additive.ofMul v, funext fun σ => Additive.toMul.injective (MonoidHom.ext fun m => ?_)⟩
    exact (repEval_kummerHomEval_apply K hπ htriv π (Additive.ofMul v) σ m).trans
      (congrArg (fun f : M →* X => f m) (congrFun hv σ))

end Level

/-! ### The everywhere locally trivial classes vanish -/

section Induced

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [Algebra.IsIntegral k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
  [IsAlgClosure ↥K Ω]
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/k) M] [IsCyclic M] {ιK : M →* (↥K)ˣ}
variable {p d : ℕ} [Fact p.Prime] [NeZero p]
variable {E : Type} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
  [MulDistribMulAction Gal(Ω/↥K) E] [MulDistribMulAction (↥K ≃ₐ[k] ↥K) E]
variable (hπ : ∀ (g : Gal(Ω/k)) (e : E), g • e = AlgEquiv.restrictNormalHom ↥K g • e)
  (hπK : ∀ (g : Gal(Ω/↥K)) (e : E), g • e = galRestrictScalarsHom k ↥K Ω g • e)
variable (hK : IsKummerData ↥K Ω M ιK p)
variable (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivEK : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable {J : Type} [Fintype J] [DecidableEq J] (α : E ≃* (J → M))
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m))
variable [ActsTrivially K.fixingSubgroup (M →* E)]
variable (eM : Additive (M →* E) ≃+ (Fin d → ZMod p))
variable (hroot : ∀ x : Ωˣ, ∃ y : Ωˣ, y ^ p = x)
variable {X : Type} [CommGroup X]

include hπ hπK hK htriv htrivEK α hfix eM hroot in
/-- **A kernel which is the functions on the Galois group of a finite Kummer extension has no
everywhere locally trivial class in the second cohomology of the absolute Galois group.**  Being
the functions on that group makes the homomorphisms of the roots of unity into the kernel the
functions on the same group, which kills the three complete cohomology groups that bound the
locally trivial classes by the image of inflation from the level; and it kills the second
cohomology at the level itself, so the image of inflation is trivial. -/
theorem sha2_eq_bot_of_bijective_translateEval (π : E →* X)
    (hbij : Function.Bijective (translateEval (G := Gal(↥K/k)) π)) :
    sha2 E (decompositionSubgroups k Ω) = ⊥ := by
  have hiso : kummerHomRep M E (K := K) ≅ Rep.of (inducedRep ℤ Gal(↥K/k) (Additive (M →* X))) :=
    inducedRepIsoOfBijective (kummerHomEval K M π)
      (bijective_repEval_kummerHomEval K hπ htriv π hbij)
  have hle := sha2_le_range_galInflH2_of_isoInducedRep K hπ hπK hK htriv htrivEK α hfix eM hroot
    hiso
  have hsub : Subsingleton (SmoothH2 Gal(↥K/k) E) :=
    subsingleton_smoothH2_of_bijective_translateEval π hbij
  refine le_antisymm (le_trans hle ?_) bot_le
  rintro x ⟨z, rfl⟩
  rw [Subsingleton.elim z 1, _root_.map_one]
  exact Subgroup.mem_bot.2 rfl

end Induced

end

end InverseGalois.CFT
