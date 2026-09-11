/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ShaInduced
import InverseGalois.CFT.Profinite.SylowVanish
import InverseGalois.CFT.TateCohomology.SylowInduced

/-!
# A kernel which is the functions on a Sylow subgroup has no locally trivial classes

The classes of the second cohomology of the absolute Galois group of a number field which die on
every decomposition subgroup vanish once the kernel of the lifting problem is, as a module, the
functions on the Galois group of a finite Kummer extension.  That hypothesis asks a great deal of
the extension.  It can be weakened all the way down to a Sylow subgroup for the prime: only the
part of the cohomology killed by a power of the prime can be there in the first place, and that part
is seen faithfully on a Sylow subgroup, both in the complete cohomology of the finite group and in
the second cohomology of the Galois group of the level.

So the condition to be arranged is that the kernel be the functions on a Sylow subgroup of the
Galois group of the level, with values anywhere.  It is asked at every Sylow subgroup, which costs
nothing, since they are all conjugate and the values may be taken in one and the same group.

## Main results

* `InverseGalois.CFT.bijective_repEval_kummerHomEval_resObj`: the homomorphisms of the roots of
  unity into a kernel which is the functions on a subgroup are the functions on that subgroup.
* `InverseGalois.CFT.sha2_eq_bot_of_bijective_translateEval_sylow`: **a kernel which is the
  functions on a Sylow subgroup of the Galois group of a finite Kummer extension has no everywhere
  locally trivial class in the second cohomology.**

## Tags

number field, Galois cohomology, local-global principle, Sylow subgroup, induced module, Kummer
theory
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory Limits MulAction NumberField Tate

noncomputable section

/-! ### The homomorphisms of the roots of unity, read on a subgroup of the level -/

section Level

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable (K : IntermediateField k Ω) [IsGalois k ↥K]
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M]
variable {E : Type} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
  [MulDistribMulAction (↥K ≃ₐ[k] ↥K) E]
variable (hπ : ∀ (g : Gal(Ω/k)) (e : E), g • e = AlgEquiv.restrictNormalHom ↥K g • e)
variable (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable [ActsTrivially K.fixingSubgroup (M →* E)]
variable {X : Type} [CommGroup X]

include hπ htriv in
/-- The reading of the homomorphisms of the roots of unity as functions on a subgroup of the level
is the reading of the kernel itself, taken at each value. -/
theorem repEval_kummerHomEval_resObj_apply (H : Subgroup Gal(↥K/k)) (π : E →* X)
    (w : Additive (M →* E)) (x : ↥H) (m : M) :
    (repEval (A := resObj H (kummerHomRep M E (K := K))) (kummerHomEval K M π) w x).toMul m
      = translateEval (G := ↥H) π (w.toMul m) x := by
  show π ((kummerHomAutLevel M E (K := K) (x : Gal(↥K/k)) w).toMul m) = _
  rw [kummerHomAutLevel_toMul_apply K hπ htriv, translateEval_apply]
  rfl

include hπ htriv in
/-- **The homomorphisms of the roots of unity into a kernel which is the functions on a subgroup of
the Galois group of the level are again the functions on that subgroup.**  The values of a
homomorphism are read one at a time, and the reading of the kernel turns each of them into a
function on the subgroup; the inverse reassembles a homomorphism out of a family of homomorphisms
into the values. -/
theorem bijective_repEval_kummerHomEval_resObj (H : Subgroup Gal(↥K/k)) (π : E →* X)
    (hbij : Function.Bijective (translateEval (G := ↥H) π)) :
    Function.Bijective
      (repEval (A := resObj H (kummerHomRep M E (K := K))) (kummerHomEval K M π)) := by
  constructor
  · intro w w' h
    refine Additive.toMul.injective (MonoidHom.ext fun m => hbij.1 (funext fun x => ?_))
    have e1 := repEval_kummerHomEval_resObj_apply K hπ htriv H π w x m
    have e2 := repEval_kummerHomEval_resObj_apply K hπ htriv H π w' x m
    exact e1.symm.trans
      ((congrArg (fun u : ↥H → Additive (M →* X) => (u x).toMul m) h).trans e2)
  · intro F
    obtain ⟨v, hv⟩ := (bijective_homTranslate (M := M) (translateEvalEquiv π hbij)).2
      fun x => (F x).toMul
    refine ⟨Additive.ofMul v, funext fun x => Additive.toMul.injective (MonoidHom.ext fun m => ?_)⟩
    exact (repEval_kummerHomEval_resObj_apply K hπ htriv H π (Additive.ofMul v) x m).trans
      (congrArg (fun f : M →* X => f m) (congrFun hv x))

end Level

/-! ### The everywhere locally trivial classes vanish -/

section Sylow

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
/-- **A kernel which is the functions on a Sylow subgroup of the Galois group of a finite Kummer
extension has no everywhere locally trivial class in the second cohomology of the absolute Galois
group.**  Being the functions on the Sylow subgroup makes the homomorphisms of the roots of unity
into the kernel the functions on that same subgroup, which kills the two complete cohomology groups
of subgroups of it that bound the locally trivial classes by the image of inflation from the level;
the third, two degrees below zero over the whole group, dies because the coefficients are killed by
the prime and restriction to a Sylow subgroup is injective there; and the second cohomology at the
level itself dies for the same reason, so the image of inflation is trivial. -/
theorem sha2_eq_bot_of_bijective_translateEval_sylow (π : E →* X)
    (hbij : ∀ P : Sylow p Gal(↥K/k),
      Function.Bijective (translateEval (G := ↥(P : Subgroup Gal(↥K/k))) π)) :
    sha2 E (decompositionSubgroups k Ω) = ⊥ := by
  have hMp : ∀ m : M, m ^ p = 1 := fun m =>
    hK.injective (by rw [_root_.map_pow, hK.pow_eq_one, _root_.map_one])
  have hEp : ∀ e : E, e ^ p = 1 := fun e =>
    α.injective (by
      rw [_root_.map_pow, _root_.map_one]
      exact funext fun j => hMp _)
  have hiso : ∀ P : Sylow p Gal(↥K/k),
      resObj (P : Subgroup Gal(↥K/k)) (kummerHomRep M E (K := K))
        ≅ Rep.of (inducedRep ℤ ↥(P : Subgroup Gal(↥K/k)) (Additive (M →* X))) := fun P =>
    inducedRepIsoOfBijective (kummerHomEval K M π)
      (bijective_repEval_kummerHomEval_resObj K hπ htriv (P : Subgroup Gal(↥K/k)) π (hbij P))
  have hW : ∀ w : ↥(kummerHomRep M E (K := K)).V, p ^ 1 • w = 0 := by
    intro w
    rw [pow_one]
    exact nsmul_additive_hom_eq_zero hEp _
  obtain ⟨P₀⟩ : Nonempty (Sylow p Gal(↥K/k)) := Sylow.nonempty
  have hle := sha2_le_range_galInflH2_of_isZero_local K hπ hπK hK htriv htrivEK α hfix eM hroot
    (fun P w => isZero_tateModule_tensorObj_right_of_isoInducedRep
      (resIsoInducedRep (hiso P) (stabilizer ↥(P : Subgroup Gal(↥K/k)) w)) _ 2)
    (fun P v => isZero_tateModule_tensorObj_right_of_isoInducedRep
      (resIsoInducedRep (hiso P) (stabilizer ↥(P : Subgroup Gal(↥K/k)) v)) _ 2)
    (fun P => by
      rw [resObj_tensorObj]
      exact isZero_tateModule_tensorObj_right_of_isoInducedRep (hiso P) _ 3)
    (fun y => eq_zero_tateModule_of_isoInducedRep_sylow P₀ (hiso P₀) hW (-2) y)
  have hsubP : Subsingleton (SmoothH2 ↥(P₀ : Subgroup Gal(↥K/k)) E) :=
    subsingleton_smoothH2_of_bijective_translateEval π (hbij P₀)
  have hsub : Subsingleton (SmoothH2 Gal(↥K/k) E) :=
    subsingleton_smoothH2_of_sylow P₀ (j := 1) (fun e => by rw [pow_one]; exact hEp e) hsubP
  refine le_antisymm (le_trans hle ?_) bot_le
  rintro x ⟨z, rfl⟩
  rw [Subsingleton.elim z 1, _root_.map_one]
  exact Subgroup.mem_bot.2 rfl

end Sylow

end

end InverseGalois.CFT
