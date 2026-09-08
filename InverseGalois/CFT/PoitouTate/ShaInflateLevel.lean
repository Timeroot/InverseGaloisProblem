/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ShaInflate
import InverseGalois.CFT.Units.KummerShaLevel

/-!
# The everywhere locally trivial classes come from a finite group, unconditionally on duality

The classes of the second cohomology of the absolute Galois group of a number field which die on
every decomposition subgroup are inflated from the Galois group of a finite extension splitting the
coefficients, provided the everywhere locally trivial classes of the first cohomology at that level
vanish.  The vanishing at the level was reduced, through Kummer theory and the comparison of Tate
and Nakayama, to three statements about complete cohomology of subgroups of that finite Galois
group.  Putting the two together removes the level entirely from the hypotheses.

What is left is a statement about a finite Galois extension of number fields carrying the roots of
unity, a kernel split by it into a product of those roots of unity, and three vanishing conditions
which mention only the finite group, its Sylow subgroups, the stabilisers of its places, and the
kernel.  In particular no duality theorem is used: the local-global principle at the second
cohomology is bought by the arithmetic of the extension and by cohomological vanishing that a
construction free to enlarge the extension can arrange.

## Main results

* `InverseGalois.CFT.sha2_le_range_galInflH2_of_isZero_local`: **the everywhere locally trivial
  classes of the second cohomology lie in the image of inflation from the Galois group of a finite
  Kummer extension**, as soon as three complete cohomology groups of subgroups of that group vanish.

## Tags

number field, Galois cohomology, local-global principle, inflation, Kummer theory, Sylow subgroup
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain Limits MulAction NumberField Tate

open scoped TensorProduct

noncomputable section

section Inflate

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

include hπ hπK hK htriv htrivEK α hfix eM hroot in
/-- **The everywhere locally trivial classes of the second cohomology of the absolute Galois group
of a number field lie in the image of inflation from the Galois group of a finite Kummer extension
splitting the coefficients**, as soon as three complete cohomology groups of subgroups of that
finite group vanish: over a Sylow subgroup for the prime, the stabiliser of every place of the
extension has none with coefficients the roots of unity of the completion tensored with the
homomorphisms of the roots of unity into the coefficients, in degree two; the whole Sylow subgroup
has none with coefficients the roots of unity of the extension tensored with those homomorphisms, in
degree three; and the Galois group of the extension has none with coefficients the homomorphisms
themselves, two degrees below zero.  Kummer theory reads the obstruction to inflation as a first
cohomology group over the finite group, the comparison of Tate and Nakayama produces every
everywhere locally trivial class there out of complete cohomology two degrees below zero, and the
three conditions say there is nothing to produce it from. -/
theorem sha2_le_range_galInflH2_of_isZero_local
    (h₁ : ∀ (P : Sylow p Gal(↥K/k)) (w : InfinitePlace ↥K), IsZero
      (tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(↥K/k) w)) (R := w.Completion)).comp
          (stabilizerSubgroupHom (P : Subgroup Gal(↥K/k)) w)) (p : ℤ))
        (resObj (stabilizer ↥(P : Subgroup Gal(↥K/k)) w)
          (resObj (P : Subgroup Gal(↥K/k)) (kummerHomRep M E (K := K))))) 2))
    (h₂ : ∀ (P : Sylow p Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)), IsZero
      (tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(↥K/k) v)) (R := v.adicCompletion ↥K)).comp
          (stabilizerSubgroupHom (P : Subgroup Gal(↥K/k)) v)) (p : ℤ))
        (resObj (stabilizer ↥(P : Subgroup Gal(↥K/k)) v)
          (resObj (P : Subgroup Gal(↥K/k)) (kummerHomRep M E (K := K))))) 2))
    (hU : ∀ P : Sylow p Gal(↥K/k), IsZero (tateModule (resObj (P : Subgroup Gal(↥K/k))
      (tensorObj (torsionRep (globalUnitsAut (k := k) (K := ↥K)) (p : ℤ))
        (kummerHomRep M E (K := K)))) 3))
    (hzero : ∀ y : ↥(tateModule (kummerHomRep M E (K := K)) (-2)), y = 0) :
    sha2 E (decompositionSubgroups k Ω) ≤ (galInflH2 K hπ).range := by
  have hMp : ∀ m : M, m ^ p = 1 := fun m =>
    hK.injective (by rw [_root_.map_pow, hK.pow_eq_one, _root_.map_one])
  have hEp : ∀ e : E, e ^ p = 1 := fun e =>
    α.injective (by
      rw [_root_.map_pow, _root_.map_one]
      exact funext fun j => hMp _)
  have hsha1 := sha1Level_eq_bot_of_isZero_local hK htriv htrivEK α hEp hfix eM hroot
    K.fixingSubgroup_isOpen h₁ h₂ hU hzero
  exact sha2_le_range_galInflH2 K E hπ hπK hK.isPrimitiveRoot_primitiveRoot hK.smul_eq α
    hK.injective hK.pow_eq_one hK.exists_ι_eq hsha1

end Inflate

end

end InverseGalois.CFT
