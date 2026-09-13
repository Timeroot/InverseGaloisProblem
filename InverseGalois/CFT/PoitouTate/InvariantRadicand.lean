/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedUnits
import InverseGalois.CFT.PoitouTate.OrdInvariant

/-!
# An invariant radicand with prescribed orbit values

A prescription of radicands asks for an element of a group of units, tensored with a module of
coefficients, which is **invariant** under the Galois group and whose divisor is a prescribed
equivariant one.  Realising the divisor is free, because the vector of orders is onto; invariance
is not, and the obstruction is one class in the first cohomology of the Galois group with
coefficients in the kernel of the vector of orders, tensored with the module.

The obstruction is killed by **shrinking the module of coefficients**: a homomorphism of modules
which annihilates the first cohomology with coefficients in the kernel of the valuation carries the
realising tensor to an invariant one, and the prescribed value is read off after the homomorphism
has been applied.  The homomorphism is not asked to be injective, and nothing else about the
divisor is disturbed.

This file assembles the descent in that form, first for an arbitrary group carrying an equivariant
valuation, then for the units of a number field confined to a set of places.

## Main results

* `InverseGalois.CFT.exists_invariant_tensorVal_eq_orbitRadicand_of_kill`: **an invariant tensor
  realising the divisor carried by one orbit, once the module of coefficients has been shrunk.**
* `InverseGalois.CFT.exists_invariant_confinedTensorVal_eq_orbitRadicand`: **the same for the units
  of a number field which are local powers at one set of places and have order divisible by the
  exponent outside another.**

## Tags

number field, S-unit, tensor product, divisor, descent, group cohomology, Galois action
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField TensorProduct groupCohomology

/-! ### The descent with a shrinking module -/

section Shrink

variable {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C C' : Type} [CommGroup C] [CommGroup C'] [MulDistribMulAction Q C]
  [MulDistribMulAction Q C']
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ)) (B : Subgroup A) [IsStableSubgroup Q B]

/-- **An invariant tensor realising the divisor carried by one orbit, once the module of
coefficients has been shrunk.**  The valuation is onto, so the divisor is realised; it is
equivariant and the divisor carried by an orbit is equivariant, so the valuation of the realising
tensor is invariant.  What is left is one class with coefficients in the kernel of the valuation,
and the shrinking of the module annihilates it along with every other. -/
theorem exists_invariant_tensorVal_eq_orbitRadicand_of_kill
    (hg : Function.Surjective g) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (φ : C →* C') (hφ : ∀ (σ : Q) (w : C), φ (σ • w) = σ • φ w)
    (hkill : ∀ w : H1 (Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C)),
      (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := ↥B) Q φ hφ) 1).hom w = 0)
    (x₀ : X) (V : C) (hV : ∀ s ∈ stabilizer Q x₀, s • V = V) :
    ∃ s : Additive A ⊗[ℤ] Additive C',
      (∀ σ : Q, σ • s = s) ∧
      ∀ x : X, tensorVal C' g s x = Additive.ofMul (φ (orbitRadicand Q x₀ V x).toMul) := by
  have hgeq' : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) (σ • x) = g (Additive.ofMul a) x := by
    intro σ a x
    rw [hgeq σ a (σ • x), inv_smul_smul]
  obtain ⟨t, ht⟩ := tensorVal_surjective C g hg (orbitRadicand Q x₀ V)
  have hinv : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t :=
    tensorVal_smul_eq_of_eq C g hgeq' ht (orbitRadicand_smul_apply Q x₀ V hV)
  obtain ⟨s, hs, hsval⟩ := exists_invariant_tensorCoeff_of_map_tensorInvariantClass_eq_zero
    g B hg hB φ hφ hinv (hkill _)
  exact ⟨s, hs, fun x => by rw [hsval x, ht]⟩

end Shrink

/-! ### The confined units of a number field -/

section Confined

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
variable (n : ℕ) (Tz Y Xs : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite ↥Xs] [DecidableEq ↥Xs]
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y]
  [IsGaloisStablePlaces k K Xs]
variable {C C' : Type} [CommGroup C] [CommGroup C']
  [MulDistribMulAction Gal(K/k) C] [MulDistribMulAction Gal(K/k) C']

/-- **An invariant radicand of confined units realising the divisor carried by one orbit.**  The
units which are local powers at one set of places and have order divisible by the exponent outside
another form a subgroup carried into itself by the Galois group, and the vector of their orders at
the named places is an equivariant valuation onto the free abelian group on those places, so the
descent applies verbatim: the only input beyond surjectivity is the shrinking of the module of
coefficients. -/
theorem exists_invariant_confinedTensorVal_eq_orbitRadicand
    (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (φ : C →* C') (hφ : ∀ (σ : Gal(K/k)) (w : C), φ (σ • w) = σ • φ w)
    (hkill : ∀ w : H1 (Rep.ofDistribMulAction ℤ Gal(K/k)
        (Additive ↥(confinedSUnits n Tz Y Xs) ⊗[ℤ] Additive C)),
      (groupCohomology.map (MonoidHom.id Gal(K/k))
        (tensorCoeffRep (A := ↥(confinedSUnits n Tz Y Xs)) Gal(K/k) φ hφ) 1).hom w = 0)
    (w : ↥Xs) (V : C) (hV : ∀ s ∈ stabilizer Gal(K/k) w, s • V = V) :
    ∃ s : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C',
      (∀ σ : Gal(K/k), σ • s = s) ∧
      ∀ y : ↥Xs, tensorVal C' (confinedOrd n Tz Y Xs) s y
        = Additive.ofMul (φ (orbitRadicand Gal(K/k) w V y).toMul) :=
  exists_invariant_tensorVal_eq_orbitRadicand_of_kill (confinedOrd n Tz Y Xs)
    (confinedSUnits n Tz Y Xs) hsurj (mem_confinedSUnits_iff n Tz Y Xs)
    (confinedOrd_smul_apply n Tz Y Xs) φ hφ hkill w V hV

end Confined

end InverseGalois.CFT
