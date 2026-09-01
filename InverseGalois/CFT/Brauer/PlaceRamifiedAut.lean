/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceRamified

/-!
# The local generator at a totally ramified place is a global automorphism

The invariant of a cyclic algebra at a totally ramified place is computed from a generator of the
Galois group of the completions restricting to the chosen generator of the Galois group of the
extension.  Such a generator is unique: an automorphism of the completion is determined by its
restriction to the extension, so it is the automorphism induced by that restriction.  The radical
presenting the completion is produced together with the action of an induced automorphism, and this
identification is what lets that action be read as the action of the local generator.

The order of the Galois group of the completions is the degree of the extension at a totally
ramified place, so the exponent of the power residue symbol is prescribed by the extension itself
and no local counting is needed either.

## Main results

* `InverseGalois.CFT.adicCompletionAut_apply_eq_of_restrictScalars_eq`: **an automorphism of the
  completion is the one induced by its restriction to the extension.**
* `InverseGalois.CFT.natCard_aut_adicCompletion_of_inertia_eq_top`: the Galois group of the
  completions at a totally ramified place has the order of the Galois group of the extension.
* `InverseGalois.CFT.placeInvariant_cyclicBrauerHom_of_radical_aut`: **the invariant at a totally
  ramified place of a cyclic algebra whose completion is presented by a radical moved by the
  automorphism induced by the chosen generator.**

## Tags

Brauer group, cyclic algebra, local invariant, totally ramified, decomposition group, radical
extension, power residue symbol, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### Equal automorphisms induce equal automorphisms of the completion -/

section Congr

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]
  (v : HeightOneSpectrum (𝓞 K))

/-- Equal automorphisms fixing a place induce the same automorphism of the completion. -/
theorem adicCompletionAut_congr {σ τ : Gal(K/k)} (hσ : σ • v = v) (hτ : τ • v = v) (h : σ = τ)
    (z : v.adicCompletion K) :
    adicCompletionAut v σ hσ z = adicCompletionAut v τ hτ z := by
  subst h
  rfl

end Congr

/-! ### The local generator at a totally ramified place -/

section LocalGenerator

attribute [local instance] isGalois_adicCompletion

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K)) {p e n : ℕ} [NeZero n]

variable (k) in
/-- **An automorphism of the completion is the one induced by its restriction to the extension.**
Restriction to the extension is the identification of the Galois group of the completions with the
Galois group over the decomposition field, and every automorphism of the completion is induced by
its restriction. -/
theorem adicCompletionAut_apply_eq_of_restrictScalars_eq {σ₀ : Gal(K/k)} (hσ₀ : σ₀ • w = w)
    {τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K}
    (hres : (localDecompositionEquiv k w τ).restrictScalars k = σ₀) (z : w.adicCompletion K) :
    adicCompletionAut w σ₀ hσ₀ z = τ z := by
  have hrb : restrictToBase k w τ = σ₀ := by
    rw [restrictToBase_eq_restrictScalars_localDecompositionEquiv k w τ, hres]
  exact (adicCompletionAut_congr w hσ₀ (restrictToBase_mem_stabilizer k w τ) hrb.symm z).trans
    (adicCompletionAut_restrictToBase k w τ z)

variable (k) in
/-- **The Galois group of the completions at a totally ramified place has the order of the Galois
group of the extension**, because the local degree there is the degree of the extension. -/
theorem natCard_aut_adicCompletion_of_inertia_eq_top
    (h : Ideal.inertia Gal(K/k) w.asIdeal = ⊤) :
    Nat.card (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K)
      = Nat.card Gal(K/k) := by
  rw [IsGalois.card_aut_eq_finrank]
  exact finrank_adicCompletion_eq_of_inertia_eq_top k w h

variable (k) in
/-- **The invariant at a totally ramified place of a cyclic algebra whose completion is presented
by a radical moved by the automorphism induced by the chosen generator.**  That automorphism is the
generator of the Galois group of the completions restricting to the chosen one, and at a totally
ramified place the order of that group is the degree of the extension. -/
theorem placeInvariant_cyclicBrauerHom_of_radical_aut
    (hres : HasResidueChar ((primeUnder (𝓞 k) w).adicCompletion k) p e)
    (hinertia : Ideal.inertia Gal(K/k) w.asIdeal = ⊤)
    {ζ : (primeUnder (𝓞 k) w).adicCompletion k} (hζ : IsPrimitiveRoot ζ n)
    (hn : IsRadicalExponent n)
    (hpn : ¬ p ∣ n) {σ₀ : Gal(K/k)} (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀)
    (hst : σ₀ • w = w) (hcard : Nat.card Gal(K/k) = n)
    {b : ((primeUnder (𝓞 k) w).adicCompletion k)ˣ} {ν : w.adicCompletion K}
    (hpow : ν ^ n
      = algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) (b : _))
    (hact : adicCompletionAut w σ₀ hst ν
      = algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) ζ * ν)
    (hb : unitValDiv (isUnitValGen_one (valued_adicCompletion_surjective (primeUnder (𝓞 k) w)))
      (Additive.ofMul b) = -1)
    {u : (primeUnder (𝓞 k) w).adicCompletion k} (hu : Valued.v u = 1)
    (hu1 : Valued.v (ζ - u ^ ((Nat.card (DivisionResidue ((primeUnder (𝓞 k) w).adicCompletion k)
      ((primeUnder (𝓞 k) w).adicCompletion k)) - 1) / n)) < 1)
    {a : kˣ} {j : ℕ}
    (hj : Valued.v (algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k) (a : k) - u ^ j) < 1) :
    placeInvariant k (primeUnder (𝓞 k) w) (cyclicBrauerHom hσ₀ a)
      = Multiplicative.ofAdd (zmodQModZ n (j : ZMod n)) := by
  obtain ⟨σ, hσ, hrestr⟩ := exists_restrictScalars_eq_of_inertia_eq_top k w hinertia hσ₀
  refine placeInvariant_cyclicBrauerHom_of_radical_eq_powerResidue k w hres hinertia hζ hn hpn hσ₀
    hσ hrestr ?_ hpow ?_ hb hu hu1 hj
  · rw [natCard_aut_adicCompletion_of_inertia_eq_top k w hinertia, hcard]
  · rw [← adicCompletionAut_apply_eq_of_restrictScalars_eq k w hst hrestr ν]
    exact hact

end LocalGenerator

end InverseGalois.CFT
