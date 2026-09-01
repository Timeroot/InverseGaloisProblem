/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceRadical
import InverseGalois.CFT.Brauer.TameOdd

/-!
# The invariant at a totally ramified place is a power residue symbol

At a totally ramified place the invariant of a cyclic algebra whose completed splitting field is
presented by a radical is the inverse of the norm residue symbol of the coefficient against the
power of the radical.  When the coefficient is a unit of the valuation ring and the power of the
radical has valuation that of a uniformiser, the tame computation of the symbol applies and nothing
but the power residue exponent of the coefficient is left.

The power of the radical is the opposite of the rational prime below the place in the intended
application, so its divided valuation is minus one rather than one; the symbol is skew symmetric,
so the two normalisations differ only by the sign of the exponent, and the two sign changes — the
one of the normalisation, the one of the inverse — cancel.

## Main results

* `InverseGalois.CFT.placeInvariant_cyclicBrauerHom_of_radical_eq_powerResidue`: **the invariant at
  a totally ramified place of a cyclic algebra whose completed splitting field is presented by a
  radical, of a coefficient which is a unit of the valuation ring, is the class modulo the integers
  of the power residue exponent of the coefficient divided by the exponent.**

## Tags

Brauer group, cyclic algebra, local invariant, power residue symbol, tame symbol, radical
extension, totally ramified, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped Pointwise

/-! ### The invariant at a totally ramified place -/

section PlaceRamified

attribute [local instance] isGalois_adicCompletion

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K)) {p e n : ℕ} [NeZero n]

variable (k) in
/-- **The invariant at a totally ramified place of a cyclic algebra whose completed splitting field
is presented by a radical, of a coefficient which is a unit of the valuation ring, is the class
modulo the integers of the power residue exponent of the coefficient divided by the exponent.**
The invariant is the inverse of the norm residue symbol of the coefficient against the power of the
radical; that power has the divided valuation of the inverse of a uniformiser, so the tame
evaluation of the symbol applies after a skew symmetry, and the two signs cancel. -/
theorem placeInvariant_cyclicBrauerHom_of_radical_eq_powerResidue
    (hres : HasResidueChar ((primeUnder (𝓞 k) w).adicCompletion k) p e)
    (hinertia : Ideal.inertia Gal(K/k) w.asIdeal = ⊤)
    {ζ : (primeUnder (𝓞 k) w).adicCompletion k} (hζ : IsPrimitiveRoot ζ n)
    (hn : IsRadicalExponent n)
    (hpn : ¬ p ∣ n) {σ₀ : Gal(K/k)} (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀)
    {σ : Gal(w.adicCompletion K/(primeUnder (𝓞 k) w).adicCompletion k)}
    (hσ : ∀ x : Gal(w.adicCompletion K/(primeUnder (𝓞 k) w).adicCompletion k),
      x ∈ Subgroup.zpowers σ)
    (hrestr : (localDecompositionEquiv k w σ).restrictScalars k = σ₀)
    (hcard : Nat.card Gal(w.adicCompletion K/(primeUnder (𝓞 k) w).adicCompletion k) = n)
    {b : ((primeUnder (𝓞 k) w).adicCompletion k)ˣ} {ν : w.adicCompletion K}
    (hpow : ν ^ n
      = algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) (b : _))
    (hact : σ ν
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
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact zero_ne_one hu
  have hsymbol := localSymbol_unit_eq_powerResidue_of_congr (π := b)
    (b := Units.map (algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k)).toMonoidHom a)
    (u := Units.mk0 u hu0) (c := j)
    hres (isUnitValGen_one (valued_adicCompletion_surjective (primeUnder (𝓞 k) w))) hζ hn hpn hb hu
    hu1 hj
  rw [placeInvariant_cyclicBrauerHom_of_radical_of_inertia_eq_top k w hres hinertia hζ hσ₀ hσ
      hrestr hcard hpow hact a, hsymbol, map_neg, ofAdd_neg, inv_inv]

end PlaceRamified

end InverseGalois.CFT
