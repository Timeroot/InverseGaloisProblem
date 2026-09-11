/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.Selmer
import InverseGalois.CFT.PoitouTate.SUnitCharacter

/-!
# The residue of the symbol against a named family of local classes

A family of local classes having been named at finitely many finite places, the product of the norm
residue symbols of a unit of the base field against that family is a character of the units.  Its
values are killed by the exponent, the classes of the completions being, so the character is named
by a residue modulo the exponent and the naming is additive.

The residue is what the counting argument in the layers is able to annihilate.  A family which is a
product of powers of finitely many named families has for residue the corresponding combination of
their residues, so a linear relation among the residues of the named families forces the symbol
against the combination to be trivial — which is the orthogonality the prescription of the local
classes is asked for.

## Main definitions

* `InverseGalois.CFT.namedSymbolChar` — the character of the units whose value is the product of
  the norm residue symbols against a named family of local classes.
* `InverseGalois.CFT.namedSymbolResidue` — **the residue modulo the exponent naming that
  character.**

## Main results

* `InverseGalois.CFT.namedSymbolResidue_mul` — the residue is additive in the unit.
* `InverseGalois.CFT.localSymbolPiPairing_eq_one_of_sum_namedSymbolResidue_eq_zero` — **a family
  which is a product of powers of named families pairs trivially with a unit whose residues against
  those families satisfy the corresponding linear relation.**

## Tags

norm residue symbol, local class, character, Poitou-Tate, reciprocity
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section NamedSymbol

variable {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [NeZero ℓ]
  {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ} {ι : Type*} [Fintype ι]
  (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
  {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (w : ι → HeightOneSpectrum (𝓞 K))

/-- The character of the units of the base field whose value is the product of the norm residue
symbols against a named family of local classes. -/
noncomputable def namedSymbolChar (c : (μ : ι) → localClasses (w μ) ℓ) :
    Kˣ →* Multiplicative QModZ :=
  ((localSymbolPiPairing hres hζ w).flip c).comp (Pi.monoidHom fun μ => localClassHom (w μ) ℓ)

theorem namedSymbolChar_apply (c : (μ : ι) → localClasses (w μ) ℓ) (u : Kˣ) :
    namedSymbolChar hres hζ w c u
      = localSymbolPiPairing hres hζ w (fun μ => localClassHom (w μ) ℓ u) c := rfl

/-- The character of the units against a named family of local classes is killed by the exponent,
the classes of the completions being. -/
theorem namedSymbolChar_pow_eq_one (c : (μ : ι) → localClasses (w μ) ℓ) (u : Kˣ) :
    namedSymbolChar hres hζ w c u ^ ℓ = 1 := by
  show (((localSymbolPiPairing hres hζ w).flip c) (fun μ => localClassHom (w μ) ℓ u)) ^ ℓ = 1
  rw [← _root_.map_pow]
  convert _root_.map_one ((localSymbolPiPairing hres hζ w).flip c) using 2
  funext μ
  exact pow_eq_one_of_quotient_range_powMonoidHom ℓ _

/-- **The residue modulo the exponent naming the character of the units against a named family of
local classes.** -/
noncomputable def namedSymbolResidue (c : (μ : ι) → localClasses (w μ) ℓ) (u : Kˣ) : ZMod ℓ :=
  pTorsionResidue (namedSymbolChar hres hζ w c) (namedSymbolChar_pow_eq_one hres hζ w c) u

/-- The residue does name the value of the character. -/
theorem ofAdd_zmodQModZ_namedSymbolResidue (c : (μ : ι) → localClasses (w μ) ℓ) (u : Kˣ) :
    Multiplicative.ofAdd (zmodQModZ ℓ (namedSymbolResidue hres hζ w c u))
      = namedSymbolChar hres hζ w c u :=
  ofAdd_zmodQModZ_pTorsionResidue _ _ u

/-- **The residue of the symbol reads the unit only through its classes in the completions at the
named places.** -/
theorem namedSymbolResidue_congr (c : (μ : ι) → localClasses (w μ) ℓ) {u u' : Kˣ}
    (h : ∀ μ, localClassHom (w μ) ℓ u = localClassHom (w μ) ℓ u') :
    namedSymbolResidue hres hζ w c u = namedSymbolResidue hres hζ w c u' := by
  refine zmodQModZ_injective ℓ (Multiplicative.ofAdd.injective ?_)
  rw [ofAdd_zmodQModZ_namedSymbolResidue, ofAdd_zmodQModZ_namedSymbolResidue,
    namedSymbolChar_apply, namedSymbolChar_apply]
  exact congrArg
    (fun x : (μ : ι) → localClasses (w μ) ℓ => localSymbolPiPairing hres hζ w x c) (funext h)

/-- The residue of the symbol is additive in the unit. -/
theorem namedSymbolResidue_mul (c : (μ : ι) → localClasses (w μ) ℓ) (u u' : Kˣ) :
    namedSymbolResidue hres hζ w c (u * u')
      = namedSymbolResidue hres hζ w c u + namedSymbolResidue hres hζ w c u' :=
  pTorsionResidue_mul _ _ u u'

/-- The residue of the symbol vanishes exactly where the symbol is trivial. -/
theorem namedSymbolResidue_eq_zero_iff (c : (μ : ι) → localClasses (w μ) ℓ) (u : Kˣ) :
    namedSymbolResidue hres hζ w c u = 0 ↔
      localSymbolPiPairing hres hζ w (fun μ => localClassHom (w μ) ℓ u) c = 1 :=
  pTorsionResidue_eq_zero_iff _ _ u

/-- **A family which is a product of powers of named families pairs trivially with a unit whose
residues against those families satisfy the corresponding linear relation.** -/
theorem localSymbolPiPairing_eq_one_of_sum_namedSymbolResidue_eq_zero {d : ℕ}
    (ĉ : Fin d → (μ : ι) → localClasses (w μ) ℓ) (m : Fin d → ZMod ℓ)
    (c : (μ : ι) → localClasses (w μ) ℓ) (hc : c = ∏ t, ĉ t ^ (m t).val) (u : Kˣ)
    (hzero : ∑ t, m t * namedSymbolResidue hres hζ w (ĉ t) u = 0) :
    localSymbolPiPairing hres hζ w (fun μ => localClassHom (w μ) ℓ u) c = 1 := by
  have hstep : ∀ t : Fin d, (namedSymbolChar hres hζ w (ĉ t) u) ^ (m t).val
      = Multiplicative.ofAdd (zmodQModZ ℓ (m t * namedSymbolResidue hres hζ w (ĉ t) u)) := by
    intro t
    have hval : ((m t).val : ℕ) • namedSymbolResidue hres hζ w (ĉ t) u
        = m t * namedSymbolResidue hres hζ w (ĉ t) u := by
      rw [nsmul_eq_mul, ZMod.natCast_rightInverse (m t)]
    rw [← hval, _root_.map_nsmul, ofAdd_nsmul, ofAdd_zmodQModZ_namedSymbolResidue]
  calc localSymbolPiPairing hres hζ w (fun μ => localClassHom (w μ) ℓ u) c
      = ∏ t, (namedSymbolChar hres hζ w (ĉ t) u) ^ (m t).val := by
        rw [hc, _root_.map_prod]
        exact Finset.prod_congr rfl fun t _ =>
          _root_.map_pow (localSymbolPiPairing hres hζ w
            (fun μ => localClassHom (w μ) ℓ u)) (ĉ t) (m t).val
    _ = ∏ t, Multiplicative.ofAdd (zmodQModZ ℓ (m t * namedSymbolResidue hres hζ w (ĉ t) u)) :=
        Finset.prod_congr rfl fun t _ => hstep t
    _ = 1 := by
        rw [← ofAdd_sum, ← _root_.map_sum, hzero, _root_.map_zero]
        rfl

end NamedSymbol

end InverseGalois.CFT
