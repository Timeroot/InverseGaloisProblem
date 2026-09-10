/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.TameSymbol
import InverseGalois.CFT.PoitouTate.SplitClass

/-!
# The norm residue symbol on a cyclic group of classes

At an odd exponent the norm residue symbol of an element against itself is trivial: it equals the
symbol against minus one, and minus one is an odd power of itself.  Bilinearity then makes the
symbol vanish on any pair of powers of a single class, so a cyclic group of local classes is
isotropic for the symbol.

That is the second reason a prescription character can kill a radicand, alongside the one already
available: the unramified classes at a place away from the exponent are their own orthogonal
complement, so an unramified prescription pairs trivially with an unramified radicand.  The
isotropy of a cyclic group asks nothing about ramification at all — only that the class of the
radicand and the prescribed class be powers of one and the same class.  A prescription which is
ramified where it is carried is therefore still killed, provided every class it is compared
against at such a place lies on the same line as it does.

## Main results

* `InverseGalois.CFT.localSymbol_self_eq_one`: **at an odd exponent the norm residue symbol of an
  element against itself is trivial.**
* `InverseGalois.CFT.localSymbolQuotDual_eq_one_of_mem_zpowers`: **a cyclic group of classes of a
  local field is isotropic for the norm residue symbol** at an odd exponent.
* `InverseGalois.CFT.localClassPairing_eq_one_of_mem_zpowers`: the same, at a finite place of a
  number field.
* `InverseGalois.CFT.prescriptionChar_eq_one_of_mem_zpowers`: **the prescription character kills a
  unit whose class at each prescribed place lies on the same line as the prescribed class**, with
  no condition on ramification anywhere.

## Tags

norm residue symbol, local class, isotropic, cyclic, prescription character
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped Valued WithZero

/-! ### The symbol of a class against itself -/

section Local

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e n : ℕ} [NeZero n] {ζ : K}

/-- **At an odd exponent the norm residue symbol of an element against itself is trivial.**  The
symbol of an element against itself is its symbol against minus one, and at an odd exponent minus
one is an exponent-th power. -/
theorem localSymbol_self_eq_one (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (hodd : Odd n) (a : Kˣ) : localSymbol hres hm hζ a a = 1 := by
  rw [localSymbol_self_eq_neg_one hres hm hζ a]
  exact localSymbol_eq_one_of_isPow_right hres hm hζ a ⟨-1, hodd.neg_one_pow⟩

/-- **At an odd exponent a class of a local field pairs trivially with itself** under the norm
residue symbol read on the classes modulo exponent-th powers. -/
theorem localSymbolQuotDual_self_eq_one (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (hodd : Odd n)
    (x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) :
    localSymbolQuotDual hres hm hζ x x = 1 := by
  induction x using QuotientGroup.induction_on with
  | _ a => exact localSymbol_self_eq_one hres hm hζ hodd a

/-- **A cyclic group of classes of a local field is isotropic for the norm residue symbol** at an
odd exponent: two powers of one class pair to that class against itself, raised to the product of
the two powers, and a class pairs trivially with itself. -/
theorem localSymbolQuotDual_eq_one_of_mem_zpowers (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) (hodd : Odd n)
    {d x y : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range} (hx : x ∈ Subgroup.zpowers d)
    (hy : y ∈ Subgroup.zpowers d) : localSymbolQuotDual hres hm hζ x y = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  simp only [map_zpow, MonoidHom.zpow_apply, localSymbolQuotDual_self_eq_one hres hm hζ hodd d,
    one_zpow]

end Local

/-! ### A cyclic group of classes at a place of a number field -/

section Place

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **A cyclic group of classes at a finite place of a number field is isotropic** for the pairing
of local classes, at an odd exponent. -/
theorem localClassPairing_eq_one_of_mem_zpowers
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hodd : Odd n) (v : HeightOneSpectrum (𝓞 K))
    {d x y : localClasses v n} (hx : x ∈ Subgroup.zpowers d) (hy : y ∈ Subgroup.zpowers d) :
    localClassPairing hres hζ v x y = 1 :=
  localSymbolQuotDual_eq_one_of_mem_zpowers (hres v)
    (isUnitValGen_one (valued_adicCompletion_surjective v))
    (hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective) hodd hx hy

/-- **A class at a finite place of a number field pairs trivially with itself** at an odd
exponent. -/
theorem localClassPairing_self_eq_one
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hodd : Odd n) (v : HeightOneSpectrum (𝓞 K))
    (x : localClasses v n) : localClassPairing hres hζ v x x = 1 :=
  localClassPairing_eq_one_of_mem_zpowers hres hζ hodd v (Subgroup.mem_zpowers x)
    (Subgroup.mem_zpowers x)

/-- **The prescription character kills a unit whose class at each prescribed place lies on the
same line as the prescribed class.**  Where the prescription is trivial the factor disappears, and
where it is not the two classes are powers of one class, which the symbol is isotropic on.  Nothing
is asked about ramification: this is the reason available to a prescription which is ramified where
it is carried. -/
theorem prescriptionChar_eq_one_of_mem_zpowers
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hodd : Odd n) {T Tn : Finset (HeightOneSpectrum (𝓞 K))}
    {c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n}
    (hcT : ∀ v ∈ Tn, v ∉ T → c v = 1) {u : Kˣ}
    (hu : ∀ v ∈ T, ∃ d : localClasses v n,
      localClassHom v n u ∈ Subgroup.zpowers d ∧ c v ∈ Subgroup.zpowers d) :
    prescriptionChar hres hζ Tn c u = 1 := by
  classical
  rw [prescriptionChar_apply]
  refine Finset.prod_eq_one fun v hv => ?_
  by_cases hvT : v ∈ T
  · obtain ⟨d, hud, hcd⟩ := hu v hvT
    exact localClassPairing_eq_one_of_mem_zpowers hres hζ hodd v hud hcd
  · rw [hcT v hv hvT]
    exact _root_.map_one _

end Place

end InverseGalois.CFT
