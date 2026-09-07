/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.DecompositionLocalPower
import InverseGalois.CFT.Kummer.LocalPower
import InverseGalois.CFT.PoitouTate.Prescribed

/-!
# The character prescribed by local classes, on the radicands of an extension

Pairing the local classes of a unit of a number field, at the finite places of a finite set,
against a prescribed assignment of local classes gives a character of the units of the field.
Such a character is what the construction of a Chebotarev place is fed with, and what it asks of
it is that the units whose radicals generate the extension at hand be killed.

That hypothesis holds for a very concrete reason.  At a place of the base field over which the
extension splits completely, the decomposition group above is trivial, so a radical of the unit is
fixed by it, which by Kummer theory in the completion says that the unit is already a power there:
its local class is trivial and the factor of the character at that place disappears.  So if all
but finitely many of the prescribed classes come from a single global unit, and if the extension
splits completely at every place where they do not, the character of a radicand is a product over
the remaining places of norm residue symbols of two `S`-units, which the product formula sends
to one.

## Main results

* `InverseGalois.CFT.localClassHom_eq_one_of_stabilizer_eq_bot`: **a radicand is a power already in
  the completion below a place whose decomposition group is trivial.**
* `InverseGalois.CFT.prescriptionChar`: the character of the units given by pairing their local
  classes against a prescribed assignment.
* `InverseGalois.CFT.prescriptionChar_eq_one_of_pow`: **the prescription character kills every
  radicand**, when the prescription comes from a global `S`-unit away from the places at which the
  extension splits completely.

## Tags

norm residue symbol, local class, completely split, Kummer theory, product formula, S-unit
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

/-! ### A radicand at a place that splits completely -/

section Split

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] {p : ℕ}

/-- **A radicand is a power already in the completion below a place whose decomposition group is
trivial.**  A trivial decomposition group fixes the radical for nothing, so Kummer theory in the
completion produces a root of the radicand there, and a root of a unit is a root up to a unit. -/
theorem localClassHom_eq_one_of_stabilizer_eq_bot (hp : p ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {w : HeightOneSpectrum (𝓞 M)}
    (hw : stabilizer Gal(M/K) w = ⊥) {u : Kˣ} {b : M}
    (hb : algebraMap K M (u : K) = b ^ p) :
    localClassHom (primeUnder (𝓞 K) w) p u = 1 := by
  obtain ⟨c, hc⟩ := (forall_stabilizer_smul_eq_iff_exists_pow w hζ hp hb).1 fun σ => by
    have hσ : (σ : Gal(M/K)) = 1 := (Subgroup.eq_bot_iff_forall _).1 hw _ σ.2
    rw [hσ]
    rfl
  obtain ⟨d, hd⟩ := exists_units_pow_eq_of_pow_eq_coe hp
    (u := Units.map (algebraMap K ((primeUnder (𝓞 K) w).adicCompletion K)).toMonoidHom u)
    (c := c) (by rw [Units.coe_map]; exact hc)
  exact (QuotientGroup.eq_one_iff _).2 ⟨d, hd⟩

end Split

/-! ### The character prescribed by an assignment of local classes -/

section Character

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- The character of the units of a number field obtained by pairing their local classes, at the
finite places of a finite set, against a prescribed assignment of local classes. -/
noncomputable def prescriptionChar
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n) : Kˣ →* Multiplicative QModZ :=
  ∏ v ∈ T, ((localClassPairing hres hζ v).flip (c v)).comp (localClassHom v n)

theorem prescriptionChar_apply
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n) (u : Kˣ) :
    prescriptionChar hres hζ T c u
      = ∏ v ∈ T, localClassPairing hres hζ v (localClassHom v n u) (c v) := by
  simp only [prescriptionChar, MonoidHom.finset_prod_apply, MonoidHom.coe_comp,
    Function.comp_apply, MonoidHom.flip_apply]

/-- The value of the prescription character is killed by the exponent, every local class being. -/
theorem pow_prescriptionChar_eq_one
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n) (u : Kˣ) :
    prescriptionChar hres hζ T c u ^ n = 1 := by
  rw [prescriptionChar_apply, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [← _root_.map_pow, pow_eq_one_of_quotient_range_powMonoidHom n (c v), map_one]

/-- The pairing of the classes of two units of the number field is their norm residue symbol. -/
theorem localClassPairing_eq_localSymbol
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    localClassPairing hres hζ v (localClassHom v n b) (localClassHom v n a)
      = localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
          (hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective)
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom b) := rfl

end Character

/-! ### The prescription character on the radicands -/

section Radicand

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] {n : ℕ} [NeZero n] {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **The prescription character kills every radicand of the extension.**  At a place outside the
part of the prescription carried by a global unit the extension splits completely, so the local
class of a radicand there is trivial and its factor disappears; what is left is the product over
the remaining places of the norm residue symbols of two `S`-units, which is the same as the
product over all of `S` for the same reason, and the product formula sends that to one. -/
theorem prescriptionChar_eq_one_of_pow (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {T₀ T S : Finset (HeightOneSpectrum (𝓞 K))}
    (hT₀ : T₀ ⊆ T) (hTS : T ⊆ S)
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ S)
    {c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n} {g : Kˣ}
    (hg : g ∈ sUnits K (S : Set (HeightOneSpectrum (𝓞 K))))
    (hc : ∀ v ∈ T₀, c v = localClassHom v n g)
    (hsplit : ∀ v ∈ S, v ∉ T₀ → ∃ w : HeightOneSpectrum (𝓞 M),
      primeUnder (𝓞 K) w = v ∧ stabilizer Gal(M/K) w = ⊥)
    {u : Kˣ} (hu : u ∈ sUnits K (S : Set (HeightOneSpectrum (𝓞 K)))) {b : M}
    (hb : algebraMap K M (u : K) = b ^ n) :
    prescriptionChar hres hζ T c u = 1 := by
  classical
  -- the local class of the radicand is trivial wherever the extension splits completely
  have hzero : ∀ v ∈ S, v ∉ T₀ → localClassHom v n u = 1 := by
    intro v hv hv0
    obtain ⟨w, rfl, hw⟩ := hsplit v hv hv0
    exact localClassHom_eq_one_of_stabilizer_eq_bot (NeZero.ne n) hζ hw hb
  -- so the character is a product over the places where the prescription comes from a unit
  have e1 : ∏ v ∈ T₀, localClassPairing hres hζ v (localClassHom v n u) (c v)
      = ∏ v ∈ T, localClassPairing hres hζ v (localClassHom v n u) (c v) :=
    Finset.prod_subset hT₀ fun v hv hv0 => by
      rw [hzero v (hTS hv) hv0, _root_.map_one, MonoidHom.one_apply]
  rw [prescriptionChar_apply, ← e1]
  have e2 : ∏ v ∈ T₀, localClassPairing hres hζ v (localClassHom v n u) (c v)
      = ∏ v ∈ T₀, localClassPairing hres hζ v (localClassHom v n u) (localClassHom v n g) :=
    Finset.prod_congr rfl fun v hv => by rw [hc v hv]
  rw [e2]
  -- the same product over the whole of `S`, and the product formula
  have e3 : ∏ v ∈ T₀, localClassPairing hres hζ v (localClassHom v n u) (localClassHom v n g)
      = ∏ v ∈ S, localClassPairing hres hζ v (localClassHom v n u) (localClassHom v n g) :=
    Finset.prod_subset (hT₀.trans hTS) fun v hv hv0 => by
      rw [hzero v hv hv0, _root_.map_one, MonoidHom.one_apply]
  rw [e3]
  have hprod := prod_localSymbol_eq_one_of_ne_two hn hn2 hres hζ g u S ?_
  · simpa only [← localClassPairing_eq_localSymbol hres hζ] using hprod
  · intro v hvS
    have hnv : FinitePlace.mk v ((n : ℕ) : K) = 1 := by
      by_contra hcon
      exact hvS (hnS v hcon)
    exact localSymbol_eq_one_of_valued_eq_one (hres v) _ _ hn
      (not_dvd_of_finitePlace_natCast_eq_one (hres v) hnv)
      (valued_map_eq_one_of_mem_sUnits hg fun h => hvS (Finset.mem_coe.1 h))
      (valued_map_eq_one_of_mem_sUnits hu fun h => hvS (Finset.mem_coe.1 h))

end Radicand

end InverseGalois.CFT
