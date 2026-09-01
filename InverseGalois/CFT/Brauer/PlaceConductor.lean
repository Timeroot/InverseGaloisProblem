/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclotomicGenerator
import InverseGalois.CFT.Brauer.PlaceRamifiedAut
import InverseGalois.CFT.Brauer.PlaceSubcyclotomic
import InverseGalois.CFT.Brauer.ResidueCard
import InverseGalois.CFT.Cyclotomic.CyclicSubfield
import InverseGalois.CFT.Cyclotomic.TotallyRamified
import InverseGalois.CFT.Local.ResidueDiscreteLog
import InverseGalois.CFT.Units.RadicalDescent

/-!
# The invariant at the place of the conductor of a subfield of a cyclotomic field

A subfield of the cyclotomic field of an odd prime conductor is totally ramified at that prime, and
the completion there is presented by a radical of the opposite of the prime whose exponent is the
degree of the subfield.  The chosen generator multiplies that radical by a root of unity whose
residue is the complementary power of the primitive root naming the generator, so the invariant of
a cyclic algebra with a rational prime as coefficient is read off by the power residue symbol of
that coefficient.

The exponent the symbol produces is the discrete logarithm of the coefficient to the base of the
primitive root, which is exactly the exponent expressing the automorphism raising the roots of
unity to the power of the coefficient as a power of the generator.  That is the same exponent the
place attached to the coefficient produces, with the opposite sign; so the two places cancel.

## Main results

* `InverseGalois.CFT.placeInvariant_cyclicBrauerHom_conductor`: **the invariant, at the place of an
  odd prime conductor, of a cyclic algebra over the rationals split by a subfield of the cyclotomic
  field of that conductor, with a rational prime away from the conductor as coefficient**, is the
  class of the exponent expressing the automorphism raising the roots of unity to the power of that
  coefficient as a power of the generator.

## Tags

cyclotomic field, subfield, Brauer group, local invariant, cyclic algebra, totally ramified,
power residue symbol, reciprocity, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise WithZero

/-! ### The invariant at the place of the conductor -/

section Conductor

attribute [local instance] isGalois_adicCompletion

variable (q : ℕ) [NeZero q] (L F : Type) [Field L] [NumberField L]
  [IsCyclotomicExtension {q} ℚ L] [IsGalois ℚ L] [Field F] [NumberField F] [Algebra F L]
  [IsScalarTower ℚ F L] [IsGalois ℚ F]

/-- **The invariant, at the place of an odd prime conductor, of a cyclic algebra over the rationals
split by a subfield of the cyclotomic field of that conductor, with a rational prime away from the
conductor as coefficient.**  The completion of the subfield there is presented by a radical of the
opposite of the conductor whose exponent is the degree of the subfield, and the generator
multiplies that radical by the root of unity whose residue is the complementary power of the
primitive root; the power residue symbol of the coefficient then reads the discrete logarithm of
the coefficient to the base of that primitive root, which is the exponent expressing the
automorphism raising the roots of unity to the power of the coefficient as a power of the
generator. -/
theorem placeInvariant_cyclicBrauerHom_conductor (hq : q.Prime) (hodd : Odd q)
    (W : HeightOneSpectrum (𝓞 L)) [W.asIdeal.LiesOver (Ideal.span {(q : ℤ)})] {N : ℕ}
    [NeZero N] (hNodd : Odd N) (hcard : Nat.card Gal(F/ℚ) = N)
    (hinertia : Ideal.inertia Gal(F/ℚ) (primeUnder (𝓞 F) W).asIdeal = ⊤) {g : ℕ}
    (hg : Nat.Coprime g q) (hgord : ∀ k : ℕ, q ∣ g ^ k - 1 → (q - 1) ∣ k)
    (hgen : ∀ x : Gal(L/ℚ), x ∈ Subgroup.zpowers (cyclotomicPowerAut q L hg)) {p : ℕ}
    (hp : Nat.Coprime p q) {c : ℕ}
    (hc : cyclotomicPowerAut q L hp = cyclotomicPowerAut q L hg ^ c) {a : ℚˣ}
    (hap : (a : ℚ) = ((p : ℕ) : ℚ)) :
    placeInvariant ℚ (primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W))
        (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := F) hgen) a)
      = Multiplicative.ofAdd (zmodQModZ N (c : ZMod N)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsGalois F L := IsGalois.tower_top_of_isGalois ℚ F L
  haveI : Module.Finite F L := FiniteDimensional.right ℚ F L
  -- the place of the conductor, seen in the three fields of the tower
  have hmemL : ((q : ℕ) : 𝓞 L) ∈ W.asIdeal := natCast_mem_of_liesOver_span (q := q) W.asIdeal
  have hmemF : ((q : ℕ) : 𝓞 F) ∈ (primeUnder (𝓞 F) W).asIdeal := by
    rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmemL
  have hmemQ : ((q : ℕ) : 𝓞 ℚ) ∈ (primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).asIdeal := by
    rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmemF
  haveI := liesOver_span_of_natCast_mem hq (primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)) hmemQ
  have hres : HasResidueChar
      ((primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ) q 1 :=
    hasResidueChar_adicCompletion_rat_of_mem hq _ hmemQ
  -- the degrees of the tower
  have hMN : Module.finrank F L * N = q - 1 := by
    have hfin : Module.finrank ℚ F * Module.finrank F L = Module.finrank ℚ L :=
      Module.finrank_mul_finrank ℚ F L
    have hNcard : Module.finrank ℚ F = N := by
      rw [← IsGalois.card_aut_eq_finrank ℚ F, hcard]
    rw [← hNcard, mul_comm, hfin, finrank_cyclotomic_of_prime q L]
  have hqN : ¬ q ∣ N := by
    intro hd
    have h1 : q ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hd
    have h2 : N ≤ q - 1 := Nat.le_of_dvd (by have := hq.one_lt; omega) (Dvd.intro_left _ hMN)
    have := hq.one_lt
    omega
  have hgnd : ¬ q ∣ g := (Nat.Prime.coprime_iff_not_dvd hq).mp hg.symm
  -- the root of unity of the completion of the rationals with the prescribed residue
  obtain ⟨ζ, hζprim, hζres⟩ :=
    exists_isPrimitiveRoot_valued_sub_natCast_lt_one hres hgnd hgord (NeZero.ne N) hMN
  -- the generator fixes the place of the conductor, which is totally ramified
  obtain ⟨ζL, hζL⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := ({q} : Set ℕ)) ℚ L
    rfl (NeZero.ne q)
  haveI : IsCyclotomicExtension {q ^ 1} ℚ L := by rwa [pow_one]
  have hinertiaL : Ideal.inertia Gal(L/ℚ) W.asIdeal = ⊤ :=
    inertia_eq_top_cyclotomic_primePow q 1 L W.asIdeal
  have hσW : cyclotomicPowerAut q L hg • W = W := by
    have hstab := stabilizer_place_eq_top_of_inertia_eq_top (k := ℚ) W hinertiaL
    have hmem : cyclotomicPowerAut q L hg ∈ stabilizer Gal(L/ℚ) W := by
      rw [hstab]
      exact Subgroup.mem_top _
    exact hmem
  have hσζ : cyclotomicPowerAut q L hg ζL = ζL ^ g :=
    cyclotomicPowerAut_apply q L hg hζL.pow_eq_one
  -- the radical presenting the completion of the subfield
  obtain ⟨ν, hνpow, hνact⟩ :=
    exists_pow_eq_neg_natCast_aut_eq_algebraMap_mul (k := ℚ) F W hq hodd hζL hmemL hMN
      (IsGalois.card_aut_eq_finrank F L) hσW hσζ hζprim.pow_eq_one hζres
  have hst : (cyclotomicPowerAut q L hg).restrictNormal F • primeUnder (𝓞 F) W
      = primeUnder (𝓞 F) W := restrictNormalHom_smul_primeUnder F hσW
  have hact : adicCompletionAut (primeUnder (𝓞 F) W)
        ((cyclotomicPowerAut q L hg).restrictNormal F) hst ν
      = algebraMap ((primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ)
          ((primeUnder (𝓞 F) W).adicCompletion F) ζ * ν := hνact
  -- the coefficient of the radical is a uniformiser of the completion of the rationals
  have hqne : ((q : ℕ) : (primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ) ≠ 0 :=
    hres.natCast_ne_zero hq.ne_zero
  have hpow : ν ^ N = algebraMap ((primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ)
      ((primeUnder (𝓞 F) W).adicCompletion F)
      ((Units.mk0 (-((q : ℕ) : (primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ))
        (neg_ne_zero.mpr hqne) : ((primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ)ˣ) :
        _) := by
    rw [hνpow, Units.val_mk0, map_neg, map_natCast]
  have hb : unitValDiv (isUnitValGen_one
        (valued_adicCompletion_surjective (primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W))))
      (Additive.ofMul (Units.mk0
        (-((q : ℕ) : (primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ))
        (neg_ne_zero.mpr hqne))) = -1 := by
    refine unitValDiv_eq_neg_one_of_valued_eq_exp_neg_one
      (valued_adicCompletion_surjective (primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W))) ?_
    rw [Units.val_mk0, Valuation.map_neg]
    exact valued_natCast_adicCompletion_rat hq _
  have hcardres : Nat.card (DivisionResidue
      ((primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ)
      ((primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ)) = q :=
    natCard_divisionResidue_adicCompletion_rat hq _ hmemQ
  have hdiv : (q - 1) / N = Module.finrank F L :=
    Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne N)) hMN.symm
  refine placeInvariant_cyclicBrauerHom_of_radical_aut ℚ (primeUnder (𝓞 F) W) hres hinertia
    hζprim (isRadicalExponent_of_odd hNodd) hqN (forall_mem_zpowers_restrictNormal (L := F) hgen)
    hst hcard hpow hact hb
    (u := ((g : ℕ) : (primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ)) ?_ ?_ ?_
  · exact valued_natCast_eq_one_of_not_dvd hq (valued_residueChar_lt_one hres) hgnd
  · rw [hcardres, hdiv, ← Nat.cast_pow]
    exact hζres
  · have hcast : ((((p : ℕ) : ℤ) - ((g ^ c : ℕ) : ℤ) : ℤ) :
        (primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ)
        = ((p : ℕ) : (primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ)
          - ((g : ℕ) : (primeUnder (𝓞 ℚ) (primeUnder (𝓞 F) W)).adicCompletion ℚ) ^ c := by
      push_cast
      ring
    rw [hap, map_natCast, ← hcast]
    exact valued_intCast_lt_one_of_dvd hres
      (dvd_sub_pow_of_cyclotomicPowerAut_eq_pow q L hg hp hc)

end Conductor

end InverseGalois.CFT
