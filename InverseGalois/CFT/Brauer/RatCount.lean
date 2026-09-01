/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceCyclotomic
import InverseGalois.CFT.Brauer.TotallyRealInvariant
import InverseGalois.CFT.Units.OrbitPlaces
import InverseGalois.CFT.Units.RatFundamentalClass

/-!
# Counting the local invariants of a cyclic algebra over the rationals

A cyclic algebra over the rationals whose splitting field sits inside a cyclotomic field has
trivial invariant at every finite place away from the conductor at which its coefficient is a unit,
because the place is unramified there and the coefficient contributes nothing.  If in addition the
splitting field is totally real, the archimedean invariants vanish as well.  So for a coefficient
which is a rational prime distinct from the only prime dividing the conductor, the sum of all the
local invariants has just two terms: the one at the coefficient and the one at the conductor.

That two-term identity is the shape in which reciprocity for such an algebra is proved: the two
surviving invariants are computed separately, one from the Frobenius of the cyclotomic extension
and one from the ramified place, and reciprocity is the statement that they cancel.

## Main results

* `InverseGalois.CFT.placeInvariant_cyclicBrauerHom_rat_eq_one_of_notMem`: **the invariant of a
  cyclic algebra over the rationals vanishes at a finite place away from the conductor at which the
  coefficient is a unit.**
* `InverseGalois.CFT.finprod_placeInvariant_eq_prod`: the product of the local invariants over the
  finite places is a finite product as soon as the invariants vanish outside a finite set.
* `InverseGalois.CFT.totalInvariant_cyclicBrauerHom_rat_eq_mul`: **the sum of all the local
  invariants of a cyclic algebra over the rationals with a totally real splitting field inside a
  cyclotomic field of prime-power conductor, and with a rational prime as coefficient, is the sum
  of just two of them.**

## Tags

Brauer group, local invariant, cyclic algebra, cyclotomic field, reciprocity, number field
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### The valuation of a scalar in the completion -/

section Scalar

/-- **The valuation of a scalar in the completion at a finite place is its valuation there.** -/
theorem valued_algebraMap_eq_valuation {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (x : K) :
    Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

end Scalar

/-! ### Vanishing away from the conductor -/

section Vanishing

variable {K : Type} [Field K] [NumberField K] [IsGalois ℚ K]

/-- **The invariant of a cyclic algebra over the rationals vanishes at a finite place away from the
conductor at which the coefficient is a unit.**  The splitting field is embedded in the cyclotomic
field of conductor `N`, and the place is asked to contain no prime dividing `N`, which makes it
unramified in the splitting field. -/
theorem placeInvariant_cyclicBrauerHom_rat_eq_one_of_notMem {σ₀ : Gal(K/ℚ)}
    (hσ₀ : ∀ x : Gal(K/ℚ), x ∈ Subgroup.zpowers σ₀) (N : ℕ) [NeZero N] (E : Type) [Field E]
    [NumberField E] [IsCyclotomicExtension {N} ℚ E] [Algebra K E]
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hN : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {a : ℚˣ}
    (ha : v.valuation ℚ (a : ℚ) = 1) :
    placeInvariant ℚ v (cyclicBrauerHom hσ₀ a) = 1 := by
  obtain ⟨w, rfl⟩ := exists_primeUnder_eq (𝓞 ℚ) (𝓞 K) v
  refine placeInvariant_cyclicBrauerHom_eq_one_of_valued_eq_one ℚ w hσ₀ ?_ ?_
  · refine ramIdx_rat_eq_one_of_forall_prime_not_dvd N E w fun ℓ hℓ hmem hdvd => ?_
    refine hN ℓ hℓ hdvd ?_
    rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmem
  · rw [valued_algebraMap_eq_valuation]
    exact ha

end Vanishing

/-! ### The product over the finite places -/

section Finprod

/-- **The product of the local invariants over the finite places is a finite product** over any
finite set outside which they all vanish. -/
theorem finprod_placeInvariant_eq_prod (k : Type) [Field k] [NumberField k]
    (x : BrauerGroup.{0, 0} k) (S : Finset (HeightOneSpectrum (𝓞 k)))
    (h : ∀ v ∉ S, placeInvariant k v x = 1) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x = ∏ v ∈ S, placeInvariant k v x :=
  finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
    by_contra hvS
    exact hv (h v fun hs => hvS (Finset.mem_coe.mpr hs))

end Finprod

/-! ### Two places suffice -/

section TwoPlaces

variable {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] [IsTotallyReal K]

/-- The finite places of the rationals attached to two distinct rational primes are distinct. -/
theorem ratPlace_ne_ratPlace {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ratPlace p hp ≠ ratPlace q hq := by
  intro h
  refine hpq ?_
  have hmem : ((p : ℕ) : 𝓞 ℚ) ∈ (ratPlace q hq).asIdeal := h ▸ natCast_mem_ratPlace p hp
  exact (natGenerator_eq_of_natCast_mem hp hmem).symm.trans
    (natGenerator_eq_of_natCast_mem hq (natCast_mem_ratPlace q hq))

/-- **The sum of all the local invariants of a cyclic algebra over the rationals has just two
terms** when the splitting field is totally real and sits inside a cyclotomic field whose conductor
has a single prime factor `q`, and the coefficient is a rational prime `p` other than `q`.  Every
other finite place is unramified in the splitting field and sees the coefficient as a unit, and the
archimedean invariants vanish because the splitting field is totally real. -/
theorem totalInvariant_cyclicBrauerHom_rat_eq_mul {σ₀ : Gal(K/ℚ)}
    (hσ₀ : ∀ x : Gal(K/ℚ), x ∈ Subgroup.zpowers σ₀) (N : ℕ) [NeZero N] (E : Type) [Field E]
    [NumberField E] [IsCyclotomicExtension {N} ℚ E] [Algebra K E] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hN : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → ℓ = q) {a : ℚˣ}
    (hap : (a : ℚ) = ((p : ℕ) : ℚ)) :
    totalInvariant ℚ (cyclicBrauerHom hσ₀ a)
      = placeInvariant ℚ (ratPlace p hp) (cyclicBrauerHom hσ₀ a)
        * placeInvariant ℚ (ratPlace q hq) (cyclicBrauerHom hσ₀ a) := by
  classical
  have hvan : ∀ v ∉ ({ratPlace p hp, ratPlace q hq} : Finset (HeightOneSpectrum (𝓞 ℚ))),
      placeInvariant ℚ v (cyclicBrauerHom hσ₀ a) = 1 := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    push_neg at hv
    obtain ⟨hvp, hvq⟩ := hv
    refine placeInvariant_cyclicBrauerHom_rat_eq_one_of_notMem hσ₀ N E v (fun ℓ hℓ hdvd hmem =>
      hvq ?_) ?_
    · refine heightOneSpectrum_rat_eq_of_natCast_mem hq ?_ (natCast_mem_ratPlace q hq)
      rw [← hN ℓ hℓ hdvd]
      exact hmem
    · rw [hap, valuation_natCast_eq_one_iff]
      intro hmem
      exact hvp (heightOneSpectrum_rat_eq_of_natCast_mem hp hmem (natCast_mem_ratPlace p hp))
  rw [totalInvariant_cyclicBrauerHom_rat hσ₀ a, finprod_placeInvariant_eq_prod ℚ _ _ hvan,
    Finset.prod_pair (ratPlace_ne_ratPlace hp hq hpq)]

end TwoPlaces

end InverseGalois.CFT
