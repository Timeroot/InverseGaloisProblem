/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.NormPlaceValue
import InverseGalois.CFT.Brauer.NormPrimesOver
import InverseGalois.CFT.Brauer.TotalInvariant

/-!
# Grouping the invariants of a number field by the rational prime below them

The total invariant of a class in the Brauer group of a number field is the product of its
invariants over all finite places, together with the archimedean contribution.  Comparing that
product with the corresponding product over the rationals means grouping the places of the number
field into the fibres of the map sending a place to the rational prime below it.

Two steps carry out the grouping.  Over a single fibre, the invariants are values of the additive
character on the residue degree times the value of a coefficient, and the norm formula for values
at places says exactly that those weighted values sum to the value at the rational prime of the
norm of the coefficient; the terms outside the fibre drop out because the residue degree of a
prime relative to another prime below a different one is zero.  Globally, a product over the
places of the number field is a product over the fibres of the products over each fibre, which is
the interchange of a doubly indexed product with finite support.

The invariants above a rational prime are also read off from residues rather than from values, in
which case each of them is the additive character applied to an exponent naming a power of a fixed
generator of the residue field.  Since only finitely many places lie above a rational prime, the
product over the fibre is then the character applied to the sum of the exponents, reduced modulo
the order of the generator.

## Main results

* `InverseGalois.CFT.finprod_ofAdd`: a product of exponentials of an additively written family is
  the exponential of its sum.
* `InverseGalois.CFT.natCast_finsum_mem_zmod`: reducing a finite sum of natural numbers modulo an
  integer is the sum of the reductions.
* `InverseGalois.CFT.finprod_placeInvariant_fibre`: **the product of the invariants over the places
  above a rational prime**, when each of them is the exponential of the residue degree times the
  value of a coefficient, is the exponential of the value at the rational prime of the norm of the
  coefficient.
* `InverseGalois.CFT.finprod_placeInvariant_fibre_eq_of_value`: **that product is the invariant at
  the rational prime** as soon as the latter is the exponential of the same exponent times the
  value there of the norm of the coefficient.
* `InverseGalois.CFT.finprod_placeInvariant_fibre_natCast`: **the same product when each invariant
  is instead the exponential of a residue exponent**, which is then the exponential of the sum of
  those exponents.
* `InverseGalois.CFT.finprod_placeInvariant_eq_of_fibre`: **the product of the invariants over all
  finite places agrees with a product over the rational primes** as soon as it does so fibre by
  fibre.

## Tags

number field, Brauer group, local invariant, total invariant, norm, residue degree, reciprocity,
class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField

/-! ## Products of exponentials -/

section OfAdd

/-- The multiplicative support of a family of exponentials is the support of its exponent. -/
theorem mulSupport_ofAdd {ι M : Type} [AddCommMonoid M] (f : ι → M) :
    Function.mulSupport (fun i => Multiplicative.ofAdd (f i)) = Function.support f := by
  ext i
  simp [Function.mulSupport, Function.support]

/-- A product of exponentials of an additively written family is the exponential of its sum. -/
theorem finprod_ofAdd {ι M : Type} [AddCommMonoid M] (f : ι → M) :
    ∏ᶠ i, Multiplicative.ofAdd (f i) = Multiplicative.ofAdd (∑ᶠ i, f i) := by
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum_of_support_subset f (s := h.toFinset) (by simp),
      finprod_eq_prod_of_mulSupport_subset _ (s := h.toFinset)
        (by rw [mulSupport_ofAdd]; simp), ofAdd_sum]
  · have hinf : (Function.mulSupport fun i => Multiplicative.ofAdd (f i)).Infinite := by
      rw [mulSupport_ofAdd]
      exact h
    rw [finsum_of_infinite_support h, finprod_of_infinite_mulSupport hinf]
    rfl

/-- Reducing a finite sum of natural numbers modulo an integer is the sum of the reductions. -/
theorem natCast_finsum_mem_zmod {ι : Type} {S : Set ι} (hS : S.Finite) (j : ι → ℕ) (N : ℕ) :
    ((∑ᶠ v ∈ S, j v : ℕ) : ZMod N) = ∑ᶠ v ∈ S, ((j v : ℕ) : ZMod N) := by
  classical
  have hsupp : (Function.support (Set.indicator S j)).Finite :=
    hS.subset Set.support_indicator_subset
  have h := AddMonoidHom.map_finsum (Nat.castAddMonoidHom (ZMod N)) hsupp
  rw [finsum_mem_def, finsum_mem_def]
  simp only [Nat.coe_castAddMonoidHom] at h
  rw [h]
  refine finsum_congr fun v => ?_
  by_cases hv : v ∈ S
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, Nat.cast_zero]

end OfAdd

/-! ## A single fibre -/

section Fibre

variable {k : Type} [Field k] [NumberField k]

/-- **The product of the invariants over the places above a rational prime**, when each of them is
the exponential of a fixed exponent times the residue degree times the value of a coefficient, is
the exponential of that exponent times the value at the rational prime of the norm of the
coefficient.  The places outside the fibre contribute nothing, because the residue degree of a
prime relative to a rational prime other than the one below it is zero. -/
theorem finprod_placeInvariant_fibre {N : ℕ} (X : BrauerGroup.{0, 0} k) (a : kˣ) (c : ℕ)
    (P : HeightOneSpectrum (𝓞 ℚ))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 k), primeUnder (𝓞 ℚ) v = P →
      placeInvariant k v X = Multiplicative.ofAdd (intQModZ N
        ((c : ℤ) * (((P.asIdeal.inertiaDeg v.asIdeal : ℕ) : ℤ) * placeValue v a)))) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k),
        Set.mulIndicator {u | primeUnder (𝓞 ℚ) u = P} (fun u => placeInvariant k u X) v
      = Multiplicative.ofAdd (intQModZ N
        ((c : ℤ) * placeValue P (Units.map (Algebra.norm ℚ : k →* ℚ) a))) := by
  set H : HeightOneSpectrum (𝓞 k) → ℤ :=
    fun v => ((P.asIdeal.inertiaDeg v.asIdeal : ℕ) : ℤ) * placeValue v a with hHdef
  set φ : ℤ →+ QModZ := (intQModZ N).comp (AddMonoidHom.mulLeft (c : ℤ)) with hφdef
  have hφ : ∀ z : ℤ, φ z = intQModZ N ((c : ℤ) * z) := fun _ => rfl
  have hH : (Function.support H).Finite := by
    have hfin := finite_support_inertiaDeg_placeOrd (k := ℚ) (K := k) P
      (x := (a : k)) (Units.ne_zero a)
    refine hfin.subset fun v hv => ?_
    simpa [hHdef, placeValue_eq_placeOrd] using hv
  have hterm : ∀ v : HeightOneSpectrum (𝓞 k),
      Set.mulIndicator {u | primeUnder (𝓞 ℚ) u = P} (fun u => placeInvariant k u X) v
        = Multiplicative.ofAdd (φ (H v)) := by
    intro v
    by_cases h : primeUnder (𝓞 ℚ) v = P
    · rw [Set.mulIndicator_of_mem (show v ∈ {u | primeUnder (𝓞 ℚ) u = P} from h) _,
        hloc v h, hφ]
    · have hcomap : Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 k)) v.asIdeal ≠ P.asIdeal := fun hc =>
        h (HeightOneSpectrum.ext hc)
      rw [Set.mulIndicator_of_notMem (show v ∉ {u | primeUnder (𝓞 ℚ) u = P} from h) _,
        hφ, hHdef]
      simp [inertiaDeg_eq_zero_of_comap_ne hcomap]
  rw [finprod_congr hterm, finprod_ofAdd, ← AddMonoidHom.map_finsum φ hH, hφ, hHdef,
    ← placeValue_normUnit P a]

/-- **The product of the invariants over the places above a rational prime is the invariant at that
prime**, as soon as each of them is the exponential of a fixed exponent times the residue degree
times the value of a coefficient and the invariant at the prime is the exponential of the same
exponent times the value there of the norm of the coefficient. -/
theorem finprod_placeInvariant_fibre_eq_of_value {N : ℕ} (X : BrauerGroup.{0, 0} k)
    (Z : BrauerGroup.{0, 0} ℚ) (a : kˣ) (c : ℕ) (P : HeightOneSpectrum (𝓞 ℚ))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 k), primeUnder (𝓞 ℚ) v = P →
      placeInvariant k v X = Multiplicative.ofAdd (intQModZ N
        ((c : ℤ) * (((P.asIdeal.inertiaDeg v.asIdeal : ℕ) : ℤ) * placeValue v a))))
    (hlocP : placeInvariant ℚ P Z = Multiplicative.ofAdd (intQModZ N
      ((c : ℤ) * placeValue P (Units.map (Algebra.norm ℚ : k →* ℚ) a)))) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k),
        Set.mulIndicator {u | primeUnder (𝓞 ℚ) u = P} (fun u => placeInvariant k u X) v
      = placeInvariant ℚ P Z := by
  rw [finprod_placeInvariant_fibre X a c P hloc, hlocP]

/-- **The product of the invariants over the places above a rational prime**, when each of them is
the exponential of a residue exponent read modulo an integer, is the exponential of the sum of
those exponents.  The places outside the fibre contribute nothing. -/
theorem finprod_placeInvariant_fibre_natCast {N : ℕ} [NeZero N] (X : BrauerGroup.{0, 0} k)
    (P : HeightOneSpectrum (𝓞 ℚ)) (j : HeightOneSpectrum (𝓞 k) → ℕ)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 k), primeUnder (𝓞 ℚ) v = P →
      placeInvariant k v X = Multiplicative.ofAdd (zmodQModZ N ((j v : ℕ) : ZMod N))) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k),
        Set.mulIndicator {u | primeUnder (𝓞 ℚ) u = P} (fun u => placeInvariant k u X) v
      = Multiplicative.ofAdd (zmodQModZ N
          (((∑ᶠ v ∈ {u : HeightOneSpectrum (𝓞 k) | primeUnder (𝓞 ℚ) u = P}, j v : ℕ) :
            ZMod N))) := by
  classical
  set S : Set (HeightOneSpectrum (𝓞 k)) := {u | primeUnder (𝓞 ℚ) u = P} with hSdef
  set J : HeightOneSpectrum (𝓞 k) → ZMod N := Set.indicator S (fun u => ((j u : ℕ) : ZMod N))
    with hJdef
  have hS : S.Finite := finite_placesOver P
  have hsupp : (Function.support J).Finite := hS.subset Set.support_indicator_subset
  have hterm : ∀ v : HeightOneSpectrum (𝓞 k),
      Set.mulIndicator S (fun u => placeInvariant k u X) v
        = Multiplicative.ofAdd (zmodQModZ N (J v)) := by
    intro v
    by_cases hv : v ∈ S
    · rw [Set.mulIndicator_of_mem hv, hloc v hv, hJdef, Set.indicator_of_mem hv]
    · rw [Set.mulIndicator_of_notMem hv, hJdef, Set.indicator_of_notMem hv, map_zero]
      rfl
  rw [finprod_congr hterm, finprod_ofAdd, ← AddMonoidHom.map_finsum (zmodQModZ N) hsupp,
    natCast_finsum_mem_zmod hS j N, finsum_mem_def]

end Fibre

/-! ## Assembling the fibres -/

section Assembly

variable {k : Type} [Field k] [NumberField k]

/-- **The product of the invariants over all finite places of a number field agrees with a product
over the rational primes** as soon as it does so fibre by fibre.  A product over the places of the
number field is the product over the rational primes of the products over the places above them,
by the interchange of a doubly indexed product with finite support. -/
theorem finprod_placeInvariant_eq_of_fibre (X : BrauerGroup.{0, 0} k) (Z : BrauerGroup.{0, 0} ℚ)
    (hfib : ∀ P : HeightOneSpectrum (𝓞 ℚ),
      ∏ᶠ v : HeightOneSpectrum (𝓞 k),
          Set.mulIndicator {u | primeUnder (𝓞 ℚ) u = P} (fun u => placeInvariant k u X) v
        = placeInvariant ℚ P Z) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v X
      = ∏ᶠ P : HeightOneSpectrum (𝓞 ℚ), placeInvariant ℚ P Z := by
  set h : HeightOneSpectrum (𝓞 ℚ) × HeightOneSpectrum (𝓞 k) → Multiplicative QModZ :=
    fun x => Set.mulIndicator {u | primeUnder (𝓞 ℚ) u = x.1}
      (fun u => placeInvariant k u X) x.2 with hdef
  have hval : ∀ P v, h (P, v) =
      Set.mulIndicator {u | primeUnder (𝓞 ℚ) u = P} (fun u => placeInvariant k u X) v :=
    fun _ _ => rfl
  have hfin : (Function.mulSupport h).Finite := by
    refine ((finite_setOf_placeInvariant_ne_one X).image
      fun v => (primeUnder (𝓞 ℚ) v, v)).subset ?_
    rintro ⟨P, v⟩ hx
    rw [Function.mem_mulSupport, hval] at hx
    have hmem : v ∈ {u | primeUnder (𝓞 ℚ) u = P} := by
      by_contra hc
      exact hx (Set.mulIndicator_of_notMem hc _)
    refine ⟨v, ?_, ?_⟩
    · intro hc
      rw [Set.mulIndicator_of_mem hmem] at hx
      exact hx hc
    · show (primeUnder (𝓞 ℚ) v, v) = (P, v)
      rw [show primeUnder (𝓞 ℚ) v = P from hmem]
  have hswap : (Function.mulSupport fun x : HeightOneSpectrum (𝓞 k) × HeightOneSpectrum (𝓞 ℚ) =>
      h (x.2, x.1)).Finite :=
    hfin.preimage ((Equiv.prodComm (HeightOneSpectrum (𝓞 k))
      (HeightOneSpectrum (𝓞 ℚ))).injective.injOn)
  have hcurry1 : ∏ᶠ x, h x = ∏ᶠ P, ∏ᶠ v, h (P, v) := finprod_curry h hfin
  have hcurry2 : ∏ᶠ (x : HeightOneSpectrum (𝓞 k) × HeightOneSpectrum (𝓞 ℚ)), h (x.2, x.1)
      = ∏ᶠ v, ∏ᶠ P, h (P, v) :=
    finprod_curry (fun x : HeightOneSpectrum (𝓞 k) × HeightOneSpectrum (𝓞 ℚ) => h (x.2, x.1))
      hswap
  have hcomm : ∏ᶠ (x : HeightOneSpectrum (𝓞 k) × HeightOneSpectrum (𝓞 ℚ)), h (x.2, x.1)
      = ∏ᶠ x, h x :=
    finprod_comp_equiv (Equiv.prodComm (HeightOneSpectrum (𝓞 k)) (HeightOneSpectrum (𝓞 ℚ)))
      (f := h)
  have hsingle : ∀ v : HeightOneSpectrum (𝓞 k), ∏ᶠ P, h (P, v) = placeInvariant k v X := by
    intro v
    rw [finprod_eq_single (fun P => h (P, v)) (primeUnder (𝓞 ℚ) v) ?_, hval,
      Set.mulIndicator_of_mem (show v ∈ {u | primeUnder (𝓞 ℚ) u = primeUnder (𝓞 ℚ) v} from rfl)]
    intro P hP
    show h (P, v) = 1
    rw [hval]
    exact Set.mulIndicator_of_notMem
      (show v ∉ {u | primeUnder (𝓞 ℚ) u = P} from fun hc => hP (Eq.symm hc))
      (fun u => placeInvariant k u X)
  calc ∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v X
      = ∏ᶠ v, ∏ᶠ P, h (P, v) := (finprod_congr hsingle).symm
    _ = ∏ᶠ x, h x := by rw [← hcurry2, hcomm]
    _ = ∏ᶠ P, ∏ᶠ v, h (P, v) := hcurry1
    _ = ∏ᶠ P, placeInvariant ℚ P Z := finprod_congr fun P => by
          simpa only [hval] using hfib P

end Assembly

end InverseGalois.CFT
