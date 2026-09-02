/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.BaseCyclotomic
import InverseGalois.CFT.Brauer.PrescribedValue

/-!
# Adjusting a unit by a norm at the totally ramified places

The cyclic algebra construction kills the norms from the splitting field, so a unit of the base may
be modified by any such norm without changing its Brauer class.  When a rational prime is totally
ramified in the splitting field, this freedom is enough to make the unit trivial at every place
above that prime.

Total ramification is what makes the norm easy to compute.  If the inertia group at a place of the
extension is the whole Galois group, then that place is the only one above the place beneath it and
its residue degree is one, so the value of a norm at the place below is exactly the value of the
element at the place above.  Values at finitely many places may be prescribed at will, so the norms
realise every family of values at the places above the totally ramified prime.

Together with the observation that a unit trivial at finitely many places is a quotient of algebraic
integers trivial there, this reduces a statement about the Brauer classes of arbitrary units to the
same statement for algebraic integers which are units at the prime in question.

## Main results

* `InverseGalois.CFT.unique_of_inertia_eq_top`: **a place whose inertia group is the whole Galois
  group is the only place above the place beneath it, and has residue degree one.**
* `InverseGalois.CFT.exists_normUnit_placeValue_eq`: **prescribed values of a norm.**
* `InverseGalois.CFT.inertia_eq_top_of_natCast_mem`: **a rational prime unramified in the base and
  totally ramified in a Galois extension of the rationals is totally ramified in the compositum.**
* `InverseGalois.CFT.totalInvariant_eq_one_of_integral_qunit`: **a homomorphism to the Brauer group
  killing the norms and with trivial total invariant on the algebraic integers which are units at a
  totally ramified prime has trivial total invariant everywhere.**

## Tags

number field, place, norm, inertia group, totally ramified, Brauer group, reciprocity,
class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField InverseGalois.NumberTheory

/-! ### Consequences of total ramification at a place -/

section Unique

variable {k E : Type} [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
  [IsGalois k E]

/-- **A place whose inertia group is the whole Galois group is the only place above the place
beneath it, and has residue degree one.**  The number of places above, the order of the inertia
group and the residue degree multiply to the order of the Galois group, so once the inertia group
is everything the other two factors are trivial. -/
theorem unique_of_inertia_eq_top (w : HeightOneSpectrum (𝓞 E))
    (hinertia : Ideal.inertia Gal(E/k) w.asIdeal = ⊤) :
    (∀ w' : HeightOneSpectrum (𝓞 E), primeUnder (𝓞 k) w' = primeUnder (𝓞 k) w → w' = w) ∧
      Ideal.inertiaDeg (primeUnder (𝓞 k) w).asIdeal w.asIdeal = 1 := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : w.asIdeal.IsMaximal := isMaximal_of_ne_bot_base w.asIdeal w.ne_bot
  haveI : w.asIdeal.LiesOver (primeUnder (𝓞 k) w).asIdeal := ⟨rfl⟩
  haveI : (primeUnder (𝓞 k) w).asIdeal.IsPrime := (primeUnder (𝓞 k) w).isPrime
  haveI : (primeUnder (𝓞 k) w).asIdeal.IsMaximal :=
    isMaximal_of_ne_bot_base (primeUnder (𝓞 k) w).asIdeal (primeUnder (𝓞 k) w).ne_bot
  haveI : Algebra.IsSeparable (𝓞 k ⧸ (primeUnder (𝓞 k) w).asIdeal) (𝓞 E ⧸ w.asIdeal) :=
    isSeparable_residue_of_ne_bot_base (k := k) w.asIdeal w.ne_bot
  have hkey := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := Gal(E/k))
    (primeUnder (𝓞 k) w).asIdeal w.asIdeal
  rw [hinertia, Nat.card_congr (Subgroup.topEquiv (G := Gal(E/k))).toEquiv] at hkey
  have hcard : Nat.card Gal(E/k) ≠ 0 := Nat.card_pos.ne'
  have hone : ((primeUnder (𝓞 k) w).asIdeal.primesOver (𝓞 E)).ncard = 1 ∧
      Module.finrank (𝓞 k ⧸ (primeUnder (𝓞 k) w).asIdeal) (𝓞 E ⧸ w.asIdeal) = 1 := by
    have h1 : Nat.card Gal(E/k) *
        (((primeUnder (𝓞 k) w).asIdeal.primesOver (𝓞 E)).ncard *
          Module.finrank (𝓞 k ⧸ (primeUnder (𝓞 k) w).asIdeal) (𝓞 E ⧸ w.asIdeal))
        = Nat.card Gal(E/k) * 1 :=
      calc Nat.card Gal(E/k) *
            (((primeUnder (𝓞 k) w).asIdeal.primesOver (𝓞 E)).ncard *
              Module.finrank (𝓞 k ⧸ (primeUnder (𝓞 k) w).asIdeal) (𝓞 E ⧸ w.asIdeal))
          = ((primeUnder (𝓞 k) w).asIdeal.primesOver (𝓞 E)).ncard * Nat.card Gal(E/k) *
              Module.finrank (𝓞 k ⧸ (primeUnder (𝓞 k) w).asIdeal) (𝓞 E ⧸ w.asIdeal) := by
            ring
        _ = Nat.card Gal(E/k) := hkey
        _ = Nat.card Gal(E/k) * 1 := (mul_one _).symm
    have hprod := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hcard) h1
    exact ⟨Nat.dvd_one.mp ⟨_, hprod.symm⟩, Nat.dvd_one.mp ⟨_, by rw [← hprod]; ring⟩⟩
  refine ⟨fun w' hw' => ?_, ?_⟩
  · obtain ⟨P, hP⟩ := Set.ncard_eq_one.mp hone.1
    haveI : w'.asIdeal.IsPrime := w'.isPrime
    haveI : w'.asIdeal.LiesOver (primeUnder (𝓞 k) w).asIdeal := ⟨by rw [← hw']; rfl⟩
    have h1 : w.asIdeal ∈ (primeUnder (𝓞 k) w).asIdeal.primesOver (𝓞 E) :=
      ⟨inferInstance, inferInstance⟩
    have h2 : w'.asIdeal ∈ (primeUnder (𝓞 k) w).asIdeal.primesOver (𝓞 E) :=
      ⟨inferInstance, inferInstance⟩
    rw [hP] at h1 h2
    exact HeightOneSpectrum.ext (h2.trans h1.symm)
  · rw [Ideal.inertiaDeg_algebraMap]
    exact hone.2

end Unique

/-! ### Prescribing the values of a norm -/

section NormPrescribe

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- **Prescribed values of a norm.**  If each of the given places of the base has exactly one place
of the extension above it, of residue degree one, then the value of a norm at the place below is the
value of the element at the place above, and the values of an element at finitely many places may be
prescribed at will. -/
theorem exists_normUnit_placeValue_eq {S : Set (HeightOneSpectrum (𝓞 k))}
    {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hex : ∀ v ∈ S, ∃ W : HeightOneSpectrum (𝓞 K), W ∈ T ∧ primeUnder (𝓞 k) W = v ∧
      Ideal.inertiaDeg v.asIdeal W.asIdeal = 1 ∧
      ∀ W' : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) W' = v → W' = W)
    (n : HeightOneSpectrum (𝓞 k) → ℤ) :
    ∃ θ : Kˣ, ∀ v ∈ S, placeValue v (Units.map (Algebra.norm k : K →* k) θ) = n v := by
  obtain ⟨θ, hθ⟩ := exists_units_placeValue_eq T (fun W => n (primeUnder (𝓞 k) W))
  refine ⟨θ, fun v hv => ?_⟩
  obtain ⟨W, hWT, hWv, hWf, hWuniq⟩ := hex v hv
  rw [placeValue_normUnit v θ,
    finsum_eq_single _ W fun W' hW' => ?_, hWf, Nat.cast_one, one_mul, hθ W hWT, hWv]
  have hne : primeUnder (𝓞 k) W' ≠ v := fun hc => hW' (hWuniq W' hc)
  rw [inertiaDeg_eq_zero_of_comap_ne (fun hc => hne (HeightOneSpectrum.ext hc)), Nat.cast_zero,
    zero_mul]

end NormPrescribe

/-! ### Total ramification in the compositum -/

section Compositum

variable {q : ℕ} {k F₀ E : Type} [Field k] [NumberField k] [Field F₀] [NumberField F₀]
  [IsGalois ℚ F₀] [Field E] [NumberField E] [Algebra k E] [Algebra F₀ E] [IsScalarTower ℚ k E]
  [IsScalarTower ℚ F₀ E] [IsGalois k E]

/-- **A rational prime unramified in the base and totally ramified in a Galois extension of the
rationals is totally ramified in the compositum**, at every place of the compositum above it. -/
theorem inertia_eq_top_of_natCast_mem (hq : q.Prime) (hqk : q ∉ ramifiedSet k)
    (hinertia₀ : ∀ (Q : Ideal (𝓞 F₀)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q : ℤ)})),
      Ideal.inertia Gal(F₀/ℚ) Q = ⊤)
    (hgenE : Algebra.adjoin k (Set.range (algebraMap F₀ E)) = ⊤)
    (w : HeightOneSpectrum (𝓞 E)) (hmem : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal) :
    Ideal.inertia Gal(E/k) w.asIdeal = ⊤ := by
  have hmemk : ((q : ℕ) : 𝓞 k) ∈ (primeUnder (𝓞 k) w).asIdeal := by
    rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmem
  have hmemF : ((q : ℕ) : 𝓞 F₀) ∈ (primeUnder (𝓞 F₀) w).asIdeal := by
    rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmem
  haveI := liesOver_span_of_natCast_mem hq (primeUnder (𝓞 F₀) w) hmemF
  have hk : ramIdx (𝓞 ℚ) (primeUnder (𝓞 k) w) = 1 :=
    ramIdx_rat_eq_one_of_notMem_ramifiedSet hq hqk _ hmemk
  exact inertia_eq_top_of_inertia_base_eq_top hgenE w hk
    (hinertia₀ (primeUnder (𝓞 F₀) w).asIdeal (primeUnder (𝓞 F₀) w).isPrime inferInstance)

end Compositum

/-! ### Reduction to the algebraic integers which are units at the prime -/

section Reduce

/-- **Only finitely many places of a number field contain a given nonzero rational integer.** -/
theorem finite_places_natCast_mem {k : Type} [Field k] [NumberField k] {q : ℕ} (hq : q ≠ 0) :
    {v : HeightOneSpectrum (𝓞 k) | ((q : ℕ) : 𝓞 k) ∈ v.asIdeal}.Finite := by
  have hq0 : ((q : ℕ) : 𝓞 k) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hset : {v : HeightOneSpectrum (𝓞 k) | ((q : ℕ) : 𝓞 k) ∈ v.asIdeal}
      = {v : HeightOneSpectrum (𝓞 k) | v.asIdeal ∣ Ideal.span {((q : ℕ) : 𝓞 k)}} := by
    ext v
    simp [Ideal.dvd_span_singleton]
  rw [hset]
  exact Ideal.finite_factors (by simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hq0)

variable {k E : Type} [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
  [IsGalois k E]

/-- **A homomorphism to the Brauer group killing the norms from a Galois extension in which a prime
is totally ramified, and with trivial total invariant on the algebraic integers which are units at
that prime, has trivial total invariant on every unit.**  Adjusting by a norm makes an arbitrary
unit a unit at the prime, and such a unit is a quotient of algebraic integers which are units
there. -/
theorem totalInvariant_eq_one_of_integral_qunit {q : ℕ} (hq : q.Prime)
    (Y : kˣ →* BrauerGroup.{0, 0} k)
    (hker : ∀ θ : Eˣ, Y (Units.map (Algebra.norm k : E →* k) θ) = 1)
    (htot : ∀ W : HeightOneSpectrum (𝓞 E), ((q : ℕ) : 𝓞 E) ∈ W.asIdeal →
      Ideal.inertia Gal(E/k) W.asIdeal = ⊤)
    (hbase : ∀ a : kˣ, (∃ b : 𝓞 k, (a : k) = algebraMap (𝓞 k) k b) →
      (∀ v : HeightOneSpectrum (𝓞 k), ((q : ℕ) : 𝓞 k) ∈ v.asIdeal → placeValue v a = 0) →
      totalInvariant k (Y a) = 1) (a : kˣ) :
    totalInvariant k (Y a) = 1 := by
  classical
  have hSfin : {v : HeightOneSpectrum (𝓞 k) | ((q : ℕ) : 𝓞 k) ∈ v.asIdeal}.Finite :=
    finite_places_natCast_mem hq.ne_zero
  have hTfin : {W : HeightOneSpectrum (𝓞 E) | ((q : ℕ) : 𝓞 E) ∈ W.asIdeal}.Finite :=
    finite_places_natCast_mem hq.ne_zero
  have hex : ∀ v ∈ {v : HeightOneSpectrum (𝓞 k) | ((q : ℕ) : 𝓞 k) ∈ v.asIdeal},
      ∃ W : HeightOneSpectrum (𝓞 E), W ∈ hTfin.toFinset ∧ primeUnder (𝓞 k) W = v ∧
        Ideal.inertiaDeg v.asIdeal W.asIdeal = 1 ∧
        ∀ W' : HeightOneSpectrum (𝓞 E), primeUnder (𝓞 k) W' = v → W' = W := by
    intro v hv
    obtain ⟨W, hW⟩ := exists_primeUnder_eq (𝓞 k) (𝓞 E) v
    have hmemW : ((q : ℕ) : 𝓞 E) ∈ W.asIdeal := by
      have h1 : ((q : ℕ) : 𝓞 k) ∈ (primeUnder (𝓞 k) W).asIdeal := by
        rw [hW]
        exact hv
      rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
      exact h1
    obtain ⟨huniq, hf⟩ := unique_of_inertia_eq_top W (htot W hmemW)
    refine ⟨W, hTfin.mem_toFinset.mpr hmemW, hW, ?_, fun W' hW' => huniq W' (by rw [hW', hW])⟩
    rw [← hW]
    exact hf
  obtain ⟨θ, hθ⟩ := exists_normUnit_placeValue_eq (k := k) (K := E) hex fun v => placeValue v a
  set nθ : kˣ := Units.map (Algebra.norm k : E →* k) θ with hnθ
  have ha' : ∀ v ∈ {v : HeightOneSpectrum (𝓞 k) | ((q : ℕ) : 𝓞 k) ∈ v.asIdeal},
      placeValue v (a / nθ) = 0 := by
    intro v hv
    rw [placeValue_eq_placeOrd, Units.val_div_eq_div_val,
      placeOrd_div v (Units.ne_zero a) (Units.ne_zero nθ), ← placeValue_eq_placeOrd,
      ← placeValue_eq_placeOrd, hnθ, hθ v hv, sub_self]
  obtain ⟨b, c, habc, ⟨b', hb'⟩, ⟨c', hc'⟩, hb0, hc0⟩ :=
    exists_integral_div_of_forall_placeValue_eq_zero hSfin (a / nθ) ha'
  have hYa : Y a = Y (a / nθ) := by
    rw [map_div, hnθ, hker θ, div_one]
  rw [hYa, habc, map_div, map_div, hbase b ⟨b', hb'⟩ hb0, hbase c ⟨c', hc'⟩ hc0, div_one]

end Reduce

end InverseGalois.CFT
