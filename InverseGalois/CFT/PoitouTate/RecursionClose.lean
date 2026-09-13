/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ClosingChain
import InverseGalois.CFT.PoitouTate.ClosingChainRamified
import InverseGalois.CFT.PoitouTate.Recursion

/-!
# Closing the recursion: two places and one unit ramified at both

The recursion which adds one place at a time produces, at every stage, a list of places and a list
of units, each ramified at exactly one of the places, whose Galois conjugates cancel each other at
all the nontrivial conjugates of the earlier places.  Two invariants of such a unit are killed by
the exponent: its value at the Frobenius automorphism of its own place, moved by any automorphism
of the extension, and its value at its own place read modulo the exponent.  Both range over finite
sets, so the recursion may be run for a number of stages exceeding the size of that finite set and
two of the stages must agree.  The product of the two units attached to those stages is then
trivial at every nontrivial conjugate of both places, and is ramified exactly at the two places
themselves.

The bound on the number of stages is what makes this usable: it is read off before the recursion
is started, so the whole argument takes place inside a single stage of the recursion and no
coherence between the successive stages has to be arranged.

The prescription may be ramified on a distinguished stable part of the fixed set, provided it is
supported at no more than one place of each orbit of that part.  Then the two units are ramified
there too, and the two applications of the reciprocity law which close the chain absorb those
places because the classes they compare lie on one line.

## Main results

* `InverseGalois.CFT.exists_bound_placeFrobValue_eq`: **a bounded pigeonhole principle** for a
  sequence of places and a sequence of units.
* `InverseGalois.CFT.exists_pow_eq_of_localClassHom_eq_one`: a unit whose local class is trivial is
  a power in the completion.
* `InverseGalois.CFT.exists_prescribed_two_places`: **two completely split places and a unit
  realising a prescribed local behaviour, ramified exactly at those two places and trivial at all
  their nontrivial conjugates.**

## Tags

number field, place, local class, pigeonhole, Frobenius, prescription, recursion
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### A bounded pigeonhole principle -/

section Pigeonhole

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
  {p : ℕ} [NeZero p] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **A bounded pigeonhole principle for a sequence of units and a sequence of places**: there is a
bound, depending on neither sequence, below which two members of the sequence already have the same
value at the Frobenius automorphism of their own place moved by any automorphism, and the same
value at their own place modulo the exponent. -/
theorem exists_bound_placeFrobValue_eq
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    ∃ M : ℕ, ∀ (Pl : ℕ → HeightOneSpectrum (𝓞 K)) (z : ℕ → Kˣ),
      ∃ i N : ℕ, i < N ∧ N < M ∧
        placeValue (Pl N) (z N) ≡ placeValue (Pl i) (z i) [ZMOD (p : ℤ)] ∧
        ∀ σ : Gal(K/k),
          placeFrobValue hres hζ (σ • Pl N) (z N) = placeFrobValue hres hζ (σ • Pl i) (z i) := by
  classical
  have hfin : ((Set.univ.pi fun _ : Gal(K/k) => {x : Multiplicative QModZ | x ^ p = 1}) ×ˢ
      (Set.univ : Set (ZMod p))).Finite :=
    (Set.Finite.pi fun _ => finite_setOf_pow_eq_one p).prod Set.finite_univ
  refine ⟨hfin.toFinset.card + 1, fun Pl z => ?_⟩
  have hmaps : ∀ i ∈ Finset.range (hfin.toFinset.card + 1),
      ((fun σ : Gal(K/k) => placeFrobValue hres hζ (σ • Pl i) (z i)),
        ((placeValue (Pl i) (z i) : ℤ) : ZMod p)) ∈ hfin.toFinset :=
    fun i _ => hfin.mem_toFinset.2
      ⟨fun _ _ => pow_placeFrobValue_eq_one hres hζ _ _, Set.mem_univ _⟩
  have hcard : hfin.toFinset.card < (Finset.range (hfin.toFinset.card + 1)).card := by
    rw [Finset.card_range]
    omega
  obtain ⟨i, hi, j, hj, hij, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun i : ℕ => ((fun σ : Gal(K/k) => placeFrobValue hres hζ (σ • Pl i) (z i)),
        ((placeValue (Pl i) (z i) : ℤ) : ZMod p))) hmaps
  have hval : placeValue (Pl i) (z i) ≡ placeValue (Pl j) (z j) [ZMOD (p : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff _ _ _).1 (congrArg Prod.snd hfeq)
  have hfrob := congrArg Prod.fst hfeq
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, Finset.mem_range.1 hj, hval.symm, fun σ => congrFun hfrob.symm σ⟩
  · exact ⟨j, i, h, Finset.mem_range.1 hi, hval, fun σ => congrFun hfrob σ⟩

end Pigeonhole

/-! ### A trivial local class is a local power -/

section Power

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/-- A unit of a number field whose class at a finite place is trivial is an `n`-th power in the
completion at that place. -/
theorem exists_pow_eq_of_localClassHom_eq_one {v : HeightOneSpectrum (𝓞 K)} {a : Kˣ}
    (h : localClassHom v n a = 1) :
    ∃ c : (v.adicCompletion K)ˣ,
      c ^ n = Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a := by
  have h' : Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a ∈
      (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range :=
    (QuotientGroup.eq_one_iff _).1 h
  obtain ⟨c, hc⟩ := h'
  exact ⟨c, hc⟩

end Power

/-! ### Two places, and a unit ramified exactly at both -/

section Close

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
  {p : ℕ} [NeZero p] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **Two completely split places and a unit ramified exactly at those two places**, realising the
square of a prescribed local behaviour on a fixed Galois stable set of places containing all the
places above the exponent, and trivial at every nontrivial conjugate of the two places.  The
recursion starts from a possibly larger Galois stable set, all of whose further places already
satisfy the splitting condition; the two places are produced by running it past the bound supplied
by the pigeonhole principle, and the unit is the product of the two units attached to the two
agreeing stages.  Away from a distinguished stable part of the fixed set, where the prescription
lies on one line with the prescription carried there from the place below, the unit produced is
unramified. -/
theorem exists_prescribed_two_places (hp : p.Prime) (hp2 : p ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {Spl : HeightOneSpectrum (𝓞 K) → Prop}
    (hSpl : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), Spl v → Spl (σ • v))
    {Tr T S₀ : Finset (HeightOneSpectrum (𝓞 K))}
    (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
    (hTrT : Tr ⊆ T)
    (hTrstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tr → σ • v ∈ Tr)
    (hTS : T ⊆ S₀)
    (hSstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S₀ → σ • v ∈ S₀)
    (hSsplit : ∀ v ∈ S₀, v ∉ T → Spl v)
    (hpT : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ T)
    {g : Kˣ} (hgunr : ∀ v ∈ T, v ∉ Tr → localClassHom v p g ∈ localUnramified v p)
    (hgline : ∀ σ : Gal(K/k), σ ≠ 1 → ∀ v ∈ Tr,
      OnOneLineGal (fun w => localClassHom w p g) σ v)
    (hgp : ∀ v ∈ T, Pc v ∣ p → localClassHom v p g = 1)
    (hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S →
      (∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S → σ • v ∈ S) →
      ∀ c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p,
        (∀ v ∈ S, v ∉ Tr → c v ∈ localUnramified v p) →
        (∀ v ∈ T, c v = localClassHom v p g) →
        (∀ v ∈ S, v ∉ T → Spl v) →
        ∃ Q : HeightOneSpectrum (𝓞 K), Q ∉ S ∧ Spl Q ∧ stabilizer Gal(K/k) Q = ⊥ ∧
          ∃ w : Kˣ, (∀ v ∈ S, localClassHom v p w = c v) ∧
            (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Tr → v ≠ Q → (p : ℤ) ∣ placeValue v w) ∧
            ¬ (p : ℤ) ∣ placeValue Q w) :
    ∃ Q R : HeightOneSpectrum (𝓞 K), Q ∉ T ∧ R ∉ T ∧ Spl Q ∧ Spl R ∧
      (∀ σ : Gal(K/k), Q ≠ σ • R) ∧
      stabilizer Gal(K/k) Q = ⊥ ∧ stabilizer Gal(K/k) R = ⊥ ∧
      ∃ z : Kˣ, (∀ v ∈ T, localClassHom v p z = localClassHom v p (g ^ 2)) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Tr → v ≠ Q → v ≠ R → (p : ℤ) ∣ placeValue v z) ∧
        ¬ (p : ℤ) ∣ placeValue Q z ∧ ¬ (p : ℤ) ∣ placeValue R z ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • Q) p z = 1) ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • R) p z = 1) := by
  obtain ⟨M, hM⟩ := exists_bound_placeFrobValue_eq (k := k) hres hζ
  obtain ⟨d, hd⟩ := exists_recInv hSpl hTrT hTS hSstable hSsplit hgunr hstep M
  obtain ⟨i, N, hiN, hNM, hvalcong, hfrobeq⟩ := hM d.chosen d.unit
  have hiM : i < M := hiN.trans hNM
  -- a place outside the fixed set has residue characteristic prime to the exponent
  have hnotT : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → ¬ Pc v ∣ p := fun v hv =>
    not_dvd_of_finitePlace_natCast_eq_one (hres v) (by
      by_contra hne
      exact hv (hpT v hne))
  have hTnot : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∉ T → σ • v ∉ T :=
    fun σ v hv hmem => by
      have h := hTstable σ⁻¹ _ hmem
      rw [inv_smul_smul] at h
      exact hv h
  have hnotTr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v ∉ Tr := fun v hv hmem => hv (hTrT hmem)
  have hQnotT : d.chosen i ∉ T := hd.chosenNotMem i hiM
  have hRnotT : d.chosen N ∉ T := hd.chosenNotMem N hNM
  have hQR : ∀ σ : Gal(K/k), d.chosen i ≠ σ • d.chosen N :=
    hd.chosenNe i hiM N hNM hiN.ne
  have hQRne : d.chosen i ≠ d.chosen N := by
    have h := hQR 1
    rwa [one_smul] at h
  -- the hypotheses of the closing chain
  have hQσQ : ∀ σ : Gal(K/k), σ ≠ 1 → d.chosen i ≠ σ • d.chosen i := fun σ hσ hfix =>
    hσ ((Subgroup.eq_bot_iff_forall _).1 (hd.chosenStab i hiM) σ
      (mem_stabilizer_iff.2 hfix.symm))
  have hRσR : ∀ σ : Gal(K/k), σ ≠ 1 → d.chosen N ≠ σ • d.chosen N := fun σ hσ hfix =>
    hσ ((Subgroup.eq_bot_iff_forall _).1 (hd.chosenStab N hNM) σ
      (mem_stabilizer_iff.2 hfix.symm))
  have hziQ : IsCoprime (placeValue (d.chosen i) (d.unit i)) (p : ℤ) :=
    (((Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd).2 (hd.unitRam i hiM)).symm
  have hzip : ∀ u : HeightOneSpectrum (𝓞 K), Pc u ∣ p →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ p = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom (d.unit i) := by
    intro u hu
    have huT : u ∈ T := by
      by_contra huT
      exact hnotT u huT hu
    exact exists_pow_eq_of_localClassHom_eq_one
      ((hd.unitPres i hiM u huT).trans (hgp u huT hu))
  have hcond : ∀ σ : Gal(K/k), σ ≠ 1 →
      placeFrobValue hres hζ (d.chosen i) (galUnits σ (d.unit N))
        = (placeFrobValue hres hζ (d.chosen i) (galUnits σ (d.unit i)))⁻¹ := by
    intro σ hσ
    have h := placeFrobValue_galUnits_eq_inv hres hζ σ (σ⁻¹ • d.chosen i)
      (hd.unitConj i hiM N hNM hiN σ⁻¹ (inv_ne_one.2 hσ))
    rwa [smul_inv_smul] at h
  -- on the distinguished part the classes compared by the closing chain lie on one line
  have hiso : ∀ σ : Gal(K/k), ∀ u ∈ Tr, ∃ e : localClasses u p,
      localClassHom u p (d.unit i) ∈ Subgroup.zpowers e ∧
      localClassHom u p (galUnits σ (d.unit i)) ∈ Subgroup.zpowers e ∧
      localClassHom u p (galUnits σ (d.unit N)) ∈ Subgroup.zpowers e := fun σ =>
    exists_zpowers_of_prescription (T := Tr) (cT := fun v => localClassHom v p g) hTrstable σ
      (hgline σ) (fun v hv => hd.unitPres i hiM v (hTrT hv))
      (fun v hv => hd.unitPres N hNM v (hTrT hv))
  -- the two places and the unit
  refine ⟨d.chosen i, d.chosen N, hQnotT, hRnotT, hd.split _ (hd.chosenMem i hiM) hQnotT,
    hd.split _ (hd.chosenMem N hNM) hRnotT, hQR, hd.chosenStab i hiM, hd.chosenStab N hNM,
    d.unit i * d.unit N, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [_root_.map_mul, hd.unitPres i hiM v hv, hd.unitPres N hNM v hv, _root_.map_pow, pow_two]
  · intro v hvTr hvQ hvR
    rw [placeValue_mul]
    exact dvd_add (hd.unitUnram i hiM v hvTr hvQ) (hd.unitUnram N hNM v hvTr hvR)
  · intro hdvd
    refine hd.unitRam i hiM ?_
    have h := dvd_sub hdvd (hd.unitUnram N hNM _ (hnotTr _ hQnotT) hQRne)
    rwa [placeValue_mul, add_sub_cancel_right] at h
  · intro hdvd
    refine hd.unitRam N hNM ?_
    have h := dvd_sub hdvd (hd.unitUnram i hiM _ (hnotTr _ hRnotT) (Ne.symm hQRne))
    rwa [placeValue_mul, add_sub_cancel_left] at h
  · intro σ hσ
    rw [_root_.map_mul, hd.unitConj i hiM N hNM hiN σ hσ, mul_inv_cancel]
  · intro σ hσ
    exact localClassHom_mul_eq_one_of_isotropic hp hp2 hres hζ hTrstable (hQσQ σ hσ) (hQR σ)
      (hRσR σ hσ) (hnotTr _ hQnotT) (hnotTr _ hRnotT) (hnotT _ hQnotT)
      (hnotT _ (hTnot σ _ hQnotT)) (hnotT _ (hTnot σ _ hRnotT))
      (hd.unitUnram i hiM) (hd.unitUnram N hNM) hziQ hvalcong hzip (hiso σ) (hfrobeq σ)
      (hcond σ hσ)

end Close

end InverseGalois.CFT
