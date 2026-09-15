/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.RealSymbolPositive
import InverseGalois.CFT.PoitouTate.FrobConjugate
import InverseGalois.CFT.PoitouTate.InertSquare
import InverseGalois.CFT.PoitouTate.OrdCompare

/-!
# The quadratic symbol at the conjugate of a place carrying a unit

Let a Galois extension of number fields carry an automorphism `σ` of order two, and let `B` be a
set of finite places containing the dyadic places and the places ramified over the base, stable
under the Galois group.  Consider a unit which is a local square at every place of `B`, whose order
is even at every place but one place `v` outside `B`, which is a local unit at `σ • v`, and which
every real embedding sends to a positive number.  Its value at the Frobenius automorphism of
`σ • v` is then trivial.

The proof is the product formula applied to the pair consisting of the difference of the unit and
its conjugate, and of the conjugate itself.  At a place of `B` the conjugate is a local square, so
the symbol is trivial there.  Away from `B` and away from the finitely many places where the
difference has odd order, both arguments have even order, so the symbol is trivial there too.  At
the remaining places the symbol is a value at a Frobenius automorphism, and the automorphism pairs
those places off: the value at a place and the value at its image agree, so the two contributions
cancel.  The places the automorphism fixes contribute nothing on their own, because there the unit
is congruent to the fixed element obtained by averaging it with its conjugate, and a fixed element
of even order at a place inert under the automorphism is a local square.  The archimedean symbols
vanish because the conjugate is again positive under every real embedding, so what survives is the
symbol at `σ • v`, which is the value in question.

## Main results

* `InverseGalois.CFT.exists_units_pow_of_localClassHom_eq_one`: a unit of trivial local class at a
  place is the power of a unit of the completion there.
* `InverseGalois.CFT.zpow_odd_eq_self`: an element killed by two is unchanged by an odd power.
* `InverseGalois.CFT.placeFrobValue_eq_one_of_isInvolution`: **the value at the Frobenius
  automorphism of the conjugate place is trivial**, for a totally positive unit ramified at a
  single place and a local square at the bad places.

## Tags

power residue symbol, Frobenius, involution, product formula, number field, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1600000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

/-! ### Two small facts -/

section Small

variable {K : Type} [Field K] [NumberField K]

/-- A unit of trivial local class at a place is the power of a unit of the completion there. -/
theorem exists_units_pow_of_localClassHom_eq_one {n : ℕ} {w : HeightOneSpectrum (𝓞 K)} {a : Kˣ}
    (h : localClassHom w n a = 1) :
    ∃ c : (w.adicCompletion K)ˣ,
      c ^ n = Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom a := by
  rw [localClassHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc⟩

end Small

section Odd

/-- An element killed by two is unchanged by an odd power. -/
theorem zpow_odd_eq_self {G : Type*} [Group G] {x : G} (hx : x ^ 2 = 1) {m : ℤ}
    (hm : ¬ (2 : ℤ) ∣ m) : x ^ m = x := by
  have hmod : m ≡ 1 [ZMOD ((2 : ℕ) : ℤ)] := by
    show m % ((2 : ℕ) : ℤ) = 1 % ((2 : ℕ) : ℤ)
    omega
  rw [zpow_eq_zpow_of_modEq hx hmod, zpow_one]

end Odd

/-! ### The claim -/

section Claim

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **The value at the Frobenius automorphism of the conjugate place is trivial**, for a unit of
positive order at the exceptional place. -/
private theorem placeFrobValue_eq_one_of_isInvolution_aux
    (hres : ∀ w : HeightOneSpectrum (𝓞 K), HasResidueChar (w.adicCompletion K) (P w) (E w))
    {ζ : K} (hζ : IsPrimitiveRoot ζ 2) {σ : Gal(K/k)} (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1)
    {B : Finset (HeightOneSpectrum (𝓞 K))}
    (hBstable : ∀ (τ : Gal(K/k)) (w : HeightOneSpectrum (𝓞 K)), w ∈ B → τ • w ∈ B)
    (hBwild : ∀ w : HeightOneSpectrum (𝓞 K), P w ∣ 2 → w ∈ B)
    (hBram : ∀ w : HeightOneSpectrum (𝓞 K), ramIdx (𝓞 k) w ≠ 1 → w ∈ B)
    {v : HeightOneSpectrum (𝓞 K)} (hvB : v ∉ B) {z : Kˣ}
    (hzB : ∀ w ∈ B, localClassHom w 2 z = 1)
    (hzeven : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v → (2 : ℤ) ∣ placeValue w z)
    (hzv : ¬ (2 : ℤ) ∣ placeValue v z) (hzσv : placeValue (σ • v) z = 0)
    (hzpos : ∀ φ : K →+* ℝ, 0 < φ (z : K)) (hzord : 0 < ord K v (z : K)) :
    placeFrobValue hres hζ (σ • v) z = 1 := by
  classical
  -- the automorphism is an involution, on elements and on places
  have hσapp : ∀ x : K, σ (σ x) = x := by
    intro x
    rw [← AlgEquiv.mul_apply, hσ2, AlgEquiv.one_apply]
  have hsmul2 : ∀ w : HeightOneSpectrum (𝓞 K), σ • (σ • w) = w := by
    intro w
    rw [← mul_smul, hσ2, one_smul]
  -- the places outside the bad set are tame and unramified, and stay outside
  have hPB : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ B → ¬ P w ∣ 2 := fun w hw h => hw (hBwild w h)
  have hramB : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ B → ramIdx (𝓞 k) w = 1 := by
    intro w hw
    by_contra h
    exact hw (hBram w h)
  have hBout : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ B → σ • w ∉ B := by
    intro w hw hc
    refine hw ?_
    have h := hBstable σ (σ • w) hc
    rwa [hsmul2 w] at h
  -- the conjugate unit
  obtain ⟨sz, hszdef⟩ : ∃ s : Kˣ, s = galUnits σ z := ⟨_, rfl⟩
  have hszcoe : (sz : K) = σ (z : K) := by rw [hszdef]; exact coe_galUnits_apply σ z
  have hσsz : σ (sz : K) = (z : K) := by rw [hszcoe, hσapp]
  have hordsmul : ∀ w : HeightOneSpectrum (𝓞 K), ord K w (sz : K) = ord K (σ • w) (z : K) := by
    intro w
    have h := ord_galUnits σ (σ • w) z
    rw [hsmul2 w] at h
    rw [hszdef]
    exact h
  have hpvsmul : ∀ w : HeightOneSpectrum (𝓞 K), placeValue w sz = placeValue (σ • w) z := by
    intro w
    have h := placeValue_galSmul (σ • w) σ z
    rw [hsmul2 w] at h
    rw [hszdef]
    exact h
  have hclasssmul : ∀ w : HeightOneSpectrum (𝓞 K),
      (localClassHom w 2 sz = 1 ↔ localClassHom (σ • w) 2 z = 1) := by
    intro w
    have h := localClassHom_galUnits_eq_one_iff σ (σ • w) 2 z
    rw [hsmul2 w] at h
    rw [hszdef]
    exact h
  -- the order table at the exceptional place and its image
  have hpvz : ∀ w : HeightOneSpectrum (𝓞 K), placeValue w z = -ord K w (z : K) :=
    fun w => placeValue_eq_neg_ord w z
  have hordσv_z : ord K (σ • v) (z : K) = 0 := by
    have h := hzσv
    rw [hpvz (σ • v)] at h
    omega
  have hordv_sz : ord K v (sz : K) = 0 := by rw [hordsmul v, hordσv_z]
  have hordσv_sz : ord K (σ • v) (sz : K) = ord K v (z : K) := by
    rw [hordsmul (σ • v), hsmul2 v]
  have hDne : (z : K) - (sz : K) ≠ 0 := by
    refine sub_ne_zero.2 fun h => ?_
    rw [h, hordv_sz] at hzord
    exact lt_irrefl 0 hzord
  obtain ⟨d, hdcoe⟩ : ∃ a : Kˣ, (a : K) = (z : K) - (sz : K) := ⟨Units.mk0 _ hDne, rfl⟩
  have hpvd : ∀ w : HeightOneSpectrum (𝓞 K),
      placeValue w d = -ord K w ((z : K) - (sz : K)) := by
    intro w
    rw [placeValue_eq_neg_ord, hdcoe]
  have hordv_d : ord K v ((z : K) - (sz : K)) = 0 := by
    have hlt : ord K v (sz : K) < ord K v (z : K) := by rw [hordv_sz]; exact hzord
    rw [ord_sub_eq_right v sz.ne_zero hlt, hordv_sz]
  have hordσv_d : ord K (σ • v) ((z : K) - (sz : K)) = 0 := by
    have hlt : ord K (σ • v) (z : K) < ord K (σ • v) (sz : K) := by
      rw [hordσv_z, hordσv_sz]; exact hzord
    rw [ord_sub_of_ord_lt z.ne_zero hlt, hordσv_z]
  have hd_smul : ∀ w : HeightOneSpectrum (𝓞 K),
      ord K (σ • w) ((z : K) - (sz : K)) = ord K w ((z : K) - (sz : K)) := by
    intro w
    have h := ord_galSmul σ w ((z : K) - (sz : K))
    rw [_root_.map_sub, hσsz, ← hszcoe,
      show (sz : K) - (z : K) = -((z : K) - (sz : K)) by ring, ord_neg] at h
    exact h
  -- the finite set of places where the difference has odd order
  have hfin : {w : HeightOneSpectrum (𝓞 K) | ¬ (ord K w ((z : K) - (sz : K)) = 0)}.Finite :=
    Filter.eventually_cofinite.1 (ord_finite (R := 𝓞 K) (K := K) ((z : K) - (sz : K)))
  set Λ : Finset (HeightOneSpectrum (𝓞 K)) :=
    hfin.toFinset.filter (fun w => w ∉ B ∧ ¬ (2 : ℤ) ∣ placeValue w d) with hΛdef
  have hmemΛ : ∀ w : HeightOneSpectrum (𝓞 K),
      (w ∈ Λ ↔ (w ∉ B ∧ ¬ (2 : ℤ) ∣ placeValue w d)) := by
    intro w
    rw [hΛdef, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    intro hz0
    exact h.2 ⟨0, by rw [hpvd w, hz0]; ring⟩
  have hΛB : ∀ w ∈ Λ, w ∉ B := fun w hw => ((hmemΛ w).1 hw).1
  have hΛodd : ∀ w ∈ Λ, ¬ (2 : ℤ) ∣ placeValue w d := fun w hw => ((hmemΛ w).1 hw).2
  have hΛsmul : ∀ w ∈ Λ, σ • w ∈ Λ := by
    intro w hw
    refine (hmemΛ _).2 ⟨hBout w (hΛB w hw), ?_⟩
    rw [hpvd, hd_smul w, ← hpvd w]
    exact hΛodd w hw
  have hvΛ : v ∉ Λ := fun hv => hΛodd v hv ⟨0, by rw [hpvd v, hordv_d]; ring⟩
  have hσvΛ : σ • v ∉ Λ := fun hv => hΛodd _ hv ⟨0, by rw [hpvd (σ • v), hordσv_d]; ring⟩
  have hΛne : ∀ w ∈ Λ, w ≠ v ∧ σ • w ≠ v := by
    intro w hw
    refine ⟨fun h => hvΛ (h ▸ hw), fun h => ?_⟩
    refine hσvΛ ?_
    rw [← h, hsmul2 w]
    exact hw
  -- at a place of odd difference the unit and its conjugate have the same order
  have hΛord : ∀ w ∈ Λ, ord K w (z : K) = ord K w (sz : K) ∧
      ord K w (sz : K) < ord K w ((z : K) - (sz : K)) := by
    intro w hw
    have hα : (2 : ℤ) ∣ ord K w (z : K) := by
      have h := hzeven w (hΛne w hw).1
      rw [hpvz w] at h
      exact dvd_neg.1 h
    have hβ : (2 : ℤ) ∣ ord K w (sz : K) := by
      have h := hzeven (σ • w) (hΛne w hw).2
      rw [hpvz (σ • w), ← hordsmul w] at h
      exact dvd_neg.1 h
    have hδ : ¬ (2 : ℤ) ∣ ord K w ((z : K) - (sz : K)) := by
      intro h
      refine hΛodd w hw ?_
      rw [hpvd w]
      exact dvd_neg.2 h
    have heq : ord K w (z : K) = ord K w (sz : K) := by
      by_contra hcon
      rcases lt_or_gt_of_ne hcon with h | h
      · exact hδ (by rw [ord_sub_of_ord_lt z.ne_zero h]; exact hα)
      · exact hδ (by rw [ord_sub_eq_right w sz.ne_zero h]; exact hβ)
    refine ⟨heq, ?_⟩
    have hmin := min_ord_le_ord_sub (v := w) (x := (z : K)) (y := (sz : K)) hDne
    rw [heq, min_self] at hmin
    rcases eq_or_lt_of_le hmin with h | h
    · exact absurd (h ▸ hβ) hδ
    · exact h
  have hΛclass : ∀ w ∈ Λ, localClassHom w 2 z = localClassHom w 2 sz := by
    intro w hw
    refine localClassHom_eq_of_valuation_sub_lt (hres w) (hPB w (hΛB w hw)) ?_
    exact (valuation_lt_iff_ord_lt w hDne sz.ne_zero).2 (hΛord w hw).2
  have hΛfrobz : ∀ w ∈ Λ,
      placeFrobValue hres hζ w z = placeFrobValue hres hζ w sz := fun w hw =>
    placeFrobValue_eq_of_localClassHom_eq hres hζ w (hΛclass w hw)
  have hΛeven : ∀ w ∈ Λ, (2 : ℤ) ∣ placeValue w z := fun w hw => hzeven w (hΛne w hw).1
  have hΛconj : ∀ w ∈ Λ,
      placeFrobValue hres hζ (σ • w) z = placeFrobValue hres hζ w z := by
    intro w hw
    have h1 := hΛfrobz (σ • w) (hΛsmul w hw)
    have h2 : placeFrobValue hres hζ (σ • w) sz = placeFrobValue hres hζ w z := by
      rw [hszdef]
      exact placeFrobValue_galUnits hres hζ σ (hPB w (hΛB w hw))
        (hPB (σ • w) (hΛB (σ • w) (hΛsmul w hw))) (hΛeven w hw)
    rw [h1, h2]
  -- two is a unit away from the dyadic places
  have hord2 : ∀ w : HeightOneSpectrum (𝓞 K), ¬ P w ∣ 2 → ord K w (2 : K) = 0 := by
    intro w hw
    have hmem := two_notMem_asIdeal (hres w) hw
    have h2ne : ((2 : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 (by norm_num)
    have hnotpos : ¬ (0 < ord K w (algebraMap (𝓞 K) K ((2 : ℕ) : 𝓞 K))) := fun h =>
      hmem ((mem_iff_ord_pos (K := K) w h2ne).2 h)
    have hnn := ord_nonneg (K := K) w ((2 : ℕ) : 𝓞 K)
    have hzero : ord K w (algebraMap (𝓞 K) K ((2 : ℕ) : 𝓞 K)) = 0 := by omega
    rw [_root_.map_natCast] at hzero
    simpa using hzero
  -- at a place the automorphism fixes the unit is a local square
  have hΛfixed : ∀ w ∈ Λ, σ • w = w → placeFrobValue hres hζ w z = 1 := by
    intro w hw hfix
    have hwB := hΛB w hw
    have heqo := (hΛord w hw).1
    have hlt := (hΛord w hw).2
    have h2K : (2 : K) ≠ 0 := by norm_num
    have hsum : (z : K) + (sz : K) ≠ 0 := by
      intro h
      have hd2 : (z : K) - (sz : K) = 2 * (z : K) := by linear_combination -h
      have hcon := hlt
      rw [hd2, ord_mul w h2K z.ne_zero, hord2 w (hPB w hwB), zero_add, heqo] at hcon
      exact lt_irrefl _ hcon
    obtain ⟨A, hAcoe⟩ : ∃ a : Kˣ, (a : K) = ((z : K) + (sz : K)) / 2 :=
      ⟨Units.mk0 _ (div_ne_zero hsum h2K), rfl⟩
    have hAgal : galUnits σ A = A := by
      refine Units.ext ?_
      rw [coe_galUnits_apply, hAcoe, _root_.map_div₀, _root_.map_add, hσsz, ← hszcoe,
        _root_.map_ofNat]
      ring
    have hord2z : ord K w (2 * (z : K)) = ord K w (z : K) := by
      rw [ord_mul w h2K z.ne_zero, hord2 w (hPB w hwB), zero_add]
    have hordA : ord K w (A : K) = ord K w (z : K) := by
      have hlt' : ord K w (2 * (z : K)) < ord K w ((z : K) - (sz : K)) := by
        rw [hord2z, heqo]; exact hlt
      have hsumord : ord K w ((z : K) + (sz : K)) = ord K w (z : K) := by
        rw [show (z : K) + (sz : K) = 2 * (z : K) - ((z : K) - (sz : K)) by ring,
          ord_sub_of_ord_lt (mul_ne_zero h2K z.ne_zero) hlt', hord2z]
      rw [hAcoe, ord_div w hsum h2K, hsumord, hord2 w (hPB w hwB), sub_zero]
    have hsubA : (z : K) - (A : K) = ((z : K) - (sz : K)) / 2 := by rw [hAcoe]; ring
    have hordsubA : ord K w ((z : K) - (A : K)) = ord K w ((z : K) - (sz : K)) := by
      rw [hsubA, ord_div w hDne h2K, hord2 w (hPB w hwB), sub_zero]
    have hAclass : localClassHom w 2 z = localClassHom w 2 A := by
      refine localClassHom_eq_of_valuation_sub_lt (hres w) (hPB w hwB) ?_
      refine (valuation_lt_iff_ord_lt w ?_ A.ne_zero).2 ?_
      · rw [hsubA]
        exact div_ne_zero hDne h2K
      · rw [hordsubA, hordA, heqo]
        exact hlt
    have hAeven : (2 : ℤ) ∣ placeValue w A := by
      rw [placeValue_eq_neg_ord, hordA, ← placeValue_eq_neg_ord]
      exact hΛeven w hw
    have hAone : localClassHom w 2 A = 1 :=
      localClassHom_two_eq_one_of_galUnits_eq (hres w) (hPB w hwB) hσ1 hσ2 hfix (hramB w hwB)
        hAgal hAeven
    rw [placeFrobValue_eq_one_iff_localClassHom_eq_one Nat.prime_two hres hζ (hPB w hwB)
      (hΛeven w hw), hAclass, hAone]
  -- the values at the places of odd difference cancel in pairs
  have hΛprod : (∏ w ∈ Λ, placeFrobValue hres hζ w z) = 1 := by
    refine Finset.prod_involution (fun w _ => σ • w) (fun w hw => ?_) (fun w hw hne => ?_)
      (fun w hw => hΛsmul w hw) (fun w _ => hsmul2 w)
    · rw [hΛconj w hw, ← pow_two]
      exact pow_placeFrobValue_eq_one hres hζ w z
    · intro hfix
      exact hne (hΛfixed w hw hfix)
  have hfw : ∀ w ∈ Λ,
      localSymbol (hres w) (isUnitValGen_one (valued_adicCompletion_surjective w))
          (hζ.map_of_injective (algebraMap K (w.adicCompletion K)).injective)
          (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom d)
          (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom sz)
        = placeFrobValue hres hζ w z := by
    intro w hw
    have hszeven : (2 : ℤ) ∣ placeValue w sz := by
      rw [hpvsmul w]
      exact hzeven (σ • w) (hΛne w hw).2
    rw [localSymbol_eq_placeFrobValue_zpow_right Nat.prime_two hres hζ (hPB w (hΛB w hw))
        hszeven d,
      zpow_odd_eq_self (pow_placeFrobValue_eq_one hres hζ w sz) (hΛodd w hw), ← hΛfrobz w hw]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_two]
    exact pow_placeFrobValue_eq_one hres hζ w z
  have hΛsym : (∏ w ∈ Λ,
      localSymbol (hres w) (isUnitValGen_one (valued_adicCompletion_surjective w))
        (hζ.map_of_injective (algebraMap K (w.adicCompletion K)).injective)
        (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom d)
        (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom sz)) = 1 :=
    (Finset.prod_congr rfl hfw).trans hΛprod
  -- the symbol at the image of the exceptional place is the value in question
  have hPσv : ¬ P (σ • v) ∣ 2 := hPB (σ • v) (hBout v hvB)
  have hfv : localSymbol (hres (σ • v)) (isUnitValGen_one (valued_adicCompletion_surjective _))
        (hζ.map_of_injective (algebraMap K ((σ • v).adicCompletion K)).injective)
        (Units.map (algebraMap K ((σ • v).adicCompletion K)).toMonoidHom d)
        (Units.map (algebraMap K ((σ • v).adicCompletion K)).toMonoidHom sz)
      = placeFrobValue hres hζ (σ • v) z := by
    have hdv : (2 : ℤ) ∣ placeValue (σ • v) d := ⟨0, by rw [hpvd (σ • v), hordσv_d]; ring⟩
    have hoddexp : ¬ (2 : ℤ) ∣ placeValue (σ • v) sz := by
      rw [hpvsmul (σ • v), hsmul2 v]
      exact hzv
    rw [localSymbol_eq_placeFrobValue_zpow Nat.prime_two hres hζ hPσv hdv sz,
      zpow_odd_eq_self (pow_placeFrobValue_eq_one hres hζ (σ • v) d) hoddexp]
    refine placeFrobValue_eq_of_localClassHom_eq hres hζ (σ • v) ?_
    refine localClassHom_eq_of_valuation_sub_lt (hres (σ • v)) hPσv ?_
    have hdz : (d : K) - (z : K) = -(sz : K) := by rw [hdcoe]; ring
    refine (valuation_lt_iff_ord_lt (σ • v) ?_ z.ne_zero).2 ?_
    · rw [hdz]
      exact neg_ne_zero.2 sz.ne_zero
    · rw [hdz, ord_neg, hordσv_sz, hordσv_z]
      exact hzord
  -- everywhere else the symbol is trivial
  have hS : ∀ w ∉ insert (σ • v) Λ,
      localSymbol (hres w) (isUnitValGen_one (valued_adicCompletion_surjective w))
        (hζ.map_of_injective (algebraMap K (w.adicCompletion K)).injective)
        (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom d)
        (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom sz) = 1 := by
    intro w hw
    rw [Finset.mem_insert] at hw
    push_neg at hw
    obtain ⟨hw1, hw2⟩ := hw
    by_cases hwB : w ∈ B
    · exact localSymbol_eq_one_of_isPow_right _ _ _ _
        (exists_units_pow_of_localClassHom_eq_one
          ((hclasssmul w).2 (hzB (σ • w) (hBstable σ w hwB))))
    · have h1 : (2 : ℤ) ∣ placeValue w d := by
        by_contra hc
        exact hw2 ((hmemΛ w).2 ⟨hwB, hc⟩)
      have h2 : (2 : ℤ) ∣ placeValue w sz := by
        rw [hpvsmul w]
        refine hzeven (σ • w) fun h => hw1 ?_
        rw [← h, hsmul2 w]
      exact localSymbol_eq_one_of_dvd_of_dvd _ _ _ Nat.prime_two (hPB w hwB) h1 h2
  -- the conjugate is again positive under every real embedding
  have hszpos : ∀ φ : K →+* ℝ, 0 < φ (sz : K) := by
    intro φ
    rw [hszcoe]
    exact forall_pos_map σ hzpos φ
  have hprod := prod_localSymbol_mul_prod_archSymbol_eq_one (n := 2) Nat.prime_two hres hζ d sz
    (insert (σ • v) Λ) hS
  rw [Finset.prod_insert hσvΛ, hfv, hΛsym, mul_one,
    prod_archSymbol_eq_one_of_forall_pos d sz hszpos, mul_one] at hprod
  exact hprod

/-- **The value at the Frobenius automorphism of the conjugate place is trivial.**  Let an
automorphism of order two of a Galois extension of number fields be given, together with a set `B`
of finite places stable under the Galois group and containing the dyadic places and the places
ramified over the base.  A unit which is a local square at every place of `B`, whose order is even
away from a single place `v` outside `B`, which is a local unit at the image of `v`, and which is
positive under every real embedding, has trivial value at the Frobenius automorphism of that
image. -/
theorem placeFrobValue_eq_one_of_isInvolution
    (hres : ∀ w : HeightOneSpectrum (𝓞 K), HasResidueChar (w.adicCompletion K) (P w) (E w))
    {ζ : K} (hζ : IsPrimitiveRoot ζ 2) {σ : Gal(K/k)} (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1)
    {B : Finset (HeightOneSpectrum (𝓞 K))}
    (hBstable : ∀ (τ : Gal(K/k)) (w : HeightOneSpectrum (𝓞 K)), w ∈ B → τ • w ∈ B)
    (hBwild : ∀ w : HeightOneSpectrum (𝓞 K), P w ∣ 2 → w ∈ B)
    (hBram : ∀ w : HeightOneSpectrum (𝓞 K), ramIdx (𝓞 k) w ≠ 1 → w ∈ B)
    {v : HeightOneSpectrum (𝓞 K)} (hvB : v ∉ B) {z : Kˣ}
    (hzB : ∀ w ∈ B, localClassHom w 2 z = 1)
    (hzeven : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v → (2 : ℤ) ∣ placeValue w z)
    (hzv : ¬ (2 : ℤ) ∣ placeValue v z) (hzσv : placeValue (σ • v) z = 0)
    (hzpos : ∀ φ : K →+* ℝ, 0 < φ (z : K)) :
    placeFrobValue hres hζ (σ • v) z = 1 := by
  have hpvinv : ∀ w : HeightOneSpectrum (𝓞 K), placeValue w z⁻¹ = -placeValue w z := by
    intro w
    rw [placeValue_eq_neg_ord, placeValue_eq_neg_ord, Units.val_inv_eq_inv_val, ord_inv]
  have hordne : ord K v (z : K) ≠ 0 := by
    intro h
    exact hzv ⟨0, by rw [placeValue_eq_neg_ord, h]; ring⟩
  rcases lt_or_gt_of_ne hordne with hneg | hpos
  · have h := placeFrobValue_eq_one_of_isInvolution_aux (z := z⁻¹) hres hζ hσ1 hσ2 hBstable
      hBwild hBram hvB
      (fun w hw => by rw [_root_.map_inv, hzB w hw, inv_one])
      (fun w hw => by rw [hpvinv w]; exact dvd_neg.2 (hzeven w hw))
      (by rw [hpvinv v]; exact fun hc => hzv (dvd_neg.1 hc))
      (by rw [hpvinv (σ • v), hzσv, neg_zero])
      (fun φ => by rw [Units.val_inv_eq_inv_val, map_inv₀]; exact inv_pos.2 (hzpos φ))
      (by rw [Units.val_inv_eq_inv_val, ord_inv]; omega)
    rw [placeFrobValue_inv] at h
    exact inv_eq_one.1 h
  · exact placeFrobValue_eq_one_of_isInvolution_aux hres hζ hσ1 hσ2 hBstable hBwild hBram hvB
      hzB hzeven hzv hzσv hzpos hpos

end Claim

end InverseGalois.CFT
