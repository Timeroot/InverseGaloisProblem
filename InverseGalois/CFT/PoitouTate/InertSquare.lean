/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.BaseRamification
import InverseGalois.CFT.Local.FixedSquare
import InverseGalois.CFT.PoitouTate.LocalClassClose

/-!
# Squares at a place inert under an involution

Let a Galois extension of number fields carry an automorphism of order two, and let a finite place
of the upper field be fixed by that automorphism, unramified over the base and of odd residue
characteristic.  The automorphism then induces an automorphism of the residue field at the place,
which is again of order two and nontrivial because the inertia group is trivial; the residues it
fixes are therefore squares.

A unit of the upper field fixed by the automorphism and of even order at the place is a square in
the completion there.  A uniformizer taken from the base field is fixed as well, so multiplying by
a power of it moves the unit to one of order zero without changing its local class modulo squares.
That unit is congruent to a residue fixed by the automorphism, hence congruent to a square, and a
unit congruent to a square at a place of odd residue characteristic is a square there.

## Main results

* `InverseGalois.CFT.localClassHom_pow_self`: the local class of a power is trivial.
* `InverseGalois.CFT.ringChar_residue_ne_two`: the residue field at a place of odd residue
  characteristic does not have characteristic two.
* `InverseGalois.CFT.exists_residue_involution`: **an automorphism of order two fixing a place
  unramified over the base induces a nontrivial involution of the residue field.**
* `InverseGalois.CFT.localClassHom_two_eq_one_of_galUnits_eq`: **a unit fixed by an automorphism of
  order two is a square in the completion at a place the automorphism fixes**, provided the place
  is unramified over the base and of odd residue characteristic and the unit has even order there.

## Tags

number field, local square, involution, inert place, residue field, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

open scoped Pointwise WithZero

attribute [local instance] Ideal.Quotient.field

/-! ### Powers and the residue characteristic -/

section Residue

variable {K : Type} [Field K] [NumberField K] {n p e : ℕ} [NeZero n]
  {v : HeightOneSpectrum (𝓞 K)}

/-- The local class of a power is trivial: the unit is already a power in the completion. -/
theorem localClassHom_pow_self (u : Kˣ) : localClassHom v n (u ^ n) = 1 :=
  (localClassHom_eq_one_iff_exists_pow v (u ^ n)).2
    ⟨algebraMap K (v.adicCompletion K) (u : K), by
      rw [← _root_.map_pow, ← Units.val_pow_eq_pow_val]⟩

/-- **Two is a unit at a place of odd residue characteristic.** -/
theorem two_notMem_asIdeal (hres : HasResidueChar (v.adicCompletion K) p e) (hp2 : ¬ p ∣ 2) :
    ((2 : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hbridge : Valued.v ((2 : ℕ) : v.adicCompletion K)
      = v.valuation K (algebraMap (𝓞 K) K ((2 : ℕ) : 𝓞 K)) := by
    rw [← _root_.map_natCast (algebraMap (𝓞 K) (v.adicCompletion K)) 2,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
  have h := hres.valued_natCast (n := 2) (by norm_num)
  rw [padicValNat.eq_zero_of_not_dvd hp2, hbridge] at h
  have h1 : v.valuation K (algebraMap (𝓞 K) K ((2 : ℕ) : 𝓞 K)) = 1 := by
    rw [h]
    simp
  intro hmem
  have hlt : v.valuation K (algebraMap (𝓞 K) K ((2 : ℕ) : 𝓞 K)) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hmem
  rw [h1] at hlt
  exact lt_irrefl 1 hlt

/-- **The residue field at a place of odd residue characteristic does not have characteristic
two.** -/
theorem ringChar_residue_ne_two (hres : HasResidueChar (v.adicCompletion K) p e) (hp2 : ¬ p ∣ 2) :
    ringChar (𝓞 K ⧸ v.asIdeal) ≠ 2 := by
  intro h
  have h0 : ((2 : ℕ) : 𝓞 K ⧸ v.asIdeal) = 0 := (ringChar.spec _ 2).2 (by rw [h])
  rw [← _root_.map_natCast (Ideal.Quotient.mk v.asIdeal) 2, Ideal.Quotient.eq_zero_iff_mem] at h0
  exact two_notMem_asIdeal hres hp2 h0

end Residue

/-! ### The involution of the residue field -/

section Involution

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {v : HeightOneSpectrum (𝓞 K)}

/-- **An automorphism of order two fixing a place unramified over the base induces a nontrivial
involution of the residue field there.**  The map from the decomposition group to the automorphisms
of the residue field has the inertia group as its kernel, and that group is trivial exactly when
the place is unramified. -/
theorem exists_residue_involution {σ : Gal(K/k)} (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) (hσv : σ • v = v)
    (hram : ramIdx (𝓞 k) v = 1) :
    ∃ τ : (𝓞 K ⧸ v.asIdeal) ≃+* (𝓞 K ⧸ v.asIdeal), (∃ y, τ y ≠ y) ∧ (∀ y, τ (τ y) = y) ∧
      ∀ x : 𝓞 K, τ (Ideal.Quotient.mk v.asIdeal x) = Ideal.Quotient.mk v.asIdeal (σ • x) := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI : v.asIdeal.LiesOver (v.asIdeal.under (𝓞 k)) := ⟨rfl⟩
  have hmem : σ ∈ MulAction.stabilizer Gal(K/k) v.asIdeal :=
    MulAction.mem_stabilizer_iff.2 (congrArg HeightOneSpectrum.asIdeal hσv)
  have hker :
      (Ideal.Quotient.stabilizerHom v.asIdeal (v.asIdeal.under (𝓞 k)) Gal(K/k)).ker = ⊥ := by
    rw [Ideal.Quotient.ker_stabilizerHom, (inertia_eq_bot_iff_ramIdx_eq_one v).2 hram]
    simp
  have hinj := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hmul : (⟨σ, hmem⟩ : MulAction.stabilizer Gal(K/k) v.asIdeal) * ⟨σ, hmem⟩ = 1 :=
    Subtype.ext hσ2
  refine ⟨(Ideal.Quotient.stabilizerHom v.asIdeal (v.asIdeal.under (𝓞 k)) Gal(K/k)
    ⟨σ, hmem⟩).toRingEquiv, ?_, fun y => ?_, fun x => rfl⟩
  · by_contra hc
    push_neg at hc
    refine hσ1 (congrArg Subtype.val (hinj (a₁ := ⟨σ, hmem⟩) (a₂ := 1) ?_))
    rw [_root_.map_one]
    refine AlgEquiv.ext fun y => ?_
    rw [AlgEquiv.one_apply]
    exact hc y
  · show Ideal.Quotient.stabilizerHom v.asIdeal (v.asIdeal.under (𝓞 k)) Gal(K/k) ⟨σ, hmem⟩
      (Ideal.Quotient.stabilizerHom v.asIdeal (v.asIdeal.under (𝓞 k)) Gal(K/k) ⟨σ, hmem⟩ y) = y
    rw [← AlgEquiv.mul_apply, ← _root_.map_mul, hmul, _root_.map_one, AlgEquiv.one_apply]

end Involution

/-! ### A fixed unit is a local square -/

section Inert

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {p e : ℕ} {v : HeightOneSpectrum (𝓞 K)}

/-- **A unit fixed by an automorphism of order two is a square in the completion at a place the
automorphism fixes**, provided the place is unramified over the base and of odd residue
characteristic and the unit has even order there.  A uniformizer of the base field is fixed as
well, so the unit may be taken of order zero; it is then congruent to a residue fixed by the
induced involution of the residue field, hence to a square, and a unit congruent to a square at a
place of odd residue characteristic is a square there. -/
theorem localClassHom_two_eq_one_of_galUnits_eq (hres : HasResidueChar (v.adicCompletion K) p e)
    (hp2 : ¬ p ∣ 2) {σ : Gal(K/k)} (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) (hσv : σ • v = v)
    (hram : ramIdx (𝓞 k) v = 1) {a : Kˣ} (ha : galUnits σ a = a)
    (heven : (2 : ℤ) ∣ placeValue v a) : localClassHom v 2 a = 1 := by
  classical
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI : v.asIdeal.IsMaximal := isMaximal_of_ne_bot_base v.asIdeal v.ne_bot
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := finite_quotient_of_ne_bot_base v.asIdeal v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  -- a uniformizer coming from the base field, fixed by the automorphism
  obtain ⟨π, hπ⟩ := (primeUnder (𝓞 k) v).valuation_exists_uniformizer k
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero] at hπ
    exact (WithZero.exp_pos (a := (-1 : ℤ))).ne hπ
  have ht0 : algebraMap k K π ≠ 0 := by
    simpa using (algebraMap k K).injective.ne hπ0
  obtain ⟨t, htgal, htord⟩ : ∃ t : Kˣ, galUnits σ t = t ∧ ord K v (t : K) = 1 := by
    refine ⟨Units.mk0 (algebraMap k K π) ht0, Units.ext (σ.commutes π), ?_⟩
    show ord K v (algebraMap k K π) = 1
    have hval : v.valuation K (algebraMap k K π) = WithZero.exp (-1 : ℤ) := by
      rw [valuation_algebraMap (A := 𝓞 k) v π, hram, pow_one, hπ]
    rw [valuation_eq_exp_neg_ord K v ht0] at hval
    simpa using congrArg WithZero.log hval
  -- move the unit to one of order zero
  obtain ⟨m, hm⟩ := heven
  have haord : ord K v (a : K) = -(2 * m) := by
    have hpv := placeValue_eq_neg_ord v a
    omega
  obtain ⟨b, hbgal, hbord, hbclass⟩ : ∃ b : Kˣ, galUnits σ b = b ∧ ord K v (b : K) = 0 ∧
      localClassHom v 2 a = localClassHom v 2 b := by
    refine ⟨a * (t ^ m) ^ 2, ?_, ?_, ?_⟩
    · rw [_root_.map_mul, ha, _root_.map_pow, _root_.map_zpow, htgal]
    · have hzne : ((t : K) ^ m) ≠ 0 := zpow_ne_zero m t.ne_zero
      have hcoe : ((a * (t ^ m) ^ 2 : Kˣ) : K) = (a : K) * ((t : K) ^ m) ^ 2 := by
        push_cast
        ring
      rw [hcoe, ord_mul v a.ne_zero (pow_ne_zero 2 hzne), ord_pow v hzne 2, ord_zpow v t.ne_zero m,
        htord, haord]
      push_cast
      ring
    · rw [_root_.map_mul, localClassHom_pow_self]
      exact (mul_one (localClassHom v 2 a)).symm
  have hbval : v.valuation K (b : K) = 1 := by
    rw [valuation_eq_exp_neg_ord K v b.ne_zero, hbord]
    simp
  -- approximate it by an algebraic integer
  obtain ⟨r, hr⟩ := exists_valuation_sub_algebraMap_le v (le_of_eq hbval)
  have hexp1 : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
    rw [show (1 : ℤᵐ⁰) = WithZero.exp (0 : ℤ) from rfl]
    exact WithZero.exp_lt_exp.2 (by norm_num)
  have hrlt : v.valuation K ((b : K) - algebraMap (𝓞 K) K r) < 1 := lt_of_le_of_lt hr hexp1
  have hrval : v.valuation K (algebraMap (𝓞 K) K r) = 1 := by
    refine (Valuation.map_eq_of_sub_lt (v.valuation K) ?_).trans hbval
    rw [Valuation.map_sub_swap, hbval]
    exact hrlt
  -- the residue of the approximation is fixed by the automorphism
  have hσval : ∀ x : K, v.valuation K (σ x) = v.valuation K x := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · rw [_root_.map_zero]
    · have hσx : σ x ≠ 0 := fun hc => hx (by simpa using congrArg σ.symm hc)
      have hord := ord_galSmul σ v x
      rw [hσv] at hord
      rw [valuation_eq_exp_neg_ord K v hσx, valuation_eq_exp_neg_ord K v hx, hord]
  have hbσ : σ (b : K) = (b : K) := by rw [← coe_galUnits_apply σ b, hbgal]
  have hsmulcoe : ∀ x : 𝓞 K, algebraMap (𝓞 K) K (σ • x) = σ (algebraMap (𝓞 K) K x) :=
    fun _ => rfl
  have hsub : σ • r - r ∈ v.asIdeal := by
    have h1 : v.valuation K ((b : K) - algebraMap (𝓞 K) K (σ • r)) < 1 := by
      have h2 := hσval ((b : K) - algebraMap (𝓞 K) K r)
      rw [_root_.map_sub, hbσ] at h2
      rw [hsmulcoe r, h2]
      exact hrlt
    have h3 : v.valuation K (algebraMap (𝓞 K) K (σ • r - r)) < 1 := by
      have heq : algebraMap (𝓞 K) K (σ • r - r) =
          ((b : K) - algebraMap (𝓞 K) K r) - ((b : K) - algebraMap (𝓞 K) K (σ • r)) := by
        rw [_root_.map_sub]
        ring
      rw [heq]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hrlt h1)
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) (v := v) (σ • r - r)).1 h3
  -- a fixed residue in odd characteristic is a square
  obtain ⟨τ, hτne, hτinv, hτapply⟩ := exists_residue_involution hσ1 hσ2 hσv hram
  have hfix : τ (Ideal.Quotient.mk v.asIdeal r) = Ideal.Quotient.mk v.asIdeal r := by
    rw [hτapply, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hsub
  obtain ⟨s, hs⟩ :=
    isSquare_of_ringEquiv_apply_eq (ringChar_residue_ne_two hres hp2) hτne hτinv hfix
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
  have hsub2 : r - c * c ∈ v.asIdeal := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, _root_.map_mul]
    exact hs
  -- the approximation is congruent to a square
  have hcclt : v.valuation K (algebraMap (𝓞 K) K (r - c * c)) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) (v := v) (r - c * c)).2 hsub2
  have hccval : v.valuation K (algebraMap (𝓞 K) K (c * c)) = 1 := by
    refine (Valuation.map_eq_of_sub_lt (v.valuation K) ?_).trans hrval
    rw [Valuation.map_sub_swap, hrval, ← _root_.map_sub]
    exact hcclt
  have hc0 : algebraMap (𝓞 K) K c ≠ 0 := by
    intro hz
    rw [_root_.map_mul, hz, zero_mul, _root_.map_zero] at hccval
    exact zero_ne_one hccval
  have hd2 : ((Units.mk0 (algebraMap (𝓞 K) K c) hc0 ^ 2 : Kˣ) : K) =
      algebraMap (𝓞 K) K (c * c) := by
    rw [_root_.map_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    ring
  have hclose : v.valuation K ((b : K) - ((Units.mk0 (algebraMap (𝓞 K) K c) hc0 ^ 2 : Kˣ) : K)) <
      v.valuation K ((Units.mk0 (algebraMap (𝓞 K) K c) hc0 ^ 2 : Kˣ) : K) := by
    rw [hd2, hccval]
    have heq : (b : K) - algebraMap (𝓞 K) K (c * c) =
        ((b : K) - algebraMap (𝓞 K) K r) + algebraMap (𝓞 K) K (r - c * c) := by
      rw [_root_.map_sub]
      ring
    rw [heq]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hrlt hcclt)
  rw [hbclass, localClassHom_eq_of_valuation_sub_lt hres hp2 hclose, localClassHom_pow_self]

end Inert

end InverseGalois.CFT
