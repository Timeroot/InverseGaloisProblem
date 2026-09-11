/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.SymbolReciprocity
import InverseGalois.CFT.PoitouTate.GlobalClasses

/-!
# The pigeonhole principle, and the closing chain of the construction of algebraic numbers

The construction of an algebraic number with prescribed local behaviour produces a sequence of
units of a Galois extension of number fields, each of which is ramified at exactly one finite
place, the value at that place being prime to the exponent, and each of which is arranged to
cancel the values of its predecessors along the Galois group.  The element wanted is a product of
two members of that sequence, chosen so that their values at the Frobenius automorphisms of the
moved places agree and their values at their own places agree modulo the exponent; the pigeonhole
principle produces such a pair because the former are killed by the exponent, and the elements of
the rationals modulo the integers killed by the exponent are finite in number, while the latter
range over the residues modulo the exponent.

For such a pair the product is trivial at every moved place.  The chain of equalities which shows
this is two applications of one reciprocity law.  Moving a place by an automorphism and moving the
unit by the same automorphism leaves the value at the place unchanged, so a unit ramified at one
place has a Galois conjugate ramified at the image of that place, and two such units satisfy the
reciprocity law between two units each ramified at a single place.  Applying it to the first unit
against its own conjugate, and then to the first unit against the conjugate of the second, turns
the equality supplied by the pigeonhole principle and the cancellation arranged in the construction
into the statement that the values of the two units at the Frobenius automorphism of the moved
place are mutually inverse.

## Main results

* `InverseGalois.CFT.placeFrobValue_eq_placeFrobValue`: reciprocity between two units each
  ramified at a single place, where the two values there agree modulo the exponent and are prime
  to it.
* `InverseGalois.CFT.finite_setOf_pow_eq_one`: the elements of the rationals modulo the integers
  killed by the exponent are finite in number.
* `InverseGalois.CFT.exists_lt_placeFrobValue_eq`: **the pigeonhole principle for a sequence of
  units and a sequence of places.**
* `InverseGalois.CFT.placeFrobValue_eq_of_localClassHom_eq`,
  `InverseGalois.CFT.localClassHom_eq_one_of_placeFrobValue_eq_one`: the value at a Frobenius
  automorphism sees exactly the class of the unit modulo `n`-th powers.
* `InverseGalois.CFT.placeFrobValue_mul_eq_one`: **the closing chain**: the product of the two
  units supplied by the pigeonhole principle is trivial at the moved place.
* `InverseGalois.CFT.localClassHom_mul_eq_one`: **the closing chain, read on the classes**: that
  product is a power in the completion at the moved place.

## Tags

norm residue symbol, power residue symbol, reciprocity, Frobenius, unramified, pigeonhole,
number field, class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped Pointwise

/-! ### Cancelling an exponent prime to the order -/

section Cancel

/-- An element killed by `n` sees only the residue of an exponent modulo `n`. -/
theorem zpow_eq_zpow_of_modEq {G : Type*} [Group G] {x : G} {n : ℕ} (hx : x ^ n = 1)
    {p q : ℤ} (hpq : p ≡ q [ZMOD (n : ℤ)]) : x ^ p = x ^ q := by
  obtain ⟨s, hs⟩ := hpq.dvd
  have hp : p = q - (n : ℤ) * s := by rw [← hs]; ring
  rw [hp, zpow_sub, zpow_mul, zpow_natCast, hx, one_zpow, inv_one, mul_one]

/-- Two elements killed by `n` which agree after being raised to an exponent prime to `n` are
equal. -/
theorem eq_of_zpow_eq_zpow_of_isCoprime {G : Type*} [Group G] {x y : G} {n : ℕ} (hx : x ^ n = 1)
    (hy : y ^ n = 1) {m : ℤ} (hm : IsCoprime m (n : ℤ)) (h : x ^ m = y ^ m) : x = y := by
  obtain ⟨u, v, huv⟩ := hm
  have hxn : x ^ (n : ℤ) = 1 := by rw [zpow_natCast, hx]
  have hyn : y ^ (n : ℤ) = 1 := by rw [zpow_natCast, hy]
  calc x = x ^ (u * m + v * (n : ℤ)) := by rw [huv, zpow_one]
    _ = (x ^ m) ^ u * (x ^ (n : ℤ)) ^ v := by rw [zpow_add, zpow_mul', zpow_mul']
    _ = (y ^ m) ^ u * (y ^ (n : ℤ)) ^ v := by rw [h, hxn, hyn]
    _ = y ^ (u * m + v * (n : ℤ)) := by rw [zpow_add, zpow_mul', zpow_mul']
    _ = y := by rw [huv, zpow_one]

end Cancel

/-! ### Reciprocity, normalised -/

section Normalised

variable {k : Type} [Field k] [NumberField k] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 k) → ℕ}

/-- **Reciprocity between two units each ramified at a single place**, where the two values at
those places agree modulo the exponent and are prime to it: the values of each at the Frobenius
automorphism of the exceptional place of the other are equal. -/
theorem placeFrobValue_eq_placeFrobValue (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) {v w : HeightOneSpectrum (𝓞 k)} (hvw : v ≠ w)
    (hvn : ¬ P v ∣ n) (hwn : ¬ P w ∣ n) {a b : kˣ}
    (ha : ∀ u : HeightOneSpectrum (𝓞 k), u ≠ v → (n : ℤ) ∣ placeValue u a)
    (hb : ∀ u : HeightOneSpectrum (𝓞 k), u ≠ w → (n : ℤ) ∣ placeValue u b)
    (hap : ∀ u : HeightOneSpectrum (𝓞 k), P u ∣ n →
      ∃ c : (u.adicCompletion k)ˣ,
        c ^ n = Units.map (algebraMap k (u.adicCompletion k)).toMonoidHom a)
    {m : ℤ} (hm : IsCoprime m (n : ℤ)) (hav : placeValue v a ≡ m [ZMOD (n : ℤ)])
    (hbw : placeValue w b ≡ m [ZMOD (n : ℤ)]) :
    placeFrobValue hres hζ w a = placeFrobValue hres hζ v b := by
  have h := placeFrobValue_zpow_eq_zpow hn hn2 hres hζ hvw hvn hwn ha hb hap
  rw [zpow_eq_zpow_of_modEq (pow_placeFrobValue_eq_one hres hζ w a) hbw,
    zpow_eq_zpow_of_modEq (pow_placeFrobValue_eq_one hres hζ v b) hav] at h
  exact eq_of_zpow_eq_zpow_of_isCoprime (pow_placeFrobValue_eq_one hres hζ w a)
    (pow_placeFrobValue_eq_one hres hζ v b) hm h

/-- The value of a unit of a number field at a finite place is additive. -/
theorem placeValue_mul (v : HeightOneSpectrum (𝓞 k)) (a b : kˣ) :
    placeValue v (a * b) = placeValue v a + placeValue v b := by
  rw [placeValue_def, placeValue_def, placeValue_def, _root_.map_mul, ofMul_mul, map_add]

/-- **The value at a Frobenius automorphism depends only on the class of the unit** modulo `n`-th
powers in the completion. -/
theorem placeFrobValue_eq_of_localClassHom_eq
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (v : HeightOneSpectrum (𝓞 k)) {a b : kˣ}
    (h : localClassHom v n a = localClassHom v n b) :
    placeFrobValue hres hζ v a = placeFrobValue hres hζ v b := by
  have hd : localClassHom v n (a⁻¹ * b) = 1 := by
    rw [_root_.map_mul, _root_.map_inv, h, inv_mul_cancel]
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 ((QuotientGroup.eq_one_iff _).1 hd)
  have hc' : c ^ n
      = Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom (a⁻¹ * b) := hc
  have h1 : placeFrobValue hres hζ v (a⁻¹ * b) = 1 := by
    rw [placeFrobValue_def, ← hc', _root_.map_pow, pow_frobValue_eq_one]
  rw [placeFrobValue_mul, placeFrobValue_inv] at h1
  exact inv_mul_eq_one.1 h1

/-- **A unit whose value at the Frobenius automorphism of a place where it is unramified is trivial
is a power in the completion at that place.** -/
theorem localClassHom_eq_one_of_placeFrobValue_eq_one (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ P v ∣ n) {a : kˣ}
    (ha : (n : ℤ) ∣ placeValue v a) (h : placeFrobValue hres hζ v a = 1) :
    localClassHom v n a = 1 := by
  obtain ⟨c, hc⟩ := (placeFrobValue_eq_one_iff hn hres hζ hv ha).1 h
  exact (QuotientGroup.eq_one_iff _).2 ⟨c, hc⟩

end Normalised

/-! ### The elements killed by the exponent -/

section Torsion

/-- An element of the rationals modulo the integers killed by `n` is a multiple of `1/n`. -/
theorem mem_range_zmodQModZ_of_nsmul_eq_zero (n : ℕ) [NeZero n] {q : QModZ} (hq : n • q = 0) :
    q ∈ Set.range (zmodQModZ n) := by
  induction q using QuotientAddGroup.induction_on with
  | _ r =>
    have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
    have h : (QuotientAddGroup.mk ((n : ℚ) * r) : QModZ) = 0 := by
      rw [← nsmul_eq_mul]; exact hq
    obtain ⟨j, hj⟩ := (QModZ.mk_eq_zero_iff _).1 h
    refine ⟨(j : ZMod n), ?_⟩
    rw [zmodQModZ_intCast]
    congr 1
    rw [div_eq_iff hn]
    exact hj.trans (mul_comm _ _)

/-- An element of the rationals modulo the integers killed by `n` is a multiple of `1/n`, read
multiplicatively. -/
theorem mem_range_zmodQModZ_of_pow_eq_one (n : ℕ) [NeZero n] {x : Multiplicative QModZ}
    (hx : x ^ n = 1) :
    x ∈ Set.range fun c : ZMod n => Multiplicative.ofAdd (zmodQModZ n c) := by
  have h : n • Multiplicative.toAdd x = 0 := by rw [← toAdd_pow, hx, toAdd_one]
  obtain ⟨c, hc⟩ := mem_range_zmodQModZ_of_nsmul_eq_zero n h
  refine ⟨c, ?_⟩
  show Multiplicative.ofAdd (zmodQModZ n c) = x
  rw [hc]
  rfl

/-- **The elements of the rationals modulo the integers killed by `n` are finite in number.** -/
theorem finite_setOf_pow_eq_one (n : ℕ) [NeZero n] :
    {x : Multiplicative QModZ | x ^ n = 1}.Finite :=
  Set.Finite.subset (Set.finite_range _) fun _ hx => mem_range_zmodQModZ_of_pow_eq_one n hx

end Torsion

/-! ### The pigeonhole principle and the closing chain -/

section Chain

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

omit [NeZero n] in
/-- The image of a unit ramified only at one place under a Galois automorphism is ramified only at
the image of that place. -/
theorem dvd_placeValue_galUnits (σ : Gal(K/k)) {v : HeightOneSpectrum (𝓞 K)} {a : Kˣ}
    (ha : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ v → (n : ℤ) ∣ placeValue u a)
    (u : HeightOneSpectrum (𝓞 K)) (hu : u ≠ σ • v) : (n : ℤ) ∣ placeValue u (galUnits σ a) := by
  have h := placeValue_galSmul (σ⁻¹ • u) σ a
  rw [smul_inv_smul] at h
  rw [h]
  exact ha _ fun hv => hu (by rw [← hv, smul_inv_smul])

/-- **The pigeonhole principle for a sequence of units and a sequence of places**: two members of
the sequence have the same value at the Frobenius automorphism of their own place, moved by any
automorphism of the extension, and the same value at their own place modulo the exponent. -/
theorem exists_lt_placeFrobValue_eq [FiniteDimensional k K]
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (Pl : ℕ → HeightOneSpectrum (𝓞 K)) (z : ℕ → Kˣ) :
    ∃ i N : ℕ, i < N ∧ placeValue (Pl N) (z N) ≡ placeValue (Pl i) (z i) [ZMOD (n : ℤ)] ∧
      ∀ σ : Gal(K/k),
        placeFrobValue hres hζ (σ • Pl N) (z N) = placeFrobValue hres hζ (σ • Pl i) (z i) := by
  have hfin : ((Set.univ.pi fun _ : Gal(K/k) => {x : Multiplicative QModZ | x ^ n = 1}) ×ˢ
      (Set.univ : Set (ZMod n))).Finite :=
    (Set.Finite.pi fun _ => finite_setOf_pow_eq_one n).prod Set.finite_univ
  have hmaps : Set.MapsTo
      (fun i : ℕ => ((fun σ : Gal(K/k) => placeFrobValue hres hζ (σ • Pl i) (z i)),
        ((placeValue (Pl i) (z i) : ℤ) : ZMod n))) Set.univ
      ((Set.univ.pi fun _ : Gal(K/k) => {x : Multiplicative QModZ | x ^ n = 1}) ×ˢ
        (Set.univ : Set (ZMod n))) :=
    fun _ _ => ⟨fun _ _ => pow_placeFrobValue_eq_one hres hζ _ _, Set.mem_univ _⟩
  obtain ⟨i, -, j, -, hij, hfeq⟩ := Set.infinite_univ.exists_ne_map_eq_of_mapsTo hmaps hfin
  have hval : placeValue (Pl i) (z i) ≡ placeValue (Pl j) (z j) [ZMOD (n : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff _ _ _).1 (congrArg Prod.snd hfeq)
  have hfrob := congrArg Prod.fst hfeq
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, hval.symm, fun σ => congrFun hfrob.symm σ⟩
  · exact ⟨j, i, h, hval, fun σ => congrFun hfrob σ⟩

/-- **The closing chain**: two units of a Galois extension of number fields, each ramified at a
single place with the same value there modulo the exponent and prime to it, the first of which is
a power in every completion whose residue characteristic divides the exponent, whose values at the
Frobenius automorphism of their own place moved by an automorphism agree, and whose Galois
conjugates have mutually inverse values at the exceptional place of the first, have a product which
is trivial at the moved place. -/
theorem placeFrobValue_mul_eq_one (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {σ : Gal(K/k)} {Q R : HeightOneSpectrum (𝓞 K)}
    (hQσQ : Q ≠ σ • Q) (hQσR : Q ≠ σ • R) (hQn : ¬ P Q ∣ n) (hσQn : ¬ P (σ • Q) ∣ n)
    (hσRn : ¬ P (σ • R) ∣ n) {zi zN : Kˣ}
    (hzi : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ Q → (n : ℤ) ∣ placeValue u zi)
    (hzN : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ R → (n : ℤ) ∣ placeValue u zN)
    (hziQ : IsCoprime (placeValue Q zi) (n : ℤ))
    (hzNR : placeValue R zN ≡ placeValue Q zi [ZMOD (n : ℤ)])
    (hzip : ∀ u : HeightOneSpectrum (𝓞 K), P u ∣ n →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ n = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom zi)
    (hpigeon : placeFrobValue hres hζ (σ • R) zN = placeFrobValue hres hζ (σ • Q) zi)
    (hcond : placeFrobValue hres hζ Q (galUnits σ zN)
      = (placeFrobValue hres hζ Q (galUnits σ zi))⁻¹) :
    placeFrobValue hres hζ (σ • R) (zi * zN) = 1 := by
  have h1 : placeFrobValue hres hζ (σ • Q) zi = placeFrobValue hres hζ Q (galUnits σ zi) :=
    placeFrobValue_eq_placeFrobValue hn hn2 hres hζ hQσQ hQn hσQn hzi
      (dvd_placeValue_galUnits σ hzi) hzip hziQ (Int.ModEq.refl _)
      (by rw [placeValue_galSmul])
  have h2 : placeFrobValue hres hζ (σ • R) zi = placeFrobValue hres hζ Q (galUnits σ zN) :=
    placeFrobValue_eq_placeFrobValue hn hn2 hres hζ hQσR hQn hσRn hzi
      (dvd_placeValue_galUnits σ hzN) hzip hziQ (Int.ModEq.refl _)
      (by rw [placeValue_galSmul]; exact hzNR)
  have hcond' : placeFrobValue hres hζ Q (galUnits σ zi)
      = (placeFrobValue hres hζ Q (galUnits σ zN))⁻¹ := by rw [hcond, inv_inv]
  rw [placeFrobValue_mul, hpigeon, h1, hcond', ← h2]
  exact mul_inv_cancel _

/-- The cancellation of the values of two units at a place transports along the Galois group. -/
theorem placeFrobValue_galUnits_eq_inv
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) {a b : Kˣ}
    (h : localClassHom v n b = (localClassHom v n a)⁻¹) :
    placeFrobValue hres hζ (σ • v) (galUnits σ b)
      = (placeFrobValue hres hζ (σ • v) (galUnits σ a))⁻¹ := by
  have h' : localClassHom (σ • v) n (galUnits σ b)
      = (localClassHom (σ • v) n (galUnits σ a))⁻¹ := by
    rw [← localClassesGalEquiv_localClassHom, ← localClassesGalEquiv_localClassHom, h,
      _root_.map_inv]
  rw [← placeFrobValue_inv]
  refine placeFrobValue_eq_of_localClassHom_eq hres hζ _ ?_
  rw [h', _root_.map_inv]

/-- **The product of the two units supplied by the pigeonhole principle is a power in the
completion at every moved place**: the closing chain, read on the classes modulo `n`-th powers. -/
theorem localClassHom_mul_eq_one (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {σ : Gal(K/k)} {Q R : HeightOneSpectrum (𝓞 K)}
    (hQσQ : Q ≠ σ • Q) (hQσR : Q ≠ σ • R) (hRσR : R ≠ σ • R) (hQn : ¬ P Q ∣ n)
    (hσQn : ¬ P (σ • Q) ∣ n) (hσRn : ¬ P (σ • R) ∣ n) {zi zN : Kˣ}
    (hzi : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ Q → (n : ℤ) ∣ placeValue u zi)
    (hzN : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ R → (n : ℤ) ∣ placeValue u zN)
    (hziQ : IsCoprime (placeValue Q zi) (n : ℤ))
    (hzNR : placeValue R zN ≡ placeValue Q zi [ZMOD (n : ℤ)])
    (hzip : ∀ u : HeightOneSpectrum (𝓞 K), P u ∣ n →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ n = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom zi)
    (hpigeon : placeFrobValue hres hζ (σ • R) zN = placeFrobValue hres hζ (σ • Q) zi)
    (hcond : placeFrobValue hres hζ Q (galUnits σ zN)
      = (placeFrobValue hres hζ Q (galUnits σ zi))⁻¹) :
    localClassHom (σ • R) n (zi * zN) = 1 := by
  refine localClassHom_eq_one_of_placeFrobValue_eq_one hn hres hζ hσRn ?_
    (placeFrobValue_mul_eq_one hn hn2 hres hζ hQσQ hQσR hQn hσQn hσRn hzi hzN hziQ hzNR hzip
      hpigeon hcond)
  rw [placeValue_mul]
  exact dvd_add (hzi _ (Ne.symm hQσR)) (hzN _ (Ne.symm hRσR))

end Chain

end InverseGalois.CFT
