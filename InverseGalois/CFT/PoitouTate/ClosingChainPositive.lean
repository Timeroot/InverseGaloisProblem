/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.ReciprocityPositive
import InverseGalois.CFT.PoitouTate.ClosingChainRamified
import InverseGalois.CFT.PoitouTate.PositiveClasses

/-!
# The reciprocity law of the closing chain, for a second unit positive at every real embedding

The reciprocity law between two units of a number field, each unramified away from a single place,
was stated under the demand that minus one be a power of the exponent.  That demand is archimedean:
it is what makes the infinite half of the product formula disappear.  At an even exponent it also
makes the field totally complex, so a field with a real place can never meet it, and the law has to
be restated.

A second unit which every real embedding sends to a positive number does just as well: the
archimedean symbols against it are trivial one by one, so the finite half of the product formula is
trivial by itself.  That is the only use the law makes of the demand, and the rest of the argument
— the symbols away from the two exceptional places, the collapse to a value at a Frobenius
automorphism raised to a value, the cancellation of an exponent prime to the order — is unchanged.

The same substitution is available for two units ramified on a prescribed set as well, provided
their classes at each place of that set lie on one line.  There the isotropy of the line is read in
the completion at the place, so what it asks for is a square root of minus one **there**, at those
places alone; a field with a real place has plenty of places meeting that, and the demand no longer
runs over the whole field.

The two routes join into one statement.  Being a local power at every infinite place is what the
duality theorem hands over, and at a prime exponent it says nothing at all when the exponent is odd
— where minus one is a power anyway — and says exactly positivity when the exponent is two.  So the
closing chain holds at every prime exponent for units which are local powers at the infinite
places, the isotropy of the line being read place by place.

## Main results

* `InverseGalois.CFT.placeFrobValue_eq_placeFrobValue_of_forall_pos`: **reciprocity between two
  units each ramified at a single place, normalised**, for a second unit positive at every real
  embedding.
* `InverseGalois.CFT.placeFrobValue_zpow_eq_zpow_of_isotropic_pos`: **the same law for units
  ramified on a prescribed set as well**, on which their classes lie on one line.
* `InverseGalois.CFT.placeFrobValue_eq_placeFrobValue_of_isotropic_pos`: its normalised form.
* `InverseGalois.CFT.forall_pos_galUnits`: an automorphism carries a unit positive at every real
  embedding to one positive at every real embedding.
* `InverseGalois.CFT.placeFrobValue_mul_eq_one_of_isotropic_pos`,
  `InverseGalois.CFT.localClassHom_mul_eq_one_of_isotropic_pos`: **the closing chain** for units
  ramified on the prescribed set as well and positive at every real embedding.
* `InverseGalois.CFT.localClassHom_mul_eq_one_of_isotropic_inf`: **the closing chain at every prime
  exponent**, for units which are local powers at the infinite places.

## Tags

reciprocity, Frobenius, totally positive, isotropic, cyclic, product formula, number field
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section Positive

variable {k : Type} [Field k] [NumberField k] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 k) → ℕ}

/-- **Reciprocity between two units each ramified at a single place, normalised**, for a second
unit positive at every real embedding: when the two values at those places agree modulo the
exponent and are prime to it, the values of each at the Frobenius automorphism of the exceptional
place of the other are equal. -/
theorem placeFrobValue_eq_placeFrobValue_of_forall_pos (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) {v w : HeightOneSpectrum (𝓞 k)} (hvw : v ≠ w)
    (hvn : ¬ P v ∣ n) (hwn : ¬ P w ∣ n) {a b : kˣ}
    (hbpos : ∀ φ : k →+* ℝ, 0 < φ (b : k))
    (ha : ∀ u : HeightOneSpectrum (𝓞 k), u ≠ v → (n : ℤ) ∣ placeValue u a)
    (hb : ∀ u : HeightOneSpectrum (𝓞 k), u ≠ w → (n : ℤ) ∣ placeValue u b)
    (hap : ∀ u : HeightOneSpectrum (𝓞 k), P u ∣ n →
      ∃ c : (u.adicCompletion k)ˣ,
        c ^ n = Units.map (algebraMap k (u.adicCompletion k)).toMonoidHom a)
    {m : ℤ} (hm : IsCoprime m (n : ℤ)) (hav : placeValue v a ≡ m [ZMOD (n : ℤ)])
    (hbw : placeValue w b ≡ m [ZMOD (n : ℤ)]) :
    placeFrobValue hres hζ w a = placeFrobValue hres hζ v b := by
  have h := placeFrobValue_zpow_eq_zpow_of_forall_pos hn hres hζ hvw hvn hwn hbpos ha hb hap
  rw [zpow_eq_zpow_of_modEq (pow_placeFrobValue_eq_one hres hζ w a) hbw,
    zpow_eq_zpow_of_modEq (pow_placeFrobValue_eq_one hres hζ v b) hav] at h
  exact eq_of_zpow_eq_zpow_of_isCoprime (pow_placeFrobValue_eq_one hres hζ w a)
    (pow_placeFrobValue_eq_one hres hζ v b) hm h

/-- **Reciprocity between two units each ramified at a single place outside a prescribed set**,
whose classes at every place of that set lie on one line, for a second unit positive at every real
embedding.  The factors of the product formula at the prescribed places vanish by the isotropy of
the line there, the archimedean factors vanish by positivity, and the two remaining ones give the
law. -/
theorem placeFrobValue_zpow_eq_zpow_of_isotropic_pos (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) {T : Finset (HeightOneSpectrum (𝓞 k))}
    {v w : HeightOneSpectrum (𝓞 k)} (hvw : v ≠ w) (hvT : v ∉ T) (hwT : w ∉ T)
    (hvn : ¬ P v ∣ n) (hwn : ¬ P w ∣ n) {a b : kˣ}
    (hbpos : ∀ φ : k →+* ℝ, 0 < φ (b : k))
    (ha : ∀ u : HeightOneSpectrum (𝓞 k), u ∉ T → u ≠ v → (n : ℤ) ∣ placeValue u a)
    (hb : ∀ u : HeightOneSpectrum (𝓞 k), u ∉ T → u ≠ w → (n : ℤ) ∣ placeValue u b)
    (hap : ∀ u : HeightOneSpectrum (𝓞 k), P u ∣ n →
      ∃ c : (u.adicCompletion k)ˣ,
        c ^ n = Units.map (algebraMap k (u.adicCompletion k)).toMonoidHom a)
    (hneg : ∀ u ∈ T, IsNegOnePow (u.adicCompletion k) n)
    (hiso : ∀ u ∈ T, ∃ d : localClasses u n, localClassHom u n a ∈ Subgroup.zpowers d ∧
      localClassHom u n b ∈ Subgroup.zpowers d) :
    placeFrobValue hres hζ w a ^ placeValue w b
      = placeFrobValue hres hζ v b ^ placeValue v a := by
  classical
  have hS : ∀ u : HeightOneSpectrum (𝓞 k), u ∉ ({v, w} : Finset (HeightOneSpectrum (𝓞 k))) →
      localSymbol (hres u) (isUnitValGen_one (valued_adicCompletion_surjective u))
        (hζ.map_of_injective (algebraMap k (u.adicCompletion k)).injective)
        (Units.map (algebraMap k (u.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (u.adicCompletion k)).toMonoidHom b) = 1 := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    push_neg at hu
    by_cases huT : u ∈ T
    · obtain ⟨d, hda, hdb⟩ := hiso u huT
      exact localSymbol_eq_one_of_localClassHom_mem_zpowers hres hζ u (hneg u huT) hda hdb
    · by_cases hun : P u ∣ n
      · exact localSymbol_eq_one_of_isPow_left _ _ _ (hap u hun) _
      · exact localSymbol_eq_one_of_dvd_of_dvd _ _ _ hn hun (ha u huT hu.1) (hb u huT hu.2)
  have hprod := prod_localSymbol_eq_one_of_forall_pos hn hres hζ a hbpos {v, w} hS
  rw [Finset.prod_pair hvw,
    localSymbol_eq_placeFrobValue_zpow_right hn hres hζ hvn (hb v hvT hvw) a,
    localSymbol_eq_placeFrobValue_zpow hn hres hζ hwn (ha w hwT (Ne.symm hvw)) b] at hprod
  exact (inv_mul_eq_one.mp hprod).symm

/-- **Reciprocity between two units each ramified at a single place outside a prescribed set,
normalised**, for a second unit positive at every real embedding: when the two values at the
exceptional places agree modulo the exponent and are prime to it, the values of each at the
Frobenius automorphism of the other's place are equal. -/
theorem placeFrobValue_eq_placeFrobValue_of_isotropic_pos (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) {T : Finset (HeightOneSpectrum (𝓞 k))}
    {v w : HeightOneSpectrum (𝓞 k)} (hvw : v ≠ w) (hvT : v ∉ T) (hwT : w ∉ T)
    (hvn : ¬ P v ∣ n) (hwn : ¬ P w ∣ n) {a b : kˣ}
    (hbpos : ∀ φ : k →+* ℝ, 0 < φ (b : k))
    (ha : ∀ u : HeightOneSpectrum (𝓞 k), u ∉ T → u ≠ v → (n : ℤ) ∣ placeValue u a)
    (hb : ∀ u : HeightOneSpectrum (𝓞 k), u ∉ T → u ≠ w → (n : ℤ) ∣ placeValue u b)
    (hap : ∀ u : HeightOneSpectrum (𝓞 k), P u ∣ n →
      ∃ c : (u.adicCompletion k)ˣ,
        c ^ n = Units.map (algebraMap k (u.adicCompletion k)).toMonoidHom a)
    (hneg : ∀ u ∈ T, IsNegOnePow (u.adicCompletion k) n)
    (hiso : ∀ u ∈ T, ∃ d : localClasses u n, localClassHom u n a ∈ Subgroup.zpowers d ∧
      localClassHom u n b ∈ Subgroup.zpowers d)
    {m : ℤ} (hm : IsCoprime m (n : ℤ)) (hav : placeValue v a ≡ m [ZMOD (n : ℤ)])
    (hbw : placeValue w b ≡ m [ZMOD (n : ℤ)]) :
    placeFrobValue hres hζ w a = placeFrobValue hres hζ v b := by
  have h := placeFrobValue_zpow_eq_zpow_of_isotropic_pos hn hres hζ hvw hvT hwT hvn hwn hbpos
    ha hb hap hneg hiso
  rw [zpow_eq_zpow_of_modEq (pow_placeFrobValue_eq_one hres hζ w a) hbw,
    zpow_eq_zpow_of_modEq (pow_placeFrobValue_eq_one hres hζ v b) hav] at h
  exact eq_of_zpow_eq_zpow_of_isCoprime (pow_placeFrobValue_eq_one hres hζ w a)
    (pow_placeFrobValue_eq_one hres hζ v b) hm h

end Positive

/-! ### The closing chain -/

section Chain

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ} {T : Finset (HeightOneSpectrum (𝓞 K))}

omit [NeZero n] [NumberField K] in
/-- **A unit positive at every real embedding is carried by an automorphism to a unit positive at
every real embedding**: an embedding composed with the automorphism is again an embedding. -/
theorem forall_pos_galUnits (σ : Gal(K/k)) {a : Kˣ} (ha : ∀ φ : K →+* ℝ, 0 < φ (a : K))
    (φ : K →+* ℝ) : 0 < φ ((galUnits σ a : Kˣ) : K) :=
  ha (φ.comp σ.toRingEquiv.toRingHom)

/-- **The closing chain for units ramified on a prescribed set as well, for units positive at every
real embedding**: the product of the two units supplied by the pigeonhole principle is trivial at
the moved place.  The two applications of the reciprocity law absorb the prescribed places, where
the classes compared lie on one line, and the archimedean places, where positivity is enough. -/
theorem placeFrobValue_mul_eq_one_of_isotropic_pos (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hT : ∀ (τ : Gal(K/k)) (u : HeightOneSpectrum (𝓞 K)), u ∈ T → τ • u ∈ T) {σ : Gal(K/k)}
    {Q R : HeightOneSpectrum (𝓞 K)} (hQσQ : Q ≠ σ • Q) (hQσR : Q ≠ σ • R) (hQT : Q ∉ T)
    (hRT : R ∉ T) (hQn : ¬ P Q ∣ n) (hσQn : ¬ P (σ • Q) ∣ n) (hσRn : ¬ P (σ • R) ∣ n)
    {zi zN : Kˣ} (hzipos : ∀ φ : K →+* ℝ, 0 < φ (zi : K))
    (hzNpos : ∀ φ : K →+* ℝ, 0 < φ (zN : K))
    (hzi : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ Q → (n : ℤ) ∣ placeValue u zi)
    (hzN : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ R → (n : ℤ) ∣ placeValue u zN)
    (hziQ : IsCoprime (placeValue Q zi) (n : ℤ))
    (hzNR : placeValue R zN ≡ placeValue Q zi [ZMOD (n : ℤ)])
    (hzip : ∀ u : HeightOneSpectrum (𝓞 K), P u ∣ n →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ n = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom zi)
    (hneg : ∀ u ∈ T, IsNegOnePow (u.adicCompletion K) n)
    (hiso : ∀ u ∈ T, ∃ d : localClasses u n, localClassHom u n zi ∈ Subgroup.zpowers d ∧
      localClassHom u n (galUnits σ zi) ∈ Subgroup.zpowers d ∧
      localClassHom u n (galUnits σ zN) ∈ Subgroup.zpowers d)
    (hpigeon : placeFrobValue hres hζ (σ • R) zN = placeFrobValue hres hζ (σ • Q) zi)
    (hcond : placeFrobValue hres hζ Q (galUnits σ zN)
      = (placeFrobValue hres hζ Q (galUnits σ zi))⁻¹) :
    placeFrobValue hres hζ (σ • R) (zi * zN) = 1 := by
  have h1 : placeFrobValue hres hζ (σ • Q) zi = placeFrobValue hres hζ Q (galUnits σ zi) :=
    placeFrobValue_eq_placeFrobValue_of_isotropic_pos hn hres hζ hQσQ hQT
      (notMem_of_smul_stable hT σ hQT) hQn hσQn (forall_pos_galUnits σ hzipos) hzi
      (dvd_placeValue_galUnits_of_notMem hT σ hzi) hzip hneg
      (fun u hu => (hiso u hu).imp fun _ h => ⟨h.1, h.2.1⟩) hziQ (Int.ModEq.refl _)
      (by rw [placeValue_galSmul])
  have h2 : placeFrobValue hres hζ (σ • R) zi = placeFrobValue hres hζ Q (galUnits σ zN) :=
    placeFrobValue_eq_placeFrobValue_of_isotropic_pos hn hres hζ hQσR hQT
      (notMem_of_smul_stable hT σ hRT) hQn hσRn (forall_pos_galUnits σ hzNpos) hzi
      (dvd_placeValue_galUnits_of_notMem hT σ hzN) hzip hneg
      (fun u hu => (hiso u hu).imp fun _ h => ⟨h.1, h.2.2⟩) hziQ (Int.ModEq.refl _)
      (by rw [placeValue_galSmul]; exact hzNR)
  have hcond' : placeFrobValue hres hζ Q (galUnits σ zi)
      = (placeFrobValue hres hζ Q (galUnits σ zN))⁻¹ := by rw [hcond, inv_inv]
  rw [placeFrobValue_mul, hpigeon, h1, hcond', ← h2]
  exact mul_inv_cancel _

/-- **The closing chain for units ramified on a prescribed set as well and positive at every real
embedding, read on the classes**: the product of the two units supplied by the pigeonhole principle
is a power in the completion at the moved place. -/
theorem localClassHom_mul_eq_one_of_isotropic_pos (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hT : ∀ (τ : Gal(K/k)) (u : HeightOneSpectrum (𝓞 K)), u ∈ T → τ • u ∈ T) {σ : Gal(K/k)}
    {Q R : HeightOneSpectrum (𝓞 K)} (hQσQ : Q ≠ σ • Q) (hQσR : Q ≠ σ • R) (hRσR : R ≠ σ • R)
    (hQT : Q ∉ T) (hRT : R ∉ T) (hQn : ¬ P Q ∣ n) (hσQn : ¬ P (σ • Q) ∣ n)
    (hσRn : ¬ P (σ • R) ∣ n) {zi zN : Kˣ} (hzipos : ∀ φ : K →+* ℝ, 0 < φ (zi : K))
    (hzNpos : ∀ φ : K →+* ℝ, 0 < φ (zN : K))
    (hzi : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ Q → (n : ℤ) ∣ placeValue u zi)
    (hzN : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ R → (n : ℤ) ∣ placeValue u zN)
    (hziQ : IsCoprime (placeValue Q zi) (n : ℤ))
    (hzNR : placeValue R zN ≡ placeValue Q zi [ZMOD (n : ℤ)])
    (hzip : ∀ u : HeightOneSpectrum (𝓞 K), P u ∣ n →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ n = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom zi)
    (hneg : ∀ u ∈ T, IsNegOnePow (u.adicCompletion K) n)
    (hiso : ∀ u ∈ T, ∃ d : localClasses u n, localClassHom u n zi ∈ Subgroup.zpowers d ∧
      localClassHom u n (galUnits σ zi) ∈ Subgroup.zpowers d ∧
      localClassHom u n (galUnits σ zN) ∈ Subgroup.zpowers d)
    (hpigeon : placeFrobValue hres hζ (σ • R) zN = placeFrobValue hres hζ (σ • Q) zi)
    (hcond : placeFrobValue hres hζ Q (galUnits σ zN)
      = (placeFrobValue hres hζ Q (galUnits σ zi))⁻¹) :
    localClassHom (σ • R) n (zi * zN) = 1 := by
  refine localClassHom_eq_one_of_placeFrobValue_eq_one hn hres hζ hσRn ?_
    (placeFrobValue_mul_eq_one_of_isotropic_pos hn hres hζ hT hQσQ hQσR hQT hRT hQn hσQn hσRn
      hzipos hzNpos hzi hzN hziQ hzNR hzip hneg hiso hpigeon hcond)
  rw [placeValue_mul]
  exact dvd_add (hzi _ (notMem_of_smul_stable hT σ hRT) (Ne.symm hQσR))
    (hzN _ (notMem_of_smul_stable hT σ hRT) (Ne.symm hRσR))

/-- **The closing chain at every prime exponent, for units which are local powers at the infinite
places**: the product of the two units supplied by the pigeonhole principle is a power in the
completion at the moved place.  An odd exponent asks nothing at the infinite places and has minus
one for a power, so the chain is available there outright; at the exponent two being a local power
at every infinite place is positivity at every real embedding, which is what the archimedean half
of the product formula wants. -/
theorem localClassHom_mul_eq_one_of_isotropic_inf (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hT : ∀ (τ : Gal(K/k)) (u : HeightOneSpectrum (𝓞 K)), u ∈ T → τ • u ∈ T) {σ : Gal(K/k)}
    {Q R : HeightOneSpectrum (𝓞 K)} (hQσQ : Q ≠ σ • Q) (hQσR : Q ≠ σ • R) (hRσR : R ≠ σ • R)
    (hQT : Q ∉ T) (hRT : R ∉ T) (hQn : ¬ P Q ∣ n) (hσQn : ¬ P (σ • Q) ∣ n)
    (hσRn : ¬ P (σ • R) ∣ n) {zi zN : Kˣ}
    (hziinf : ∀ w : InfinitePlace K, infClassHom w n zi = 1)
    (hzNinf : ∀ w : InfinitePlace K, infClassHom w n zN = 1)
    (hzi : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ Q → (n : ℤ) ∣ placeValue u zi)
    (hzN : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ R → (n : ℤ) ∣ placeValue u zN)
    (hziQ : IsCoprime (placeValue Q zi) (n : ℤ))
    (hzNR : placeValue R zN ≡ placeValue Q zi [ZMOD (n : ℤ)])
    (hzip : ∀ u : HeightOneSpectrum (𝓞 K), P u ∣ n →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ n = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom zi)
    (hneg : ∀ u ∈ T, IsNegOnePow (u.adicCompletion K) n)
    (hiso : ∀ u ∈ T, ∃ d : localClasses u n, localClassHom u n zi ∈ Subgroup.zpowers d ∧
      localClassHom u n (galUnits σ zi) ∈ Subgroup.zpowers d ∧
      localClassHom u n (galUnits σ zN) ∈ Subgroup.zpowers d)
    (hpigeon : placeFrobValue hres hζ (σ • R) zN = placeFrobValue hres hζ (σ • Q) zi)
    (hcond : placeFrobValue hres hζ Q (galUnits σ zN)
      = (placeFrobValue hres hζ Q (galUnits σ zi))⁻¹) :
    localClassHom (σ • R) n (zi * zN) = 1 := by
  rcases hn.eq_two_or_odd' with rfl | hodd
  · exact localClassHom_mul_eq_one_of_isotropic_pos hn hres hζ hT hQσQ hQσR hRσR hQT hRT hQn
      hσQn hσRn (forall_pos_of_forall_infClassHom_eq_one dvd_rfl hziinf)
      (forall_pos_of_forall_infClassHom_eq_one dvd_rfl hzNinf) hzi hzN hziQ hzNR hzip hneg hiso
      hpigeon hcond
  · exact localClassHom_mul_eq_one_of_isotropic hn (isNegOnePow_of_odd hodd) hres hζ hT hQσQ
      hQσR hRσR hQT hRT hQn hσQn hσRn hzi hzN hziQ hzNR hzip hiso hpigeon hcond

end Chain

end InverseGalois.CFT
