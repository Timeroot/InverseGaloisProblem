/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ClosingChain
import InverseGalois.CFT.PoitouTate.CyclicPairing

/-!
# The closing chain for units ramified on a prescribed set as well

The reciprocity law between two units of a number field, and the closing chain built out of it,
were stated for units ramified at a single place each.  A construction which prescribes a local
behaviour that is itself ramified produces units ramified at the prescribed places as well, and the
reciprocity law has to absorb those places.

It absorbs them for free at an odd exponent, provided the classes of the two units at each such
place lie on one line: the norm residue symbol is isotropic on a cyclic group of classes, so the
factor of the product formula at such a place is trivial, exactly as it is at a place where both
units are unramified.  Nothing else changes, and the closing chain goes through verbatim.

In the intended use the prescription is carried by one place of each Galois orbit and is trivial at
the others, and every unit produced has the prescribed class at every prescribed place; the classes
compared at one place are then the prescribed class there and the images of the prescribed classes
at the places of the same orbit, all but one of which are trivial.

## Main results

* `InverseGalois.CFT.localSymbol_eq_one_of_localClassHom_mem_zpowers`: the norm residue symbol of
  two units whose classes at a place lie on one line is trivial there, at an odd exponent.
* `InverseGalois.CFT.placeFrobValue_zpow_eq_zpow_of_isotropic`: **reciprocity between two units
  each ramified at a single place outside a prescribed set**, on which their classes lie on one
  line.
* `InverseGalois.CFT.placeFrobValue_eq_placeFrobValue_of_isotropic`: the normalised form.
* `InverseGalois.CFT.exists_zpowers_of_prescription`: a prescription supported at no more than one
  place of each orbit puts the classes compared by the closing chain on one line.
* `InverseGalois.CFT.placeFrobValue_mul_eq_one_of_isotropic`,
  `InverseGalois.CFT.localClassHom_mul_eq_one_of_isotropic`: **the closing chain** for units
  ramified on the prescribed set as well.

## Tags

norm residue symbol, reciprocity, Frobenius, isotropic, cyclic, prescription, number field
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped Pointwise

/-! ### The symbol at a place where the two classes lie on one line -/

section Line

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **The norm residue symbol of two units whose classes at a place are powers of one class is
trivial there**, at an odd exponent. -/
theorem localSymbol_eq_one_of_localClassHom_mem_zpowers
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hodd : Odd n) (v : HeightOneSpectrum (𝓞 K)) {a b : Kˣ}
    {d : localClasses v n} (ha : localClassHom v n a ∈ Subgroup.zpowers d)
    (hb : localClassHom v n b ∈ Subgroup.zpowers d) :
    localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective)
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom b) = 1 :=
  (localClassPairing_eq_localSymbol hres hζ v a b).symm.trans
    (localClassPairing_eq_one_of_mem_zpowers hres hζ hodd v hb ha)

end Line

/-! ### Reciprocity outside a prescribed set -/

section Reciprocity

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **Reciprocity between two units each ramified at a single place outside a prescribed set**,
whose classes at every place of that set lie on one line.  The factors of the product formula at
the prescribed places vanish by isotropy, and the two remaining ones give the law. -/
theorem placeFrobValue_zpow_eq_zpow_of_isotropic (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {T : Finset (HeightOneSpectrum (𝓞 K))}
    {v w : HeightOneSpectrum (𝓞 K)} (hvw : v ≠ w) (hvT : v ∉ T) (hwT : w ∉ T)
    (hvn : ¬ P v ∣ n) (hwn : ¬ P w ∣ n) {a b : Kˣ}
    (ha : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ v → (n : ℤ) ∣ placeValue u a)
    (hb : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ w → (n : ℤ) ∣ placeValue u b)
    (hap : ∀ u : HeightOneSpectrum (𝓞 K), P u ∣ n →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ n = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom a)
    (hiso : ∀ u ∈ T, ∃ d : localClasses u n, localClassHom u n a ∈ Subgroup.zpowers d ∧
      localClassHom u n b ∈ Subgroup.zpowers d) :
    placeFrobValue hres hζ w a ^ placeValue w b
      = placeFrobValue hres hζ v b ^ placeValue v a := by
  classical
  have hS : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ ({v, w} : Finset (HeightOneSpectrum (𝓞 K))) →
      localSymbol (hres u) (isUnitValGen_one (valued_adicCompletion_surjective u))
        (hζ.map_of_injective (algebraMap K (u.adicCompletion K)).injective)
        (Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom a)
        (Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom b) = 1 := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    push_neg at hu
    by_cases huT : u ∈ T
    · obtain ⟨d, hda, hdb⟩ := hiso u huT
      exact localSymbol_eq_one_of_localClassHom_mem_zpowers hres hζ (hn.odd_of_ne_two hn2) u
        hda hdb
    · by_cases hun : P u ∣ n
      · exact localSymbol_eq_one_of_isPow_left _ _ _ (hap u hun) _
      · exact localSymbol_eq_one_of_dvd_of_dvd _ _ _ hn hun (ha u huT hu.1) (hb u huT hu.2)
  have hprod := prod_localSymbol_eq_one_of_ne_two hn hn2 hres hζ a b {v, w} hS
  rw [Finset.prod_pair hvw,
    localSymbol_eq_placeFrobValue_zpow_right hn hres hζ hvn (hb v hvT hvw) a,
    localSymbol_eq_placeFrobValue_zpow hn hres hζ hwn (ha w hwT (Ne.symm hvw)) b] at hprod
  exact (inv_mul_eq_one.mp hprod).symm

/-- **Reciprocity between two units each ramified at a single place outside a prescribed set**,
normalised: when the two values at the exceptional places agree modulo the exponent and are prime
to it, the values of each at the Frobenius automorphism of the other's place are equal. -/
theorem placeFrobValue_eq_placeFrobValue_of_isotropic (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {T : Finset (HeightOneSpectrum (𝓞 K))}
    {v w : HeightOneSpectrum (𝓞 K)} (hvw : v ≠ w) (hvT : v ∉ T) (hwT : w ∉ T)
    (hvn : ¬ P v ∣ n) (hwn : ¬ P w ∣ n) {a b : Kˣ}
    (ha : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ v → (n : ℤ) ∣ placeValue u a)
    (hb : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ w → (n : ℤ) ∣ placeValue u b)
    (hap : ∀ u : HeightOneSpectrum (𝓞 K), P u ∣ n →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ n = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom a)
    (hiso : ∀ u ∈ T, ∃ d : localClasses u n, localClassHom u n a ∈ Subgroup.zpowers d ∧
      localClassHom u n b ∈ Subgroup.zpowers d)
    {m : ℤ} (hm : IsCoprime m (n : ℤ)) (hav : placeValue v a ≡ m [ZMOD (n : ℤ)])
    (hbw : placeValue w b ≡ m [ZMOD (n : ℤ)]) :
    placeFrobValue hres hζ w a = placeFrobValue hres hζ v b := by
  have h := placeFrobValue_zpow_eq_zpow_of_isotropic hn hn2 hres hζ hvw hvT hwT hvn hwn ha hb
    hap hiso
  rw [zpow_eq_zpow_of_modEq (pow_placeFrobValue_eq_one hres hζ w a) hbw,
    zpow_eq_zpow_of_modEq (pow_placeFrobValue_eq_one hres hζ v b) hav] at h
  exact eq_of_zpow_eq_zpow_of_isCoprime (pow_placeFrobValue_eq_one hres hζ w a)
    (pow_placeFrobValue_eq_one hres hζ v b) hm h

end Reciprocity

/-! ### The closing chain -/

section Chain

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ} {T : Finset (HeightOneSpectrum (𝓞 K))}

omit [NeZero n] [NumberField K] in
/-- A place outside a set stable under the Galois group is moved to a place outside it. -/
theorem notMem_of_smul_stable (hT : ∀ (τ : Gal(K/k)) (u : HeightOneSpectrum (𝓞 K)),
    u ∈ T → τ • u ∈ T) (σ : Gal(K/k)) {u : HeightOneSpectrum (𝓞 K)} (hu : u ∉ T) : σ • u ∉ T :=
  fun hmem => hu (by simpa using hT σ⁻¹ _ hmem)

omit [NeZero n] in
/-- The image of a unit ramified only at one place and on a stable prescribed set is ramified only
at the image of that place and on the prescribed set. -/
theorem dvd_placeValue_galUnits_of_notMem
    (hT : ∀ (τ : Gal(K/k)) (u : HeightOneSpectrum (𝓞 K)), u ∈ T → τ • u ∈ T) (σ : Gal(K/k))
    {v : HeightOneSpectrum (𝓞 K)} {a : Kˣ}
    (ha : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ v → (n : ℤ) ∣ placeValue u a)
    (u : HeightOneSpectrum (𝓞 K)) (huT : u ∉ T) (hu : u ≠ σ • v) :
    (n : ℤ) ∣ placeValue u (galUnits σ a) := by
  have h := placeValue_galSmul (σ⁻¹ • u) σ a
  rw [smul_inv_smul] at h
  rw [h]
  exact ha _ (notMem_of_smul_stable hT σ⁻¹ huT) fun hv => hu (by rw [← hv, smul_inv_smul])

omit [NeZero n] [NumberField K] in
/-- A property holding at the images under an automorphism of the places of a stable set holds at
every place of that set. -/
theorem forall_mem_of_forall_mem_smul
    (hT : ∀ (τ : Gal(K/k)) (u : HeightOneSpectrum (𝓞 K)), u ∈ T → τ • u ∈ T) (σ : Gal(K/k))
    {Q : HeightOneSpectrum (𝓞 K) → Prop} (h : ∀ v ∈ T, Q (σ • v)) : ∀ u ∈ T, Q u := by
  intro u hu
  have h' := h (σ⁻¹ • u) (hT σ⁻¹ u hu)
  rwa [smul_inv_smul] at h'

omit [NeZero n] [NumberField K] in
/-- A unit of a number field is fixed by the trivial automorphism. -/
theorem galUnits_one_apply (a : Kˣ) : galUnits (1 : Gal(K/k)) a = a :=
  Units.ext (by rw [coe_galUnits_apply, AlgEquiv.one_apply])

omit [NeZero n] in
/-- **The classes compared by the closing chain lie on one line** when the prescription carried by
the two units is supported at no more than one place of each orbit of the prescribed set. -/
theorem exists_zpowers_of_prescription
    (hT : ∀ (τ : Gal(K/k)) (u : HeightOneSpectrum (𝓞 K)), u ∈ T → τ • u ∈ T) (σ : Gal(K/k))
    {cT : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n}
    (hfree : σ ≠ 1 → ∀ v ∈ T, cT (σ • v) = 1 ∨ cT v = 1)
    {a b : Kˣ} (ha : ∀ v ∈ T, localClassHom v n a = cT v)
    (hb : ∀ v ∈ T, localClassHom v n b = cT v) (u : HeightOneSpectrum (𝓞 K)) (hu : u ∈ T) :
    ∃ d : localClasses u n, localClassHom u n a ∈ Subgroup.zpowers d ∧
      localClassHom u n (galUnits σ a) ∈ Subgroup.zpowers d ∧
      localClassHom u n (galUnits σ b) ∈ Subgroup.zpowers d := by
  rcases eq_or_ne σ 1 with rfl | hσ
  · refine ⟨localClassHom u n a, Subgroup.mem_zpowers _, ?_, ?_⟩
    · rw [galUnits_one_apply]
      exact Subgroup.mem_zpowers _
    · rw [galUnits_one_apply, hb u hu, ← ha u hu]
      exact Subgroup.mem_zpowers _
  · revert u
    refine forall_mem_of_forall_mem_smul hT σ ?_
    intro v hv
    have hga : localClassHom (σ • v) n (galUnits σ a) = localClassesGalEquiv σ v n (cT v) := by
      rw [← localClassesGalEquiv_localClassHom, ha v hv]
    have hgb : localClassHom (σ • v) n (galUnits σ b) = localClassesGalEquiv σ v n (cT v) := by
      rw [← localClassesGalEquiv_localClassHom, hb v hv]
    rcases hfree hσ v hv with h | h
    · refine ⟨localClassesGalEquiv σ v n (cT v), ?_, ?_, ?_⟩
      · rw [ha _ (hT σ v hv), h]
        exact one_mem _
      · rw [hga]
        exact Subgroup.mem_zpowers _
      · rw [hgb]
        exact Subgroup.mem_zpowers _
    · refine ⟨cT (σ • v), ?_, ?_, ?_⟩
      · rw [ha _ (hT σ v hv)]
        exact Subgroup.mem_zpowers _
      · rw [hga, h, _root_.map_one]
        exact one_mem _
      · rw [hgb, h, _root_.map_one]
        exact one_mem _

/-- **The closing chain for units ramified on a prescribed set as well**: the product of the two
units supplied by the pigeonhole principle is trivial at the moved place.  The two applications of
the reciprocity law now absorb the prescribed places, where the classes compared lie on one
line. -/
theorem placeFrobValue_mul_eq_one_of_isotropic (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hT : ∀ (τ : Gal(K/k)) (u : HeightOneSpectrum (𝓞 K)), u ∈ T → τ • u ∈ T) {σ : Gal(K/k)}
    {Q R : HeightOneSpectrum (𝓞 K)} (hQσQ : Q ≠ σ • Q) (hQσR : Q ≠ σ • R) (hQT : Q ∉ T)
    (hRT : R ∉ T) (hQn : ¬ P Q ∣ n) (hσQn : ¬ P (σ • Q) ∣ n) (hσRn : ¬ P (σ • R) ∣ n)
    {zi zN : Kˣ}
    (hzi : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ Q → (n : ℤ) ∣ placeValue u zi)
    (hzN : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ R → (n : ℤ) ∣ placeValue u zN)
    (hziQ : IsCoprime (placeValue Q zi) (n : ℤ))
    (hzNR : placeValue R zN ≡ placeValue Q zi [ZMOD (n : ℤ)])
    (hzip : ∀ u : HeightOneSpectrum (𝓞 K), P u ∣ n →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ n = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom zi)
    (hiso : ∀ u ∈ T, ∃ d : localClasses u n, localClassHom u n zi ∈ Subgroup.zpowers d ∧
      localClassHom u n (galUnits σ zi) ∈ Subgroup.zpowers d ∧
      localClassHom u n (galUnits σ zN) ∈ Subgroup.zpowers d)
    (hpigeon : placeFrobValue hres hζ (σ • R) zN = placeFrobValue hres hζ (σ • Q) zi)
    (hcond : placeFrobValue hres hζ Q (galUnits σ zN)
      = (placeFrobValue hres hζ Q (galUnits σ zi))⁻¹) :
    placeFrobValue hres hζ (σ • R) (zi * zN) = 1 := by
  have h1 : placeFrobValue hres hζ (σ • Q) zi = placeFrobValue hres hζ Q (galUnits σ zi) :=
    placeFrobValue_eq_placeFrobValue_of_isotropic hn hn2 hres hζ hQσQ hQT
      (notMem_of_smul_stable hT σ hQT) hQn hσQn hzi
      (dvd_placeValue_galUnits_of_notMem hT σ hzi) hzip
      (fun u hu => (hiso u hu).imp fun _ h => ⟨h.1, h.2.1⟩) hziQ (Int.ModEq.refl _)
      (by rw [placeValue_galSmul])
  have h2 : placeFrobValue hres hζ (σ • R) zi = placeFrobValue hres hζ Q (galUnits σ zN) :=
    placeFrobValue_eq_placeFrobValue_of_isotropic hn hn2 hres hζ hQσR hQT
      (notMem_of_smul_stable hT σ hRT) hQn hσRn hzi
      (dvd_placeValue_galUnits_of_notMem hT σ hzN) hzip
      (fun u hu => (hiso u hu).imp fun _ h => ⟨h.1, h.2.2⟩) hziQ (Int.ModEq.refl _)
      (by rw [placeValue_galSmul]; exact hzNR)
  have hcond' : placeFrobValue hres hζ Q (galUnits σ zi)
      = (placeFrobValue hres hζ Q (galUnits σ zN))⁻¹ := by rw [hcond, inv_inv]
  rw [placeFrobValue_mul, hpigeon, h1, hcond', ← h2]
  exact mul_inv_cancel _

/-- **The closing chain for units ramified on a prescribed set as well, read on the classes**: the
product of the two units supplied by the pigeonhole principle is a power in the completion at the
moved place. -/
theorem localClassHom_mul_eq_one_of_isotropic (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hT : ∀ (τ : Gal(K/k)) (u : HeightOneSpectrum (𝓞 K)), u ∈ T → τ • u ∈ T) {σ : Gal(K/k)}
    {Q R : HeightOneSpectrum (𝓞 K)} (hQσQ : Q ≠ σ • Q) (hQσR : Q ≠ σ • R) (hRσR : R ≠ σ • R)
    (hQT : Q ∉ T) (hRT : R ∉ T) (hQn : ¬ P Q ∣ n) (hσQn : ¬ P (σ • Q) ∣ n)
    (hσRn : ¬ P (σ • R) ∣ n) {zi zN : Kˣ}
    (hzi : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ Q → (n : ℤ) ∣ placeValue u zi)
    (hzN : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ T → u ≠ R → (n : ℤ) ∣ placeValue u zN)
    (hziQ : IsCoprime (placeValue Q zi) (n : ℤ))
    (hzNR : placeValue R zN ≡ placeValue Q zi [ZMOD (n : ℤ)])
    (hzip : ∀ u : HeightOneSpectrum (𝓞 K), P u ∣ n →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ n = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom zi)
    (hiso : ∀ u ∈ T, ∃ d : localClasses u n, localClassHom u n zi ∈ Subgroup.zpowers d ∧
      localClassHom u n (galUnits σ zi) ∈ Subgroup.zpowers d ∧
      localClassHom u n (galUnits σ zN) ∈ Subgroup.zpowers d)
    (hpigeon : placeFrobValue hres hζ (σ • R) zN = placeFrobValue hres hζ (σ • Q) zi)
    (hcond : placeFrobValue hres hζ Q (galUnits σ zN)
      = (placeFrobValue hres hζ Q (galUnits σ zi))⁻¹) :
    localClassHom (σ • R) n (zi * zN) = 1 := by
  refine localClassHom_eq_one_of_placeFrobValue_eq_one hn hres hζ hσRn ?_
    (placeFrobValue_mul_eq_one_of_isotropic hn hn2 hres hζ hT hQσQ hQσR hQT hRT hQn hσQn hσRn
      hzi hzN hziQ hzNR hzip hiso hpigeon hcond)
  rw [placeValue_mul]
  exact dvd_add (hzi _ (notMem_of_smul_stable hT σ hRT) (Ne.symm hQσR))
    (hzN _ (notMem_of_smul_stable hT σ hRT) (Ne.symm hRσR))

end Chain

end InverseGalois.CFT
