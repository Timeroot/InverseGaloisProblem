/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.RadicalRamIdx
import InverseGalois.CFT.Kummer.SupRadicalSplit
import InverseGalois.CFT.PoitouTate.GlobalClasses
import InverseGalois.CFT.PoitouTate.NormLocalPower
import InverseGalois.CFT.PoitouTate.SUnitReduce
import InverseGalois.CFT.PoitouTate.SplitClass

/-!
# The prescription character on a radicand split between two extensions

A radicand of a compositum of two extensions factors as a radicand of the first times a radicand
of the second, and the character prescribed by an assignment of local classes kills each factor
for its own reason.

The first factor is handled the way a radicand of a single extension is: at a place where the
first extension splits completely its local class is trivial, so the character is a product over
the places carrying the prescription, and there the prescription comes from a global unit, so the
product formula applies.  Carrying that argument out on classes rather than on units is what makes
it available here, because a factor of a radicand is no longer a unit away from the places in
play; all that survives is that its value is divisible by the exponent, which is exactly what the
class formulation asks for.

The second factor is handled by orthogonality instead.  Where the prescription is trivial there is
nothing to prove, and where it is not the place is one at which the second extension is unramified,
so the local class of the factor is unramified; the unramified classes at a place away from the
exponent are their own orthogonal complement, and at a place over the exponent the prescription is
again trivial.

## Main results

* `InverseGalois.CFT.prod_localClassPairing_eq_one_of_dvd_placeValue`: **the product formula for
  the pairing of local classes**, for two units whose values are divisible by the exponent outside
  a finite set carrying the places over it.
* `InverseGalois.CFT.prescriptionChar_eq_one_of_localClassHom_eq_one`: the prescription character
  kills a unit whose local classes are trivial where the prescription is not carried by a global
  unit and whose values are divisible by the exponent outside the prescribed set.
* `InverseGalois.CFT.prescriptionChar_eq_one_of_dvd_placeValue`: the prescription character kills a
  unit unramified on the part of the prescribed set where the prescription is not trivial.
* `InverseGalois.CFT.prescriptionChar_eq_one_of_mul`: **the prescription character kills a product
  of two such units**, which is the shape a radicand of a compositum takes.
* `InverseGalois.CFT.prescriptionChar_eq_one_of_pow_mul`: the same, with the first factor given as
  a radicand of an extension splitting completely where the prescription is not carried by a
  global unit.
* `InverseGalois.CFT.prescriptionChar_eq_one_of_factor`: the same, with each factor given as a
  radicand of its own extension.
* `InverseGalois.CFT.prescriptionChar_eq_one_of_pow_sup`: **the prescription character kills every
  radicand of a compositum** of an extension splitting completely off the prescribed set and
  unramified outside it, with one whose Galois group is abelian of exponent the exponent and which
  is unramified on the part of the prescribed set away from the exponent.

## Tags

norm residue symbol, local class, unramified, product formula, compositum, radicand
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

/-! ### A radicand at an unramified place -/

section Unramified

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

/-- **The exponent divides the value of a radicand at a place unramified in the extension where it
becomes a power.**  The order of the radicand at the place above is the exponent times the order of
its root, and an unramified place above reads the same order as the place below. -/
theorem dvd_placeValue_of_pow_eq_of_ramIdx_eq_one {n : ℕ} (hn : n ≠ 0)
    (w : HeightOneSpectrum (𝓞 M)) (he : ramIdx (𝓞 K) w = 1) {x : Kˣ} {b : M}
    (hb : algebraMap K M (x : K) = b ^ n) :
    (n : ℤ) ∣ placeValue (primeUnder (𝓞 K) w) x := by
  have hx0 : ((x : Kˣ) : K) ≠ 0 := x.ne_zero
  have hxM : algebraMap K M ((x : Kˣ) : K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K M).injective).2 hx0
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hb
    exact hxM hb
  have h1 : ord M w (algebraMap K M ((x : Kˣ) : K))
      = ord K (primeUnder (𝓞 K) w) ((x : Kˣ) : K) := by
    rw [ord_algebraMap_eq_ramIdx_mul K w hx0, he, Nat.cast_one, one_mul]
  have h2 : ord M w (algebraMap K M ((x : Kˣ) : K)) = n * ord M w b := by
    rw [hb, ord_pow w hb0]
  rw [placeValue_eq_neg_ord]
  exact dvd_neg.2 ⟨ord M w b, by rw [← h1, h2]⟩

/-- **The exponent divides the value of a radicand at a place unramified in the extension where it
becomes a power**, stated with the unramifiedness of the place above. -/
theorem dvd_placeValue_of_pow_eq_of_isUnramifiedAt {n : ℕ} (hn : n ≠ 0)
    (w : HeightOneSpectrum (𝓞 M)) [Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal] {x : Kˣ} {b : M}
    (hb : algebraMap K M (x : K) = b ^ n) :
    (n : ℤ) ∣ placeValue (primeUnder (𝓞 K) w) x :=
  dvd_placeValue_of_pow_eq_of_ramIdx_eq_one hn w (ramIdx_eq_one_of_isUnramifiedAt w) hb

end Unramified

/-! ### The product formula on classes -/

section Product

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **Two classes of units unramified at a place away from the exponent pair trivially.**  The
unramified classes there are their own orthogonal complement, and a class is unramified exactly
when the exponent divides the value. -/
theorem localClassPairing_eq_one_of_dvd_placeValue
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) {v : HeightOneSpectrum (𝓞 K)}
    (hv : FinitePlace.mk v ((n : ℕ) : K) = 1) {a b : Kˣ}
    (ha : (n : ℤ) ∣ placeValue v a) (hb : (n : ℤ) ∣ placeValue v b) :
    localClassPairing hres hζ v (localClassHom v n a) (localClassHom v n b) = 1 := by
  have hmem : localClassHom v n a ∈ perpSubgroupLeft (A := localClasses v n)
      (localClassPairing hres hζ v) (localUnramified v n) := by
    rw [perpSubgroupLeft_localUnramified hres hζ hn hv]
    exact (localClassHom_mem_localUnramified_iff v a).2 ha
  exact mem_perpSubgroupLeft.1 hmem _ ((localClassHom_mem_localUnramified_iff v b).2 hb)

/-- **The product formula for the pairing of local classes.**  Over a finite set of places
containing those over the exponent, the pairings of the classes of two units whose values outside
the set are divisible by the exponent multiply to one: the pairing of classes is the norm residue
symbol, whose factors outside the set are trivial by the previous lemma, so the product over the
set is the product over all places. -/
theorem prod_localClassPairing_eq_one_of_dvd_placeValue (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ S)
    {a b : Kˣ} (ha : ∀ v ∉ S, (n : ℤ) ∣ placeValue v a)
    (hb : ∀ v ∉ S, (n : ℤ) ∣ placeValue v b) :
    ∏ v ∈ S, localClassPairing hres hζ v (localClassHom v n a) (localClassHom v n b) = 1 := by
  have hprod := prod_localSymbol_eq_one_of_ne_two hn hn2 hres hζ b a S ?_
  · simpa only [← localClassPairing_eq_localSymbol hres hζ] using hprod
  · intro v hvS
    have hnv : FinitePlace.mk v ((n : ℕ) : K) = 1 := by
      by_contra hcon
      exact hvS (hnS v hcon)
    rw [← localClassPairing_eq_localSymbol hres hζ]
    exact localClassPairing_eq_one_of_dvd_placeValue hres hζ hn hnv (ha v hvS) (hb v hvS)

end Product

/-! ### The two halves of the character -/

section Halves

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **The prescription character kills a unit whose classes are trivial off the part of the
prescription carried by a global unit.**  Those trivial classes let the product be taken over that
part alone, where the prescription is the class of a global unit, and then over the whole set
again; the product formula on classes finishes it, the global unit being a unit away from the
set. -/
theorem prescriptionChar_eq_one_of_localClassHom_eq_one (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {T Tn : Finset (HeightOneSpectrum (𝓞 K))} (hT : T ⊆ Tn)
    (hnTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Tn)
    {c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n} {g : Kˣ}
    (hg : g ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hc : ∀ v ∈ T, c v = localClassHom v n g)
    {u : Kˣ} (hu : ∀ v ∈ Tn, v ∉ T → localClassHom v n u = 1)
    (huout : ∀ v ∉ Tn, (n : ℤ) ∣ placeValue v u) :
    prescriptionChar hres hζ Tn c u = 1 := by
  classical
  have e1 : ∏ v ∈ T, localClassPairing hres hζ v (localClassHom v n u) (c v)
      = ∏ v ∈ Tn, localClassPairing hres hζ v (localClassHom v n u) (c v) :=
    Finset.prod_subset hT fun v hv hv0 => by
      rw [hu v hv hv0, _root_.map_one, MonoidHom.one_apply]
  rw [prescriptionChar_apply, ← e1]
  have e2 : ∏ v ∈ T, localClassPairing hres hζ v (localClassHom v n u) (c v)
      = ∏ v ∈ T, localClassPairing hres hζ v (localClassHom v n u) (localClassHom v n g) :=
    Finset.prod_congr rfl fun v hv => by rw [hc v hv]
  rw [e2]
  have e3 : ∏ v ∈ T, localClassPairing hres hζ v (localClassHom v n u) (localClassHom v n g)
      = ∏ v ∈ Tn, localClassPairing hres hζ v (localClassHom v n u) (localClassHom v n g) :=
    Finset.prod_subset hT fun v hv hv0 => by
      rw [hu v hv hv0, _root_.map_one, MonoidHom.one_apply]
  rw [e3]
  refine prod_localClassPairing_eq_one_of_dvd_placeValue hn hn2 hres hζ Tn hnTn huout
    fun v hv => ?_
  rw [placeValue_eq_zero_of_mem_sUnits hg fun h => hv (Finset.mem_coe.1 h)]
  exact dvd_zero _

/-- **The prescription character kills a unit unramified where the prescription is not trivial.**
Away from that part the factors disappear outright, and on it the class of the unit and the
prescribed class are both unramified at a place not dividing the exponent, where the unramified
classes are their own orthogonal complement; at a place dividing the exponent the prescription is
trivial again, so nothing is asked of the unit there. -/
theorem prescriptionChar_eq_one_of_dvd_placeValue (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {T Tn : Finset (HeightOneSpectrum (𝓞 K))}
    {c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n}
    (hcT : ∀ v ∈ Tn, v ∉ T → c v = 1) (hcunr : ∀ v ∈ T, c v ∈ localUnramified v n)
    (hcn : ∀ v ∈ T, FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → c v = 1)
    {u : Kˣ} (hu : ∀ v ∈ T, FinitePlace.mk v ((n : ℕ) : K) = 1 → (n : ℤ) ∣ placeValue v u) :
    prescriptionChar hres hζ Tn c u = 1 := by
  classical
  rw [prescriptionChar_apply]
  refine Finset.prod_eq_one fun v hv => ?_
  by_cases hvT : v ∈ T
  · by_cases hvn : FinitePlace.mk v ((n : ℕ) : K) = 1
    · have hmem : localClassHom v n u ∈ perpSubgroupLeft (A := localClasses v n)
          (localClassPairing hres hζ v) (localUnramified v n) := by
        rw [perpSubgroupLeft_localUnramified hres hζ hn hvn]
        exact (localClassHom_mem_localUnramified_iff v u).2 (hu v hvT hvn)
      exact mem_perpSubgroupLeft.1 hmem _ (hcunr v hvT)
    · rw [hcn v hvT hvn]
      exact _root_.map_one _
  · rw [hcT v hv hvT]
    exact _root_.map_one _

/-- **The prescription character kills a product of the two shapes of unit it kills.**  A radicand
of a compositum is such a product, one factor coming from each of the two extensions. -/
theorem prescriptionChar_eq_one_of_mul (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {T Tn : Finset (HeightOneSpectrum (𝓞 K))} (hT : T ⊆ Tn)
    (hnTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Tn)
    {c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n} {g : Kˣ}
    (hg : g ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hc : ∀ v ∈ T, c v = localClassHom v n g) (hcT : ∀ v ∈ Tn, v ∉ T → c v = 1)
    (hcunr : ∀ v ∈ T, c v ∈ localUnramified v n)
    (hcn : ∀ v ∈ T, FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → c v = 1)
    {u u₁ u₂ : Kˣ} (hu : u = u₁ * u₂)
    (h1 : ∀ v ∈ Tn, v ∉ T → localClassHom v n u₁ = 1)
    (h1out : ∀ v ∉ Tn, (n : ℤ) ∣ placeValue v u₁)
    (h2 : ∀ v ∈ T, FinitePlace.mk v ((n : ℕ) : K) = 1 → (n : ℤ) ∣ placeValue v u₂) :
    prescriptionChar hres hζ Tn c u = 1 := by
  rw [hu, _root_.map_mul,
    prescriptionChar_eq_one_of_localClassHom_eq_one hn hn2 hres hζ hT hnTn hg hc h1 h1out,
    prescriptionChar_eq_one_of_dvd_placeValue hn hres hζ hcT hcunr hcn h2, one_mul]

end Halves

/-! ### The first factor as a radicand -/

section Radicand

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] {n : ℕ} [NeZero n] {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **The prescription character kills a product whose first factor is a radicand of an extension
splitting completely off the part of the prescription carried by a global unit.**  At such a place
the decomposition group is trivial, so the radicand is already a power in the completion and its
local class there is trivial. -/
theorem prescriptionChar_eq_one_of_pow_mul (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {T Tn : Finset (HeightOneSpectrum (𝓞 K))} (hT : T ⊆ Tn)
    (hnTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Tn)
    {c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n} {g : Kˣ}
    (hg : g ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hc : ∀ v ∈ T, c v = localClassHom v n g) (hcT : ∀ v ∈ Tn, v ∉ T → c v = 1)
    (hcunr : ∀ v ∈ T, c v ∈ localUnramified v n)
    (hcn : ∀ v ∈ T, FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → c v = 1)
    (hsplit : ∀ v ∈ Tn, v ∉ T → ∃ w : HeightOneSpectrum (𝓞 M),
      primeUnder (𝓞 K) w = v ∧ stabilizer Gal(M/K) w = ⊥)
    {u u₁ u₂ : Kˣ} (hu : u = u₁ * u₂) {b : M} (hb : algebraMap K M (u₁ : K) = b ^ n)
    (h1out : ∀ v ∉ Tn, (n : ℤ) ∣ placeValue v u₁)
    (h2 : ∀ v ∈ T, FinitePlace.mk v ((n : ℕ) : K) = 1 → (n : ℤ) ∣ placeValue v u₂) :
    prescriptionChar hres hζ Tn c u = 1 := by
  refine prescriptionChar_eq_one_of_mul hn hn2 hres hζ hT hnTn hg hc hcT hcunr hcn hu
    (fun v hv hv0 => ?_) h1out h2
  obtain ⟨w, rfl, hw⟩ := hsplit v hv hv0
  exact localClassHom_eq_one_of_stabilizer_eq_bot (NeZero.ne n) hζ hw hb

end Radicand

/-! ### The two factors as radicands of two extensions -/

section Factor

variable {K M₁ M₂ : Type} [Field K] [NumberField K] [Field M₁] [NumberField M₁] [Algebra K M₁]
  [IsGalois K M₁] [Field M₂] [NumberField M₂] [Algebra K M₂] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **The prescription character kills a product of a radicand of one extension and a radicand of
another**, when the first extension splits completely where the prescription is not carried by a
global unit and is unramified outside the prescribed set, and the second is unramified on the part
of the prescribed set away from the exponent.  Splitting completely makes the local class of the
first factor trivial, while an unramified place reads the value of a radicand as a multiple of the
exponent. -/
theorem prescriptionChar_eq_one_of_factor (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {T Tn : Finset (HeightOneSpectrum (𝓞 K))} (hT : T ⊆ Tn)
    (hnTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Tn)
    {c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n} {g : Kˣ}
    (hg : g ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hc : ∀ v ∈ T, c v = localClassHom v n g) (hcT : ∀ v ∈ Tn, v ∉ T → c v = 1)
    (hcunr : ∀ v ∈ T, c v ∈ localUnramified v n)
    (hcn : ∀ v ∈ T, FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → c v = 1)
    (hsplit : ∀ v ∈ Tn, v ∉ T → ∃ w : HeightOneSpectrum (𝓞 M₁),
      primeUnder (𝓞 K) w = v ∧ stabilizer Gal(M₁/K) w = ⊥)
    (hram₁ : ∀ v ∉ Tn, ∃ w : HeightOneSpectrum (𝓞 M₁),
      primeUnder (𝓞 K) w = v ∧ ramIdx (𝓞 K) w = 1)
    (hram₂ : ∀ v ∈ T, FinitePlace.mk v ((n : ℕ) : K) = 1 → ∃ w : HeightOneSpectrum (𝓞 M₂),
      primeUnder (𝓞 K) w = v ∧ ramIdx (𝓞 K) w = 1)
    {u u₁ u₂ : Kˣ} (hu : u = u₁ * u₂) {y₁ : M₁} (hy₁ : algebraMap K M₁ (u₁ : K) = y₁ ^ n)
    {y₂ : M₂} (hy₂ : algebraMap K M₂ (u₂ : K) = y₂ ^ n) :
    prescriptionChar hres hζ Tn c u = 1 := by
  refine prescriptionChar_eq_one_of_pow_mul hn hn2 hres hζ hT hnTn hg hc hcT hcunr hcn hsplit
    hu hy₁ (fun v hv => ?_) (fun v hv hvn => ?_)
  · obtain ⟨w, rfl, hw⟩ := hram₁ v hv
    exact dvd_placeValue_of_pow_eq_of_ramIdx_eq_one hn.ne_zero w hw hy₁
  · obtain ⟨w, rfl, hw⟩ := hram₂ v hv hvn
    exact dvd_placeValue_of_pow_eq_of_ramIdx_eq_one hn.ne_zero w hw hy₂

end Factor

/-! ### A radicand of a compositum -/

section Compositum

variable {K M₁ M₂ L : Type} [Field K] [NumberField K] [Field M₁] [NumberField M₁] [Algebra K M₁]
  [IsGalois K M₁] [Field M₂] [NumberField M₂] [Algebra K M₂] [Normal K M₂] [Field L]
  [NumberField L] [Algebra K L] [IsGalois K L] [Algebra M₁ L] [IsScalarTower K M₁ L]
  [Algebra M₂ L] [IsScalarTower K M₂ L] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **The prescription character kills every radicand of a compositum of two extensions**, the
first splitting completely where the prescription is not carried by a global unit and unramified
outside the prescribed set, the second with abelian Galois group of exponent the exponent and
unramified on the part of the prescribed set away from the exponent.  The radicand factors as a
radicand of the first extension times a radicand of the second, and each factor is then killed for
its own reason. -/
theorem prescriptionChar_eq_one_of_pow_sup (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {T Tn : Finset (HeightOneSpectrum (𝓞 K))} (hT : T ⊆ Tn)
    (hnTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Tn)
    {c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n} {g : Kˣ}
    (hg : g ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hc : ∀ v ∈ T, c v = localClassHom v n g) (hcT : ∀ v ∈ Tn, v ∉ T → c v = 1)
    (hcunr : ∀ v ∈ T, c v ∈ localUnramified v n)
    (hcn : ∀ v ∈ T, FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → c v = 1)
    (hsup : (IsScalarTower.toAlgHom K M₁ L).fieldRange ⊔
      (IsScalarTower.toAlgHom K M₂ L).fieldRange = ⊤)
    (hcomm : ∀ σ τ : M₂ ≃ₐ[K] M₂, σ * τ = τ * σ) (hexp : ∀ σ : M₂ ≃ₐ[K] M₂, σ ^ n = 1)
    (hsplit : ∀ v ∈ Tn, v ∉ T → ∃ w : HeightOneSpectrum (𝓞 M₁),
      primeUnder (𝓞 K) w = v ∧ stabilizer Gal(M₁/K) w = ⊥)
    (hram₁ : ∀ v ∉ Tn, ∃ w : HeightOneSpectrum (𝓞 M₁),
      primeUnder (𝓞 K) w = v ∧ ramIdx (𝓞 K) w = 1)
    (hram₂ : ∀ v ∈ T, FinitePlace.mk v ((n : ℕ) : K) = 1 → ∃ w : HeightOneSpectrum (𝓞 M₂),
      primeUnder (𝓞 K) w = v ∧ ramIdx (𝓞 K) w = 1)
    {u : Kˣ} {b : L} (hb : algebraMap K L (u : K) = b ^ n) :
    prescriptionChar hres hζ Tn c u = 1 := by
  classical
  have φ₁ : M₁ ≃ₐ[K] ↥(IsScalarTower.toAlgHom K M₁ L).fieldRange :=
    AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M₁ L)
  have φ₂ : M₂ ≃ₐ[K] ↥(IsScalarTower.toAlgHom K M₂ L).fieldRange :=
    AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M₂ L)
  haveI : Normal K ↥(IsScalarTower.toAlgHom K M₁ L).fieldRange := Normal.of_algEquiv φ₁
  haveI : Normal K ↥(IsScalarTower.toAlgHom K M₂ L).fieldRange := Normal.of_algEquiv φ₂
  have e₂ := AlgEquiv.autCongr φ₂
  obtain ⟨b₁, b₂, hmul, ⟨x₁, hx₁, hx₁pow⟩, ⟨x₂, hx₂, hx₂pow⟩⟩ :=
    exists_mul_eq_pow_of_pow_mem_sup hn hζ hsup
      (fun σ τ => by simpa using congrArg e₂ (hcomm (e₂.symm σ) (e₂.symm τ)))
      (fun σ => by simpa using congrArg e₂ (hexp (e₂.symm σ)))
      (b := ((u : Kˣ) : K)) u.ne_zero hb.symm
  have hb₁ : b₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact u.ne_zero hmul
  have hb₂ : b₂ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul
    exact u.ne_zero hmul
  obtain ⟨y₁, hy₁⟩ := AlgHom.mem_fieldRange.1 hx₁
  obtain ⟨y₂, hy₂⟩ := AlgHom.mem_fieldRange.1 hx₂
  have hy₁' : algebraMap M₁ L y₁ = x₁ := hy₁
  have hy₂' : algebraMap M₂ L y₂ = x₂ := hy₂
  refine prescriptionChar_eq_one_of_factor hn hn2 hres hζ hT hnTn hg hc hcT hcunr hcn hsplit
    hram₁ hram₂ (u₁ := Units.mk0 b₁ hb₁) (u₂ := Units.mk0 b₂ hb₂) (by ext; simpa using hmul)
    (y₁ := y₁) ?_ (y₂ := y₂) ?_
  · refine (algebraMap M₁ L).injective ?_
    rw [← IsScalarTower.algebraMap_apply, _root_.map_pow, hy₁', hx₁pow, Units.val_mk0]
  · refine (algebraMap M₂ L).injective ?_
    rw [← IsScalarTower.algebraMap_apply, _root_.map_pow, hy₂', hx₂pow, Units.val_mk0]

end Compositum

end InverseGalois.CFT
