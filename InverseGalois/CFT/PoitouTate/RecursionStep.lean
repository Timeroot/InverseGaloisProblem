/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.PlaceUniformiser
import InverseGalois.CFT.PoitouTate.SUnitCharacter
import InverseGalois.CFT.PoitouTate.SUnitReduce
import InverseGalois.CFT.PoitouTate.SplitClass
import InverseGalois.CFT.Units.SUnitAbove

/-!
# One step of the recursion prescribing local classes at a growing set of places

A prescription of local classes at a finite set of places of a number field is met by the class of
an `S`-unit as soon as it is orthogonal to the `S`-units satisfying the dual conditions.  The step
carried out here adds one place to the set, chosen so that the orthogonality is automatic: the
place is produced by the construction of a Chebotarev place for the character of the `S`-units cut
out by the prescription, so the value of that character at an `S`-unit is a fixed power, prime to
the exponent, of the value at the Frobenius automorphism of the new place.  Prescribing at the new
place a power of a uniformiser with the inverse exponent then makes the total pairing trivial, and
the resulting `S`-unit is ramified exactly at the new place.

Two auxiliary facts feed the step.  The character of the `S`-units is killed by every radicand of
the extension in which the places of the old set are split completely, which is what the character
construction demands of it; and an `S`-unit for the enlarged set whose value at the new place is
divisible by the exponent is an old `S`-unit times a power, which is invisible both to the
character and to the value at the Frobenius automorphism.

## Main results

* `InverseGalois.CFT.stabilizer_eq_bot_of_stabilizer_base_eq_bot`: a finite place with trivial
  decomposition group over the base has trivial decomposition group over an intermediate field.
* `InverseGalois.CFT.inv_placeFrobValue_zpow_mul_prescriptionChar_eq_one`: **the pairing at the new
  place cancels the prescription character** when the two exponents are inverse to one another.
* `InverseGalois.CFT.exists_place_sUnit_prescribed_of_rad`: **one step of the recursion** — a new
  place, outside the prescribed set and completely split, together with an `S`-unit meeting the
  prescription at the old places and ramified exactly at the new one, granted that the character
  of the `S`-units kills every radicand of the middle field.
* `InverseGalois.CFT.exists_place_sUnit_prescribed`: the same, for a prescription coming from a
  global `S`-unit away from the places at which the middle field splits completely.

## Tags

Chebotarev, uniformiser, norm residue symbol, Selmer group, S-unit, prescription, recursion
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### A trivial decomposition group survives a change of base field -/

section Restrict

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [NumberField L]

omit [NumberField L] in
variable (k) in
/-- The action of an automorphism over an intermediate field on the finite places is the action of
the same automorphism read over the base field. -/
theorem smul_restrictScalars_place (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 L)) :
    (σ.restrictScalars k) • v = σ • v := rfl

omit [NumberField L] in
/-- **A finite place whose decomposition group over the base field is trivial has trivial
decomposition group over an intermediate field**, the automorphisms over the intermediate field
being among those over the base. -/
theorem stabilizer_eq_bot_of_stabilizer_base_eq_bot {v : HeightOneSpectrum (𝓞 L)}
    (h : stabilizer Gal(L/k) v = ⊥) : stabilizer Gal(L/K) v = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun σ hσ => ?_
  have h1 : (σ.restrictScalars k) • v = v := by
    rw [smul_restrictScalars_place k σ v]
    exact hσ
  have h2 : σ.restrictScalars k = 1 := (Subgroup.eq_bot_iff_forall _).1 h _ h1
  refine AlgEquiv.restrictScalars_injective k ?_
  rw [h2]
  rfl

end Restrict

/-! ### The pairing at the new place cancels the prescription character -/

section Cancel

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **The pairing at a new place against a power of a uniformiser cancels the prescription
character at the old places**, when the two exponents are inverse to one another modulo the
exponent.  A unit for the enlarged set of places whose value at the new place is divisible by the
exponent differs from a unit for the old set by a power, which neither the prescription character
nor the value at the Frobenius automorphism sees. -/
theorem inv_placeFrobValue_zpow_mul_prescriptionChar_eq_one
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {Tn : Finset (HeightOneSpectrum (𝓞 K))}
    {Q : HeightOneSpectrum (𝓞 K)} (hQTn : Q ∉ Tn)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    (c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v n) {j j' : ℤ}
    (hjj' : j * j' ≡ 1 [ZMOD (n : ℤ)])
    (hjval : ∀ u ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))),
      placeFrobValue hres hζ Q u = prescriptionChar hres hζ Tn c u ^ j)
    {u : Kˣ} (hu : u ∈ sUnits K (insert Q (Tn : Set (HeightOneSpectrum (𝓞 K)))))
    (hdvd : (n : ℤ) ∣ placeValue Q u) :
    (placeFrobValue hres hζ Q u ^ j')⁻¹ * prescriptionChar hres hζ Tn c u = 1 := by
  obtain ⟨u₀, a, hu₀, rfl⟩ :=
    exists_mul_pow_mem_sUnits (p := n) (fun h => hQTn (Finset.mem_coe.1 h)) hrepr hu hdvd
  have hfrob : placeFrobValue hres hζ Q (u₀ * a ^ n) = placeFrobValue hres hζ Q u₀ := by
    rw [← placeFrobValueHom_apply hres hζ Q (u₀ * a ^ n), ← placeFrobValueHom_apply hres hζ Q u₀,
      _root_.map_mul, _root_.map_pow, pow_placeFrobValueHom_eq_one, mul_one]
  have hpres : prescriptionChar hres hζ Tn c (u₀ * a ^ n)
      = prescriptionChar hres hζ Tn c u₀ := by
    rw [_root_.map_mul, _root_.map_pow, pow_prescriptionChar_eq_one, mul_one]
  rw [hfrob, hpres, hjval u₀ hu₀, ← zpow_mul,
    zpow_eq_zpow_of_modEq (pow_prescriptionChar_eq_one hres hζ Tn c u₀) hjj', zpow_one,
    inv_mul_cancel]

end Cancel

/-! ### One step of the recursion -/

section Step

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A]
  {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω] {p : ℕ} [NeZero p]
  {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

omit [IsGalois K ↥Ω] in
/-- **One step of the recursion prescribing local classes.**  Outside a prescribed finite set of
places of the bottom field there is a place, completely split in the middle field, together with an
`S`-unit whose local classes meet the prescription at the old places and which is ramified exactly
at the new place.  The hypothesis is that the character of the `S`-units cut out by the
prescription is killed by every radicand of the middle field, which is what the construction of a
Chebotarev place demands of it; that construction then produces a place at which the character is
a fixed power, prime to the exponent, of the value at the Frobenius automorphism, and prescribing
at the new place a power of a uniformiser with the inverse exponent makes the total pairing
trivial, so the prescription is met. -/
theorem exists_place_sUnit_prescribed_of_rad (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    (Tk : Finset (HeightOneSpectrum (𝓞 k))) {Tn : Finset (HeightOneSpectrum (𝓞 K))}
    (hTk : ∀ v ∈ Tn, primeUnder (𝓞 k) v ∈ Tk)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ Tn)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hcunr : ∀ v ∈ Tn, c v ∈ localUnramified v p)
    (hrad : ∀ u ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))), ∀ y : (↥Ω)ˣ,
      Units.map (algebraMap K ↥Ω : K →* ↥Ω) u = y ^ p →
      prescriptionChar hres hζ Tn c u = 1) :
    ∃ V : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 k) V ∉ Tk ∧
      stabilizer Gal(↥Ω/k) V = ⊥ ∧ ¬ Pc (primeUnder (𝓞 K) V) ∣ p ∧
      primeUnder (𝓞 K) V ∉ Tn ∧
      ∃ z : Kˣ, z ∈ sUnits K (insert (primeUnder (𝓞 K) V)
          (Tn : Set (HeightOneSpectrum (𝓞 K)))) ∧
        (∀ v ∈ Tn, localClassHom v p z = c v) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ≠ primeUnder (𝓞 K) V →
          (p : ℤ) ∣ placeValue v z) ∧
        ¬ (p : ℤ) ∣ placeValue (primeUnder (𝓞 K) V) z := by
  classical
  haveI : IsGalois k ↥Ω := ⟨⟩
  -- the finite, Galois stable set of primes of the middle field above the prescribed set
  have hXfin : {w : HeightOneSpectrum (𝓞 ↥Ω) |
      primeUnder (𝓞 k) w ∈ (Tk : Set (HeightOneSpectrum (𝓞 k)))}.Finite :=
    finite_setOf_primeUnder_mem k Tk.finite_toSet
  have hXstab : ∀ (σ : Gal(↥Ω/k)) {v : HeightOneSpectrum (𝓞 ↥Ω)},
      v ∈ {w : HeightOneSpectrum (𝓞 ↥Ω) |
        primeUnder (𝓞 k) w ∈ (Tk : Set (HeightOneSpectrum (𝓞 k)))} →
      σ • v ∈ {w : HeightOneSpectrum (𝓞 ↥Ω) |
        primeUnder (𝓞 k) w ∈ (Tk : Set (HeightOneSpectrum (𝓞 k)))} := by
    intro σ v hv
    show primeUnder (𝓞 k) (σ • v) ∈ (Tk : Set (HeightOneSpectrum (𝓞 k)))
    rw [primeUnder_smul_eq]
    exact hv
  -- the `S`-units of the bottom field land among those of the middle field
  have hW : Subgroup.map (Units.map (algebraMap K ↥Ω : K →* ↥Ω))
        (sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
      ≤ sUnits ↥Ω {w : HeightOneSpectrum (𝓞 ↥Ω) |
          primeUnder (𝓞 k) w ∈ (Tk : Set (HeightOneSpectrum (𝓞 k)))} := by
    rintro _ ⟨u, hu, rfl⟩
    refine sUnits_mono ?_ (map_mem_sUnits_of_mem_sUnits (M := ↥Ω) Tn hu)
    intro w hw
    show primeUnder (𝓞 k) w ∈ (Tk : Set (HeightOneSpectrum (𝓞 k)))
    rw [← primeUnder_primeUnder k K w]
    exact Finset.mem_coe.2 (hTk _ hw)
  have hWval : ∀ u ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))),
      ∀ Q : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) Q ∉ Tk → (p : ℤ) ∣ placeValue Q u := by
    intro u hu Q hQ
    rw [placeValue_eq_zero_of_mem_sUnits hu fun h => hQ (hTk _ (Finset.mem_coe.1 h))]
    exact dvd_zero _
  -- the prescription character is killed by every radicand of the middle field
  have hχ : ∀ u : ↥(sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K)))),
      ((prescriptionChar hres hζ Tn c).comp
        (sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K)))).subtype) u ^ p = 1 :=
    fun u => pow_prescriptionChar_eq_one hres hζ Tn c (u : Kˣ)
  have hχpow : ∀ (u : ↥(sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))) (y : (↥Ω)ˣ),
      Units.map (algebraMap K ↥Ω : K →* ↥Ω) (u : Kˣ) = y ^ p →
      ((prescriptionChar hres hζ Tn c).comp
        (sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K)))).subtype) u = 1 :=
    fun u y hy => hrad (u : Kˣ) u.2 y hy
  -- the Chebotarev place
  obtain ⟨V, hVT, hVstab, hVP, j, hj, hjval⟩ :=
    exists_place_placeFrobValue_eq_zpow_character hp hXfin hXstab hζ hres hW Tk hWval
      ((prescriptionChar hres hζ Tn c).comp
        (sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K)))).subtype) hχ hχpow
  set Q : HeightOneSpectrum (𝓞 K) := primeUnder (𝓞 K) V with hQdef
  have hQTk : primeUnder (𝓞 k) Q ∉ Tk := by
    rw [hQdef, primeUnder_primeUnder k K V]
    exact hVT
  have hQTn : Q ∉ Tn := fun h => hQTk (hTk _ h)
  have hjval' : ∀ u ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))),
      placeFrobValue hres hζ Q u = prescriptionChar hres hζ Tn c u ^ j :=
    fun u hu => hjval ⟨u, hu⟩
  -- the exponent inverse to the one the Chebotarev place produces
  obtain ⟨s, t, hst⟩ := (Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd.2 hj
  have hjj' : j * t ≡ 1 [ZMOD (p : ℤ)] := Int.modEq_iff_dvd.2 ⟨s, by linear_combination -hst⟩
  have hjt : ¬ (p : ℤ) ∣ t := by
    intro hdvd
    have h1 : (p : ℤ) ∣ 1 := by simpa using dvd_add hjj'.dvd (hdvd.mul_left j)
    have hp1 : p ∣ 1 := by exact_mod_cast h1
    exact hp.ne_one (Nat.dvd_one.mp hp1)
  -- the enlarged set of places, and the prescription extended to it
  have hQS : Q ∈ insert Q Tn := Finset.mem_insert_self _ _
  have hrange : Set.range (Subtype.val : ↥(insert Q Tn) → HeightOneSpectrum (𝓞 K))
      = ((insert Q Tn : Finset (HeightOneSpectrum (𝓞 K))) :
        Set (HeightOneSpectrum (𝓞 K))) := Subtype.range_coe
  have hcoeS : ((insert Q Tn : Finset (HeightOneSpectrum (𝓞 K))) :
      Set (HeightOneSpectrum (𝓞 K))) = insert Q (Tn : Set (HeightOneSpectrum (𝓞 K))) :=
    Finset.coe_insert _ _
  have hsub : sUnits K (Set.range (Subtype.val : ↥(insert Q Tn) → HeightOneSpectrum (𝓞 K)))
      ≤ sUnits K (insert Q (Tn : Set (HeightOneSpectrum (𝓞 K)))) :=
    sUnits_mono (by rw [hrange, hcoeS])
  have hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 →
      v ∈ Set.range (Subtype.val : ↥(insert Q Tn) → HeightOneSpectrum (𝓞 K)) := by
    intro v hv
    rw [hrange]
    exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (hpTn v hv))
  have hrepr' : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range (Subtype.val : ↥(insert Q Tn) → HeightOneSpectrum (𝓞 K)),
        Rigidity.RET.ord K v (a : K) = m v := by
    intro m hm
    obtain ⟨a, ha⟩ := hrepr m hm
    refine ⟨a, fun v hv => ha v fun hvTn => hv ?_⟩
    rw [hrange]
    exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hvTn))
  set L : ∀ y : ↥(insert Q Tn), Subgroup (localClasses (y : HeightOneSpectrum (𝓞 K)) p) :=
    fun y => if (y : HeightOneSpectrum (𝓞 K)) ∈ Tn then ⊥
      else localUnramified (y : HeightOneSpectrum (𝓞 K)) p with hLdef
  set D : ∀ y : ↥(insert Q Tn), Subgroup (localClasses (y : HeightOneSpectrum (𝓞 K)) p) :=
    fun y => if (y : HeightOneSpectrum (𝓞 K)) ∈ Tn then ⊤
      else localUnramified (y : HeightOneSpectrum (𝓞 K)) p with hDdef
  set c' : (y : ↥(insert Q Tn)) → localClasses (y : HeightOneSpectrum (𝓞 K)) p :=
    fun y => if (y : HeightOneSpectrum (𝓞 K)) ∈ Tn then c (y : HeightOneSpectrum (𝓞 K))
      else placeUniformiserClass (y : HeightOneSpectrum (𝓞 K)) p t with hc'def
  have hLmem : ∀ y : ↥(insert Q Tn), (y : HeightOneSpectrum (𝓞 K)) ∈ Tn → L y = ⊥ := by
    intro y hy
    simp only [hLdef]
    exact if_pos hy
  have hLnot : ∀ y : ↥(insert Q Tn), (y : HeightOneSpectrum (𝓞 K)) ∉ Tn →
      L y = localUnramified (y : HeightOneSpectrum (𝓞 K)) p := by
    intro y hy
    simp only [hLdef]
    exact if_neg hy
  have hDmem : ∀ y : ↥(insert Q Tn), (y : HeightOneSpectrum (𝓞 K)) ∈ Tn → D y = ⊤ := by
    intro y hy
    simp only [hDdef]
    exact if_pos hy
  have hDnot : ∀ y : ↥(insert Q Tn), (y : HeightOneSpectrum (𝓞 K)) ∉ Tn →
      D y = localUnramified (y : HeightOneSpectrum (𝓞 K)) p := by
    intro y hy
    simp only [hDdef]
    exact if_neg hy
  have hc'mem : ∀ y : ↥(insert Q Tn), (y : HeightOneSpectrum (𝓞 K)) ∈ Tn →
      c' y = c (y : HeightOneSpectrum (𝓞 K)) := by
    intro y hy
    simp only [hc'def]
    exact if_pos hy
  have hc'not : ∀ y : ↥(insert Q Tn), (y : HeightOneSpectrum (𝓞 K)) ∉ Tn →
      c' y = placeUniformiserClass (y : HeightOneSpectrum (𝓞 K)) p t := by
    intro y hy
    simp only [hc'def]
    exact if_neg hy
  have hLD : ∀ y : ↥(insert Q Tn), (L y = ⊥ ∧ D y = ⊤) ∨
      (FinitePlace.mk (y : HeightOneSpectrum (𝓞 K)) ((p : ℕ) : K) = 1 ∧
        L y = localUnramified (y : HeightOneSpectrum (𝓞 K)) p ∧
        D y = localUnramified (y : HeightOneSpectrum (𝓞 K)) p) := by
    intro y
    by_cases hy : (y : HeightOneSpectrum (𝓞 K)) ∈ Tn
    · exact Or.inl ⟨hLmem y hy, hDmem y hy⟩
    · refine Or.inr ⟨?_, hLnot y hy, hDnot y hy⟩
      by_contra hcon
      exact hy (hpTn _ hcon)
  -- the prescription is orthogonal to the `S`-units satisfying the dual conditions
  set F : HeightOneSpectrum (𝓞 K) → Kˣ → Multiplicative QModZ := fun v u =>
    localClassPairing hres hζ v (localClassHom v p u)
      (if v ∈ Tn then c v else placeUniformiserClass v p t) with hFdef
  have horth : ∀ b ∈ selmerGroup (Subtype.val : ↥(insert Q Tn) → HeightOneSpectrum (𝓞 K)) p
        ⊓ Subgroup.pi Set.univ D,
      localSymbolPiPairing hres hζ
        (Subtype.val : ↥(insert Q Tn) → HeightOneSpectrum (𝓞 K)) b c' = 1 := by
    intro b hb
    obtain ⟨hbsel, hbD⟩ := Subgroup.mem_inf.1 hb
    obtain ⟨w, rfl⟩ := hbsel
    have hu : (w : Kˣ) ∈ sUnits K (insert Q (Tn : Set (HeightOneSpectrum (𝓞 K)))) := hsub w.2
    have hdvdQ : (p : ℤ) ∣ placeValue Q (w : Kˣ) := by
      have h := (Subgroup.mem_pi _).1 hbD ⟨Q, hQS⟩ (Set.mem_univ _)
      rw [hDnot ⟨Q, hQS⟩ hQTn] at h
      exact (localClassHom_mem_localUnramified_iff Q (w : Kˣ)).1 h
    have hFQ : F Q (w : Kˣ) = (placeFrobValue hres hζ Q (w : Kˣ) ^ t)⁻¹ := by
      simp only [hFdef, if_neg hQTn]
      exact localClassPairing_localClassHom_placeUniformiserClass hp hres hζ hVP hdvdQ t
    have hFTn : ∏ v ∈ Tn, F v (w : Kˣ) = prescriptionChar hres hζ Tn c (w : Kˣ) := by
      rw [prescriptionChar_apply]
      refine Finset.prod_congr rfl fun v hv => ?_
      simp only [hFdef, if_pos hv]
    rw [localSymbolPiPairing_eq_piPairing, piPairing_apply]
    calc ∏ y : ↥(insert Q Tn), localClassPairing hres hζ (y : HeightOneSpectrum (𝓞 K))
            (sUnitClassHom (Subtype.val : ↥(insert Q Tn) → HeightOneSpectrum (𝓞 K)) p w y)
            (c' y)
        = ∏ y : ↥(insert Q Tn), F (y : HeightOneSpectrum (𝓞 K)) (w : Kˣ) :=
          Finset.prod_congr rfl fun y _ => rfl
      _ = ∏ v ∈ insert Q Tn, F v (w : Kˣ) :=
          Finset.prod_coe_sort (insert Q Tn) fun v => F v (w : Kˣ)
      _ = F Q (w : Kˣ) * ∏ v ∈ Tn, F v (w : Kˣ) := Finset.prod_insert hQTn
      _ = 1 := by
          rw [hFQ, hFTn]
          exact inv_placeFrobValue_zpow_mul_prescriptionChar_eq_one hres hζ hQTn hrepr c hjj'
            hjval' hu hdvdQ
  -- the `S`-unit meeting the prescription
  obtain ⟨aa, haa, l, hl, hal⟩ := exists_sUnitClass_mul_eq_unramified hp hodd hres hζ
    (ι := (Subtype.val : ↥(insert Q Tn) → HeightOneSpectrum (𝓞 K))) Subtype.val_injective hnι
    hrepr' L D hLD horth
  obtain ⟨w, rfl⟩ := haa
  have hzmem : (w : Kˣ) ∈ sUnits K (insert Q (Tn : Set (HeightOneSpectrum (𝓞 K)))) := hsub w.2
  have hzTn : ∀ v ∈ Tn, localClassHom v p (w : Kˣ) = c v := by
    intro v hv
    have hvS : v ∈ insert Q Tn := Finset.mem_insert_of_mem hv
    have h := congrFun hal ⟨v, hvS⟩
    have hlv : l ⟨v, hvS⟩ = 1 := by
      have hmem := (Subgroup.mem_pi _).1 hl ⟨v, hvS⟩ (Set.mem_univ _)
      rw [hLmem ⟨v, hvS⟩ hv] at hmem
      exact Subgroup.mem_bot.1 hmem
    rw [Pi.mul_apply, hlv, hc'mem ⟨v, hvS⟩ hv] at h
    exact (mul_one _).symm.trans h
  have hzval : ∀ v : HeightOneSpectrum (𝓞 K), v ≠ Q → (p : ℤ) ∣ placeValue v (w : Kˣ) := by
    intro v hvQ
    by_cases hv : v ∈ Tn
    · have hcv := hcunr v hv
      rw [← hzTn v hv] at hcv
      exact (localClassHom_mem_localUnramified_iff v (w : Kˣ)).1 hcv
    · have hvnot : v ∉ insert Q (Tn : Set (HeightOneSpectrum (𝓞 K))) := by
        rw [Set.mem_insert_iff]
        rintro (rfl | h)
        · exact hvQ rfl
        · exact hv (Finset.mem_coe.1 h)
      rw [placeValue_eq_zero_of_mem_sUnits hzmem hvnot]
      exact dvd_zero _
  have hzQ : ¬ (p : ℤ) ∣ placeValue Q (w : Kˣ) := by
    have h := congrFun hal ⟨Q, hQS⟩
    have hlQ : l ⟨Q, hQS⟩ ∈ localUnramified Q p := by
      have hmem := (Subgroup.mem_pi _).1 hl ⟨Q, hQS⟩ (Set.mem_univ _)
      rw [hLnot ⟨Q, hQS⟩ hQTn] at hmem
      exact hmem
    rw [Pi.mul_apply, hc'not ⟨Q, hQS⟩ hQTn, sUnitClassHom_apply] at h
    exact not_dvd_placeValue_of_localClassHom_mul_eq hlQ hjt h
  exact ⟨V, hVT, hVstab, hVP, hQTn, (w : Kˣ), hzmem, hzTn, hzval, hzQ⟩

/-- **One step of the recursion prescribing local classes, for a prescription coming from a global
`S`-unit away from the places at which the middle field splits completely.**  There the character
of the `S`-units is killed by every radicand of the middle field for the concrete reason that a
radicand is already a power in the completion at a completely split place, so what is left is a
product of norm residue symbols of two `S`-units and the product formula applies. -/
theorem exists_place_sUnit_prescribed (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    (Tk : Finset (HeightOneSpectrum (𝓞 k))) {T Tn : Finset (HeightOneSpectrum (𝓞 K))}
    (hT : T ⊆ Tn) (hTk : ∀ v ∈ Tn, primeUnder (𝓞 k) v ∈ Tk)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ Tn)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hcunr : ∀ v ∈ Tn, c v ∈ localUnramified v p)
    {g : Kˣ} (hg : g ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hc : ∀ v ∈ T, c v = localClassHom v p g)
    (hsplit : ∀ v ∈ Tn, v ∉ T → ∃ w : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) w = v ∧ stabilizer Gal(↥Ω/k) w = ⊥) :
    ∃ V : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 k) V ∉ Tk ∧
      stabilizer Gal(↥Ω/k) V = ⊥ ∧ ¬ Pc (primeUnder (𝓞 K) V) ∣ p ∧
      primeUnder (𝓞 K) V ∉ Tn ∧
      ∃ z : Kˣ, z ∈ sUnits K (insert (primeUnder (𝓞 K) V)
          (Tn : Set (HeightOneSpectrum (𝓞 K)))) ∧
        (∀ v ∈ Tn, localClassHom v p z = c v) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ≠ primeUnder (𝓞 K) V →
          (p : ℤ) ∣ placeValue v z) ∧
        ¬ (p : ℤ) ∣ placeValue (primeUnder (𝓞 K) V) z := by
  have hp2 : p ≠ 2 := by omega
  have hsplitK : ∀ v ∈ Tn, v ∉ T → ∃ w : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) w = v ∧ stabilizer Gal(↥Ω/K) w = ⊥ := by
    intro v hv hvT
    obtain ⟨w, hw1, hw2⟩ := hsplit v hv hvT
    exact ⟨w, hw1, stabilizer_eq_bot_of_stabilizer_base_eq_bot hw2⟩
  refine exists_place_sUnit_prescribed_of_rad hp hodd hζ hres Tk hTk hpTn hrepr hcunr
    fun u hu y hy => ?_
  have hb : algebraMap K ↥Ω ((u : Kˣ) : K) = ((y : (↥Ω)ˣ) : ↥Ω) ^ p := by
    have hy' := congrArg Units.val hy
    rwa [Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val] at hy'
  exact prescriptionChar_eq_one_of_pow hp hp2 hres hζ hT subset_rfl hpTn hg hc hsplitK hu hb

end Step

end InverseGalois.CFT
