/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CharPlace
import InverseGalois.CFT.PoitouTate.ClosingChain
import InverseGalois.CFT.PoitouTate.SUnitPlace
import InverseGalois.CFT.PoitouTate.SUnitReduce
import InverseGalois.CFT.Units.PlaceTower
import InverseGalois.CFT.Units.SUnitAbove
import InverseGalois.CFT.Units.SplitPowNorm

/-!
# A finite set of completely split places detecting the `S`-units

The `S`-units of a number field are a finitely generated group, and modulo their `p`-th powers they
form a finite dimensional vector space over the field with `p` elements.  A linear functional on
that space is a character of the `S`-units killing their `p`-th powers, and such a character is
read off by the Frobenius automorphism at a single finite place, which can be taken completely
split in any prescribed auxiliary field and away from any prescribed finite set of places.

Running over a spanning family of functionals — the whole dual space will do — produces a finite
set of completely split places at which the local classes of an `S`-unit are jointly trivial only
when the `S`-unit is a `p`-th power in the auxiliary field.  **Those places detect the `S`-units.**

The set of `S`-units in play is allowed to grow, as long as the local classes stay trivial at the
places added: a unit whose class is trivial at a place has order there a multiple of `p`, so
dividing by a suitable `p`-th power moves it back into the smaller group of `S`-units without
changing any of its local classes.

## Main results

* `InverseGalois.CFT.powDualChar`: the character of a subgroup read off a linear functional on its
  quotient by `p`-th powers.
* `InverseGalois.CFT.exists_pow_eq_of_forall_powDualChar_eq_one`: **an element killed by every
  such character is a `p`-th power** in the subgroup.
* `InverseGalois.CFT.exists_sUnit_div_pow_of_forall_localClassHom_eq_one`: an `S`-unit for a larger
  set whose classes at the extra places are trivial is an `S`-unit for the smaller set times a
  `p`-th power.
* `InverseGalois.CFT.exists_finset_split_detecting_sUnits`: **a finite set of completely split
  places at which the local classes detect the `S`-units**, in the sense that an `S`-unit trivial
  at all of them is a `p`-th power in the auxiliary field.

## Tags

S-unit, Kummer theory, Frobenius, Chebotarev, completely split, detection, local class
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### The characters of a subgroup modulo its `p`-th powers -/

section DualChar

variable {G : Type*} [CommGroup G] {B : Subgroup G} {p : ℕ}

/-- **The character of a subgroup read off a linear functional on its quotient by `p`-th
powers.** -/
def powDualChar (f : Module.Dual (ZMod p) (Additive (powQuotient B p))) :
    ↥B →* Multiplicative (ZMod p) where
  toFun b := Multiplicative.ofAdd
    (f (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : ↥B →* ↥B).range b)))
  map_one' := by
    show Multiplicative.ofAdd
      (f (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : ↥B →* ↥B).range 1))) = 1
    rw [_root_.map_one, ofMul_one, _root_.map_zero, ofAdd_zero]
  map_mul' b c := by
    show Multiplicative.ofAdd
      (f (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : ↥B →* ↥B).range (b * c)))) = _
    rw [_root_.map_mul, ofMul_mul, _root_.map_add, ofAdd_add]

theorem powDualChar_apply (f : Module.Dual (ZMod p) (Additive (powQuotient B p))) (b : ↥B) :
    powDualChar f b = Multiplicative.ofAdd
      (f (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : ↥B →* ↥B).range b))) := rfl

/-- The characters attached to the linear functionals kill the `p`-th powers. -/
theorem powDualChar_eq_one_of_eq_pow (f : Module.Dual (ZMod p) (Additive (powQuotient B p)))
    {b y : ↥B} (h : b = y ^ p) : powDualChar f b = 1 := by
  have hmk : (QuotientGroup.mk' (powMonoidHom p : ↥B →* ↥B).range) b = 1 := by
    rw [h, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.2 ⟨y, powMonoidHom_apply p y⟩
  rw [powDualChar_apply, hmk, ofMul_one, _root_.map_zero, ofAdd_zero]

/-- **An element of a subgroup killed by every character attached to a linear functional on the
quotient by `p`-th powers is a `p`-th power** in the subgroup: the functionals separate the points
of a vector space over the field with `p` elements. -/
theorem exists_pow_eq_of_forall_powDualChar_eq_one (hp : p.Prime) {b : ↥B}
    (h : ∀ f : Module.Dual (ZMod p) (Additive (powQuotient B p)), powDualChar f b = 1) :
    ∃ y : ↥B, y ^ p = b := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzero : ∀ f : Module.Dual (ZMod p) (Additive (powQuotient B p)),
      f (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : ↥B →* ↥B).range b)) = 0 := by
    intro f
    have hf := h f
    rw [powDualChar_apply, ← ofAdd_zero] at hf
    exact Multiplicative.ofAdd.injective hf
  have hb0 := (Module.forall_dual_apply_eq_zero_iff (ZMod p) _).1 hzero
  have hb1 : (QuotientGroup.mk' (powMonoidHom p : ↥B →* ↥B).range) b = 1 :=
    Additive.ofMul.injective (hb0.trans ofMul_one.symm)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hb1
  obtain ⟨y, hy⟩ := hb1
  exact ⟨y, (powMonoidHom_apply p y).symm.trans hy⟩

end DualChar

/-! ### Shrinking the set of places an `S`-unit is taken from -/

section Shrink

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [NeZero p]

/-- **An `S`-unit for a larger set of places whose local classes at the extra places are trivial is
an `S`-unit for the smaller set times a `p`-th power.**  A trivial local class makes the order at
the place a multiple of `p`, and an element of the field with the corresponding orders outside the
smaller set clears them all at once. -/
theorem exists_sUnit_div_pow_of_forall_localClassHom_eq_one
    {Ts Tn : Finset (HeightOneSpectrum (𝓞 K))}
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Ts : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {u : Kˣ} (hu : u ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hloc : ∀ v ∈ Tn, v ∉ Ts → localClassHom v p u = 1) :
    ∃ a : Kˣ, u / a ^ p ∈ sUnits K (Ts : Set (HeightOneSpectrum (𝓞 K))) := by
  classical
  have hdvd : ∀ v ∉ (Ts : Set (HeightOneSpectrum (𝓞 K))),
      (p : ℤ) ∣ Rigidity.RET.ord K v ((u : Kˣ) : K) := by
    intro v hv
    by_cases hvn : v ∈ Tn
    · have h := dvd_placeValue_of_localClassHom_eq_one (hloc v hvn (fun hc => hv hc))
      rwa [placeValue_eq_neg_ord, dvd_neg] at h
    · rw [mem_sUnits.mp hu v (fun hc => hvn (Finset.mem_coe.1 hc))]
      exact dvd_zero _
  have hmc : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (if v ∈ Tn then Rigidity.RET.ord K v ((u : Kˣ) : K) / (p : ℤ) else 0) = 0 := by
    filter_upwards [Tn.finite_toSet.eventually_cofinite_notMem] with v hv
    exact if_neg fun hc => hv (Finset.mem_coe.2 hc)
  obtain ⟨a, ha⟩ :=
    hrepr (fun v => if v ∈ Tn then Rigidity.RET.ord K v ((u : Kˣ) : K) / (p : ℤ) else 0) hmc
  refine ⟨a, mem_sUnits.mpr fun v hv => ?_⟩
  have hane : ((a : Kˣ) : K) ≠ 0 := a.ne_zero
  have hcoe : ((u / a ^ p : Kˣ) : K) = ((u : Kˣ) : K) / (((a : Kˣ) : K) ^ p) := by
    push_cast
    ring
  have hav : Rigidity.RET.ord K v ((a : Kˣ) : K)
      = if v ∈ Tn then Rigidity.RET.ord K v ((u : Kˣ) : K) / (p : ℤ) else 0 := ha v hv
  have hordv : (p : ℤ) * Rigidity.RET.ord K v ((a : Kˣ) : K)
      = Rigidity.RET.ord K v ((u : Kˣ) : K) := by
    rw [hav]
    by_cases hvn : v ∈ Tn
    · rw [if_pos hvn, Int.mul_ediv_cancel' (hdvd v hv)]
    · rw [if_neg hvn, mul_zero,
        mem_sUnits.mp hu v (fun hc => hvn (Finset.mem_coe.1 hc))]
  rw [hcoe, Rigidity.RET.ord_div v (Units.ne_zero u) (pow_ne_zero p hane),
    Rigidity.RET.ord_pow v hane, hordv, sub_self]

end Shrink

/-! ### The completely split places detecting the `S`-units -/

section Detect

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A]
  {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] {p : ℕ} [NeZero p]
  {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

variable (Ω) in
/-- **A finite set of places, completely split in the auxiliary field, at which the local classes
detect the `S`-units**: an `S`-unit whose local class is trivial at every one of them is a `p`-th
power in the auxiliary field.

The `S`-units of the auxiliary field for the places above the prescribed finite set are a saturated
group with a finite quotient by its `p`-th powers, so the linear functionals on that quotient are a
finite family of characters separating its points, and each of them is read off by the Frobenius
automorphism at a completely split place chosen outside the prescribed set.  A unit of the smaller
field with trivial local class at such a place has trivial value at the Frobenius automorphism
there, so joint triviality of the local classes forces every character to vanish. -/
theorem exists_finset_split_detecting_sUnits (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    (T : Finset (HeightOneSpectrum (𝓞 k))) (Ts : Finset (HeightOneSpectrum (𝓞 K)))
    (hTsT : ∀ v ∈ Ts, primeUnder (𝓞 k) v ∈ T) :
    ∃ Tf : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v ∈ Tf, primeUnder (𝓞 k) v ∉ T) ∧ (∀ v ∈ Tf, ¬ Pc v ∣ p) ∧
      (∀ v ∈ Tf, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
        primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/k) W = ⊥) ∧
      ∀ u : Kˣ, u ∈ sUnits K (Ts : Set (HeightOneSpectrum (𝓞 K))) →
        (∀ v ∈ Tf, localClassHom v p u = 1) →
          ∃ y : (↥Ω)ˣ, Units.map (algebraMap K ↥Ω : K →* ↥Ω) u = y ^ p := by
  classical
  haveI : SMulCommClass Gal(↥Ω/k) (𝓞 k) (𝓞 ↥Ω) := smulCommClass_ringOfIntegers k ↥Ω
  -- the places of the auxiliary field above the prescribed set, and its units there
  have hXfin : {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T}.Finite :=
    finite_setOf_primeUnder_mem k T.finite_toSet
  have hXstab : ∀ (σ : Gal(↥Ω/k)) {w : HeightOneSpectrum (𝓞 ↥Ω)},
      w ∈ {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T} →
      σ • w ∈ {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T} := by
    intro σ w hw
    show primeUnder (𝓞 k) (σ • w) ∈ T
    rw [primeUnder_smul_eq]
    exact hw
  have hmap : ∀ u : Kˣ, u ∈ sUnits K (Ts : Set (HeightOneSpectrum (𝓞 K))) →
      Units.map (algebraMap K ↥Ω : K →* ↥Ω) u
        ∈ sUnits ↥Ω {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T} := by
    intro u hu
    refine sUnits_mono ?_ (map_mem_sUnits_of_mem_sUnits (M := ↥Ω) Ts hu)
    intro w hw
    show primeUnder (𝓞 k) w ∈ T
    rw [← primeUnder_primeUnder k K w]
    exact hTsT _ hw
  -- the quotient of those units by their `p`-th powers is finite
  haveI : Fintype ↥{w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T} := hXfin.fintype
  have hrange : Set.range (Subtype.val :
      ↥{w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T} → HeightOneSpectrum (𝓞 ↥Ω))
      = {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T} := Subtype.range_coe
  have hζΩ : IsPrimitiveRoot (algebraMap K ↥Ω ζ) p :=
    hζ.map_of_injective (algebraMap K ↥Ω).injective
  haveI : HasEnoughRootsOfUnity (↥Ω) p := ⟨⟨_, hζΩ⟩, rootsOfUnity.isCyclic (↥Ω) p⟩
  have hcard := card_powQuotient_sUnits (K := ↥Ω) (p := p)
    (ι := (Subtype.val : ↥{w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T} →
      HeightOneSpectrum (𝓞 ↥Ω))) Subtype.val_injective
  rw [hrange] at hcard
  haveI : Finite (powQuotient
      (sUnits ↥Ω {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T}) p) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  haveI : Finite (Additive (powQuotient
      (sUnits ↥Ω {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T}) p)) :=
    inferInstanceAs (Finite (powQuotient
      (sUnits ↥Ω {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T}) p))
  haveI : Finite (Module.Dual (ZMod p) (Additive (powQuotient
      (sUnits ↥Ω {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T}) p))) :=
    Finite.of_injective (fun f => (f : Additive (powQuotient
      (sUnits ↥Ω {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T}) p) → ZMod p))
      DFunLike.coe_injective
  haveI := Fintype.ofFinite (Module.Dual (ZMod p) (Additive (powQuotient
      (sUnits ↥Ω {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T}) p)))
  -- one completely split place for each linear functional
  have hex : ∀ f : Module.Dual (ZMod p) (Additive (powQuotient
      (sUnits ↥Ω {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T}) p)),
      ∃ V : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 k) V ∉ T ∧
        stabilizer Gal(↥Ω/k) V = ⊥ ∧ ¬ Pc (primeUnder (𝓞 K) V) ∣ p ∧
        ∀ (u : Kˣ) (hu : Units.map (algebraMap K ↥Ω : K →* ↥Ω) u
            ∈ sUnits ↥Ω {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T}),
          (p : ℤ) ∣ placeValue (primeUnder (𝓞 K) V) u →
            (placeFrobValue hres hζ (primeUnder (𝓞 K) V) u = 1 ↔
              ((zmodRootHom hζΩ).comp (powDualChar f)) ⟨_, hu⟩ = 1) := by
    intro f
    refine exists_place_frobValue_eq_one_iff_character_sUnits hp hXfin hXstab hζ hres le_rfl
      ((zmodRootHom hζΩ).comp (powDualChar f)) ?_ T
    intro b hb y hy
    have hyU : y ∈ sUnits ↥Ω {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T} :=
      mem_sUnits_of_pow_mem hp.ne_zero (hy ▸ hb)
    rw [MonoidHom.comp_apply,
      powDualChar_eq_one_of_eq_pow f (y := ⟨y, hyU⟩) (Subtype.ext hy), _root_.map_one]
  choose V hVT hVstab hVP hViff using hex
  refine ⟨Finset.image (fun f => primeUnder (𝓞 K) (V f)) Finset.univ, ?_, ?_, ?_, ?_⟩
  · rintro v hv
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hv
    rw [primeUnder_primeUnder k K (V f)]
    exact hVT f
  · rintro v hv
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hv
    exact hVP f
  · rintro v hv
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨V f, rfl, hVstab f⟩
  · intro u hu hloc
    have hmapU := hmap u hu
    have hchar : ∀ f : Module.Dual (ZMod p) (Additive (powQuotient
        (sUnits ↥Ω {w : HeightOneSpectrum (𝓞 ↥Ω) | primeUnder (𝓞 k) w ∈ T}) p)),
        powDualChar f ⟨_, hmapU⟩ = (1 : Multiplicative (ZMod p)) := by
      intro f
      have hmem : primeUnder (𝓞 K) (V f)
          ∈ Finset.image (fun f => primeUnder (𝓞 K) (V f)) Finset.univ :=
        Finset.mem_image.2 ⟨f, Finset.mem_univ f, rfl⟩
      have hcl := hloc _ hmem
      have hdvd : (p : ℤ) ∣ placeValue (primeUnder (𝓞 K) (V f)) u :=
        dvd_placeValue_of_localClassHom_eq_one hcl
      have hone : localClassHom (primeUnder (𝓞 K) (V f)) p u
          = localClassHom (primeUnder (𝓞 K) (V f)) p (1 : Kˣ) := by
        rw [hcl, _root_.map_one]
      have hfrob : placeFrobValue hres hζ (primeUnder (𝓞 K) (V f)) u = 1 := by
        rw [placeFrobValue_eq_of_localClassHom_eq hres hζ _ hone,
          ← placeFrobValueHom_apply hres hζ, _root_.map_one]
      have hΦ := (hViff f u hmapU hdvd).1 hfrob
      rw [MonoidHom.comp_apply] at hΦ
      exact injective_zmodRootHom hζΩ (hΦ.trans (_root_.map_one _).symm)
    obtain ⟨y, hy⟩ := exists_pow_eq_of_forall_powDualChar_eq_one hp hchar
    refine ⟨(y : (↥Ω)ˣ), ?_⟩
    have hval := congrArg Subtype.val hy
    rw [Subgroup.coe_pow] at hval
    exact hval.symm

end Detect

/-! ### The stable set of detecting places -/

section Stable

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A]
  {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [FiniteDimensional k ↥Ω] [IsGalois k ↥Ω]
  {p : ℕ} [NeZero p] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

omit [Normal k A] [IsAlgClosed A] [Algebra K A] [Normal k ↥Ω] [IsScalarTower K ↥Ω A] in
/-- **Every place of the intermediate field sitting over the place below a place of the top field
with trivial decomposition group carries such a place itself.**  Some place of the top field lies
over the given one, and the two places of the top field have the same place of the base below them,
so an automorphism over the base carries one to the other and conjugates the decomposition
groups. -/
theorem exists_primeUnder_eq_stabilizer_eq_bot {V : HeightOneSpectrum (𝓞 ↥Ω)}
    (hV : stabilizer Gal(↥Ω/k) V = ⊥) {v : HeightOneSpectrum (𝓞 K)}
    (hv : primeUnder (𝓞 k) v = primeUnder (𝓞 k) V) :
    ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/k) W = ⊥ := by
  haveI : IsGaloisGroup Gal(↥Ω/k) (𝓞 k) (𝓞 ↥Ω) :=
    IsGaloisGroup.of_isFractionRing Gal(↥Ω/k) (𝓞 k) (𝓞 ↥Ω) k ↥Ω
  obtain ⟨W, hW⟩ := exists_primeUnder_eq (𝓞 K) (𝓞 ↥Ω) v
  refine ⟨W, hW, ?_⟩
  have hbelow : primeUnder (𝓞 k) V = primeUnder (𝓞 k) W := by
    rw [← hv, ← hW, primeUnder_primeUnder k K W]
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_primeUnder_eq (A := 𝓞 k) (G := Gal(↥Ω/k)) hbelow
  rw [← hρ, stabilizer_smul_eq_stabilizer_map_conj, hV, Subgroup.map_bot]

variable (Ω) in
/-- **A finite set of places, stable under the Galois group of the base and completely split in the
auxiliary field, whose local classes detect the `S`-units of any larger set of places.**

The places detecting the `S`-units are finitely many, and taking every place of the field over the
same place of the base makes the set stable without disturbing either property: a conjugate place
sits over the same place of the base, so it lies outside the prescribed set as well, and it carries
a place of the auxiliary field with trivial decomposition group because the automorphisms over the
base act transitively on the places above a place of the base.

An `S`-unit for a larger set of places whose classes are trivial at every place added is, up to a
`p`-th power, an `S`-unit for the smaller set with the same classes everywhere, so the detection
applies to it unchanged. -/
theorem exists_finset_stable_split_detecting_sUnits (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    (T : Finset (HeightOneSpectrum (𝓞 k))) (Ts : Finset (HeightOneSpectrum (𝓞 K)))
    (hTsT : ∀ v ∈ Ts, primeUnder (𝓞 k) v ∈ T)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Ts : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v) :
    ∃ Tf : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v ∈ Tf, v ∉ Ts) ∧
      (∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tf → σ • v ∈ Tf) ∧
      (∀ v ∈ Tf, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
        primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/k) W = ⊥) ∧
      ∀ Tn : Finset (HeightOneSpectrum (𝓞 K)), Tf ⊆ Tn → ∀ u : Kˣ,
        u ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))) →
          (∀ v ∈ Tn, v ∉ Ts → localClassHom v p u = 1) →
            ∃ y : (↥Ω)ˣ, Units.map (algebraMap K ↥Ω : K →* ↥Ω) u = y ^ p := by
  classical
  haveI : SMulCommClass Gal(K/k) (𝓞 k) (𝓞 K) := smulCommClass_ringOfIntegers k K
  obtain ⟨Tf₀, hT₀, -, hsp₀, hdet₀⟩ :=
    exists_finset_split_detecting_sUnits Ω hp hζ hres T Ts hTsT
  have hfin : {v : HeightOneSpectrum (𝓞 K) |
      primeUnder (𝓞 k) v ∈ Tf₀.image (primeUnder (𝓞 k))}.Finite :=
    finite_setOf_primeUnder_mem k (Tf₀.image (primeUnder (𝓞 k))).finite_toSet
  have hmem : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ hfin.toFinset ↔
      ∃ w ∈ Tf₀, primeUnder (𝓞 k) w = primeUnder (𝓞 k) v := fun v => by
    rw [Set.Finite.mem_toFinset]
    exact Finset.mem_image
  have hsub : Tf₀ ⊆ hfin.toFinset := fun v hv => (hmem v).2 ⟨v, hv, rfl⟩
  refine ⟨hfin.toFinset, ?_, ?_, ?_, ?_⟩
  · intro v hv hc
    obtain ⟨w, hw, hwv⟩ := (hmem v).1 hv
    exact hT₀ w hw (hwv ▸ hTsT v hc)
  · intro σ v hv
    obtain ⟨w, hw, hwv⟩ := (hmem v).1 hv
    exact (hmem (σ • v)).2 ⟨w, hw, by rw [hwv, primeUnder_smul_eq]⟩
  · intro v hv
    obtain ⟨w, hw, hwv⟩ := (hmem v).1 hv
    obtain ⟨W, hW, hWbot⟩ := hsp₀ w hw
    exact exists_primeUnder_eq_stabilizer_eq_bot hWbot
      (by rw [← hwv, ← hW, primeUnder_primeUnder k K W])
  · intro Tn hTn u hu hloc
    obtain ⟨a, ha⟩ := exists_sUnit_div_pow_of_forall_localClassHom_eq_one hrepr hu hloc
    have hcl : ∀ v : HeightOneSpectrum (𝓞 K),
        localClassHom v p (u / a ^ p) = localClassHom v p u := by
      intro v
      rw [_root_.map_div, _root_.map_pow, pow_eq_one_of_quotient_range_powMonoidHom p _, div_one]
    have hone : ∀ v ∈ Tf₀, localClassHom v p (u / a ^ p) = 1 := by
      intro v hv
      rw [hcl v]
      exact hloc v (hTn (hsub hv)) (hT₀ v hv ∘ hTsT v)
    obtain ⟨y, hy⟩ := hdet₀ (u / a ^ p) ha hone
    have hua : (u / a ^ p) * a ^ p = u := div_mul_cancel u (a ^ p)
    refine ⟨y * Units.map (algebraMap K ↥Ω : K →* ↥Ω) a, ?_⟩
    rw [← hua, _root_.map_mul, hy, _root_.map_pow, mul_pow]

end Stable

end InverseGalois.CFT
