/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.InertiaBound
import InverseGalois.CFT.Kummer.RamifiedCyclotomicPlace
import InverseGalois.CFT.Scholz.AbelianInertiaTransport
import InverseGalois.CFT.Scholz.FixedFieldRamification
import InverseGalois.CFT.Units.PlaceRestrict

/-!
# The Frattini bound on inertia at the residue characteristic

Let `N` be a Galois number field containing a primitive `ℓ`-th root of unity `ζ`, and let `W` be a
prime of `N` above `ℓ`.  Write `S` for the decomposition group of `W` and `ρ` for the mod `ℓ`
cyclotomic character of `N`.  The fixed field `F` of `H = S ⊓ ker ρ` is a subextension in which the
prime below `W` has ramification index times residue degree the order of the image of `S` under
`ρ`, which is at most `ℓ - 1`.  Since `ζ - 1` divides `ℓ` to the depth `ℓ - 1`, the two invariants
are then pinned: the ramification index is exactly `ℓ - 1` and the residue degree is one.  In
particular `ρ` is surjective on `S`, so some `τ` in `S` raises `ζ` to a primitive root modulo `ℓ`.
Such a `τ` normalises `H`, hence descends to an automorphism `δ` of `F` fixing the place below `W`.

That is exactly the local datum needed for the Kummer-theoretic dichotomy: any two characters of
`Gal(N/F)` with values in `ZMod ℓ` which are invariant under conjugation by `τ` are dependent on
the inertia subgroup of `W`.  Conjugation invariance is free when the characters are pulled back
from an abelian target containing the image of `τ`.  Transporting the dichotomy through a
homomorphism carrying the decomposition group into a subgroup `D` and the inertia subgroup onto an
`ℓ`-subgroup `I` — the missing `(ℓ - 1)`-st roots are supplied by the `ℓ`-group structure of `I` —
bounds the image of `I` in the Frattini quotient of the abelianization of `D` by `ℓ`.

## Main results

* `InverseGalois.CFT.fixedFieldAut`: the automorphism of the fixed field of a subgroup induced by
  an automorphism normalising that subgroup.
* `InverseGalois.CFT.card_map_abelianization_le_of_primitiveRoot`: **the image of inertia in the
  Frattini quotient of the abelianized decomposition group has order at most `ℓ`**, at a prime
  above `ℓ` of a Galois number field containing a primitive `ℓ`-th root of unity.

## Tags

inertia subgroup, decomposition group, Frattini quotient, cyclotomic character, Kummer theory
-/

open NumberField IntermediateField IsDedekindDomain

open scoped Pointwise

namespace InverseGalois.CFT

set_option synthInstance.maxHeartbeats 400000

/-! ### The fixed field of a normalised subgroup -/

section Normalise

variable {N : Type*} [Field N] [NumberField N]

/-- An automorphism normalising a subgroup carries its fixed field into itself. -/
theorem map_fixedField_le (U : Subgroup Gal(N/ℚ)) {σ : Gal(N/ℚ)}
    (h : ∀ u ∈ U, σ⁻¹ * u * σ ∈ U) :
    (fixedField U).map (σ : Gal(N/ℚ)).toAlgHom ≤ fixedField U := by
  have hσσ : ∀ y : N, σ (σ⁻¹ y) = y := fun y => by
    have hy : (σ * σ⁻¹) y = y := by rw [mul_inv_cancel]; rfl
    exact hy
  rintro _ ⟨x, hx, rfl⟩
  have hx2 : ∀ v ∈ U, v x = x := (IntermediateField.mem_fixedField_iff U x).mp hx
  refine (IntermediateField.mem_fixedField_iff U _).mpr fun u hu => ?_
  have hx' : σ⁻¹ (u (σ x)) = x := hx2 (σ⁻¹ * u * σ) (h u hu)
  have key := congrArg σ hx'
  rw [hσσ] at key
  exact key

/-- **An automorphism normalising a subgroup preserves its fixed field.** -/
theorem map_fixedField_eq (U : Subgroup Gal(N/ℚ)) {σ : Gal(N/ℚ)}
    (h : ∀ u ∈ U, σ⁻¹ * u * σ ∈ U) (h' : ∀ u ∈ U, σ * u * σ⁻¹ ∈ U) :
    (fixedField U).map (σ : Gal(N/ℚ)).toAlgHom = fixedField U := by
  have hσσ : ∀ y : N, σ (σ⁻¹ y) = y := fun y => by
    have hy : (σ * σ⁻¹) y = y := by rw [mul_inv_cancel]; rfl
    exact hy
  refine le_antisymm (map_fixedField_le U h) fun x hx => ?_
  have hmem : σ⁻¹ x ∈ fixedField U := by
    refine map_fixedField_le U (σ := σ⁻¹) (fun u hu => ?_) ⟨x, hx, rfl⟩
    simpa using h' u hu
  exact ⟨σ⁻¹ x, hmem, hσσ x⟩

variable [IsGalois ℚ N]

/-- **The automorphism of the fixed field of a subgroup induced by an automorphism normalising that
subgroup.** -/
noncomputable def fixedFieldAut (U : Subgroup Gal(N/ℚ)) {σ : Gal(N/ℚ)}
    (h : (fixedField U).map (σ : Gal(N/ℚ)).toAlgHom = fixedField U) :
    Gal(↥(fixedField U)/ℚ) :=
  (intermediateFieldMap σ (fixedField U)).trans (equivOfEq h)

omit [IsGalois ℚ N] in
@[simp]
theorem coe_fixedFieldAut (U : Subgroup Gal(N/ℚ)) {σ : Gal(N/ℚ)}
    (h : (fixedField U).map (σ : Gal(N/ℚ)).toAlgHom = fixedField U) (x : ↥(fixedField U)) :
    ((fixedFieldAut U h x : ↥(fixedField U)) : N) = σ (x : N) := rfl

omit [IsGalois ℚ N] in
/-- The induced automorphism of the fixed field is compatible with the inclusion of the integers of
the fixed field into the integers of the whole field. -/
theorem algebraMap_smul_fixedFieldAut (U : Subgroup Gal(N/ℚ)) {σ : Gal(N/ℚ)}
    (h : (fixedField U).map (σ : Gal(N/ℚ)).toAlgHom = fixedField U)
    (a : 𝓞 ↥(fixedField U)) :
    algebraMap (𝓞 ↥(fixedField U)) (𝓞 N) (fixedFieldAut U h • a)
      = σ • algebraMap (𝓞 ↥(fixedField U)) (𝓞 N) a := by
  apply RingOfIntegers.ext
  show algebraMap (↥(fixedField U)) N
      ((fixedFieldAut U h • a : 𝓞 ↥(fixedField U)) : ↥(fixedField U))
    = σ (algebraMap (↥(fixedField U)) N (a : ↥(fixedField U)))
  rfl

omit [IsGalois ℚ N] in
/-- **The prime of the fixed field below a moved prime is the moved prime below.** -/
theorem primeUnder_smul_fixedFieldAut (U : Subgroup Gal(N/ℚ)) {σ : Gal(N/ℚ)}
    (h : (fixedField U).map (σ : Gal(N/ℚ)).toAlgHom = fixedField U)
    (w : HeightOneSpectrum (𝓞 N)) :
    primeUnder (𝓞 ↥(fixedField U)) (σ • w)
      = fixedFieldAut U h • primeUnder (𝓞 ↥(fixedField U)) w := by
  have hinv : ∀ a : 𝓞 ↥(fixedField U),
      algebraMap (𝓞 ↥(fixedField U)) (𝓞 N) ((fixedFieldAut U h)⁻¹ • a)
        = σ⁻¹ • algebraMap (𝓞 ↥(fixedField U)) (𝓞 N) a := by
    intro a
    have hkey := algebraMap_smul_fixedFieldAut U h ((fixedFieldAut U h)⁻¹ • a)
    rw [smul_inv_smul] at hkey
    rw [hkey, inv_smul_smul]
  refine HeightOneSpectrum.ext ?_
  ext a
  rw [primeUnder_asIdeal, asIdeal_smul, asIdeal_smul, primeUnder_asIdeal, Ideal.under_def,
    Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.under_def, Ideal.mem_comap, hinv]

omit [IsGalois ℚ N] in
/-- The two actions on the integers of the whole field agree. -/
theorem fixedFieldHom_smul_ringOfIntegers (U : Subgroup Gal(N/ℚ))
    (σ : Gal(N/↥(fixedField U))) (y : 𝓞 N) : (fixedFieldHom U σ) • y = σ • y := rfl

omit [IsGalois ℚ N] in
/-- Membership in the inertia subgroup over the fixed field is membership in the inertia subgroup
over `ℚ`. -/
theorem mem_inertia_fixedFieldHom (U : Subgroup Gal(N/ℚ)) (P : Ideal (𝓞 N))
    {σ : Gal(N/↥(fixedField U))} (h : fixedFieldHom U σ ∈ Ideal.inertia Gal(N/ℚ) P) :
    σ ∈ Ideal.inertia Gal(N/↥(fixedField U)) P := by
  intro y
  have hy := h y
  rwa [fixedFieldHom_smul_ringOfIntegers] at hy

omit [IsGalois ℚ N] in
/-- Every element of a subgroup comes from the Galois group over its fixed field. -/
theorem exists_fixedFieldHom_eq (U : Subgroup Gal(N/ℚ)) {s : Gal(N/ℚ)} (hs : s ∈ U) :
    ∃ σ : Gal(N/↥(fixedField U)), fixedFieldHom U σ = s := by
  rw [← fixedFieldHom_range U] at hs
  exact hs

end Normalise

/-! ### Additive characters are invariant under conjugation -/

/-- An additive character of a group is unchanged by conjugation. -/
theorem eq_of_conj_of_add {Δ : Type*} [Group Δ] {ℓ : ℕ} (Θ : Δ → ZMod ℓ)
    (hΘ : ∀ x y : Δ, Θ (x * y) = Θ x + Θ y) (a b : Δ) : Θ (a⁻¹ * b * a) = Θ b := by
  have h1 : Θ 1 = 0 := by
    have h := hΘ 1 1
    rw [one_mul] at h
    linear_combination -h
  have hinv : ∀ c : Δ, Θ c⁻¹ = -Θ c := by
    intro c
    have h := hΘ c⁻¹ c
    rw [inv_mul_cancel, h1] at h
    linear_combination -h
  rw [hΘ (a⁻¹ * b) a, hΘ a⁻¹ b, hinv]
  ring

/-! ### The bound on the image of inertia -/

section Main

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N] {ℓ : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The image of inertia in the Frattini quotient of the abelianized decomposition group has
order at most `ℓ`.**  The two characters furnished by a hypothetical larger image become, after
passing to the fixed field of the intersection of the decomposition group with the kernel of the
cyclotomic character, two characters of the Galois group over a field in which the place below is a
cyclotomic place; there they are dependent on inertia. -/
theorem card_map_abelianization_le_of_primitiveRoot (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) {ζ : N}
    (hζ : IsPrimitiveRoot ζ ℓ) (W : Ideal (𝓞 N)) [W.IsPrime]
    [W.LiesOver (Ideal.span {(ℓ : ℤ)})] {G : Type*} [Group G] [Finite G] (f : Gal(N/ℚ) →* G)
    {D I : Subgroup G} (hIp : IsPGroup ℓ ↥I)
    (hD : ∀ x ∈ MulAction.stabilizer Gal(N/ℚ) W, f x ∈ D)
    (hI : (Ideal.inertia Gal(N/ℚ) W).map f = I) :
    Nat.card ↥(((I.subgroupOf D).map (Abelianization.of : ↥D →* Abelianization ↥D)).map
        (QuotientGroup.mk' (MonoidHom.range
          (powMonoidHom ℓ : Abelianization ↥D →* Abelianization ↥D)))) ≤ ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
  have hl2 : 2 ≤ ℓ := hℓ.two_le
  have hcardu : Nat.card (ZMod ℓ)ˣ = ℓ - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  -- the mod `ℓ` cyclotomic character and the fixed field of its kernel inside decomposition
  set ρ : Gal(N/ℚ) →* (ZMod ℓ)ˣ := hζ.autToPow ℚ with hρdef
  set S : Subgroup Gal(N/ℚ) := MulAction.stabilizer Gal(N/ℚ) W with hSdef
  set H : Subgroup Gal(N/ℚ) := S ⊓ ρ.ker with hHdef
  set F : IntermediateField ℚ N := fixedField H with hFdef
  haveI : NumberField ↥F := ⟨⟩
  haveI : IsGalois ↥F N := IsGalois.tower_top_of_isGalois ℚ ↥F N
  -- the root of unity lives in the fixed field
  have hζF : ζ ∈ F := by
    simp only [hFdef, mem_fixedField_iff]
    intro u hu
    have hu2 : u ∈ ρ.ker := (Subgroup.mem_inf.mp hu).2
    have hspec := hζ.autToPow_spec ℚ u
    rw [show (ρ u : ZMod ℓ) = 1 by rw [MonoidHom.mem_ker] at hu2; rw [hu2]; rfl,
      ZMod.val_one, pow_one] at hspec
    exact hspec.symm
  set ζF : ↥F := ⟨ζ, hζF⟩ with hζFdef
  have hmapζ : algebraMap ↥F N ζF = ζ := rfl
  have hζF' : IsPrimitiveRoot ζF ℓ :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥F N) (by rw [hmapζ]; exact hζ)
      (algebraMap ↥F N).injective
  -- the prime as a place
  have hW0 : W ≠ ⊥ := ne_bot_of_liesOver_natCast hℓ inferInstance
  set W' : HeightOneSpectrum (𝓞 N) := ⟨W, inferInstance, hW0⟩ with hW'def
  haveI := liesOver_under_intermediateField (p := ℓ) F W
  haveI : (primeUnder (𝓞 ↥F) W').asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)}) :=
    liesOver_under_intermediateField (p := ℓ) F W
  -- the ramification index times the residue degree is the order of the image of `ρ`
  have hHS : S ⊓ H = H := by rw [hHdef, ← inf_assoc, inf_idem]
  have hkerS : ρ.ker ⊓ S = H := by rw [hHdef, inf_comm]
  have hmaster := card_stabilizer_eq_card_inf_mul H hℓ W
  rw [hHS] at hmaster
  have hker := card_map_mul_card_inf_ker ρ S
  rw [hkerS] at hker
  have hHpos : 0 < Nat.card ↥H := Nat.card_pos
  have hprod : Ideal.ramificationIdx (algebraMap ℤ (𝓞 ↥F)) (Ideal.span {(ℓ : ℤ)})
        (W.under (𝓞 ↥F)) * (Ideal.span {(ℓ : ℤ)}).inertiaDeg (W.under (𝓞 ↥F))
      = Nat.card ↥(S.map ρ) := by
    refine Nat.eq_of_mul_eq_mul_left hHpos ?_
    rw [← hmaster, ← hker]
    ring
  have hcardle : Nat.card ↥(S.map ρ) ≤ ℓ - 1 := by
    rw [← hcardu]
    exact Subgroup.card_le_card_group _
  have hle : Ideal.ramificationIdx (algebraMap ℤ (𝓞 ↥F)) (Ideal.span {(ℓ : ℤ)})
        (W.under (𝓞 ↥F)) * (Ideal.span {(ℓ : ℤ)}).inertiaDeg (W.under (𝓞 ↥F)) ≤ ℓ - 1 := by
    rw [hprod]
    exact hcardle
  obtain ⟨hee, hff, hunif⟩ :=
    ramificationIdx_eq_of_mul_le hℓ hζF' (primeUnder (𝓞 ↥F) W') hle
  -- so the cyclotomic character is onto the decomposition group
  have hee' : Ideal.ramificationIdx (algebraMap ℤ (𝓞 ↥F)) (Ideal.span {(ℓ : ℤ)})
      (W.under (𝓞 ↥F)) = ℓ - 1 := hee
  have hff' : (Ideal.span {(ℓ : ℤ)}).inertiaDeg (W.under (𝓞 ↥F)) = 1 := hff
  have htop : S.map ρ = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [← hprod, hee', hff', mul_one, hcardu]
  -- a primitive root modulo `ℓ` is hit by some element of the decomposition group
  obtain ⟨g, hgu, hg, hg1⟩ := exists_primitiveRoot_natCast_isUnit hℓ hodd
  obtain ⟨τ, hτS, hτρ⟩ : ∃ t ∈ S, ρ t = hgu.unit := by
    have hmem : hgu.unit ∈ S.map ρ := by rw [htop]; exact Subgroup.mem_top _
    exact hmem
  have hτζ : τ ζ = ζ ^ g := by
    have hspec := hζ.autToPow_spec ℚ τ
    rw [show (ρ τ : ZMod ℓ) = ((g : ℕ) : ZMod ℓ) by rw [hτρ]; exact hgu.unit_spec,
      ZMod.val_natCast] at hspec
    have hmod : ζ ^ g = ζ ^ (g % ℓ) := by
      conv_lhs => rw [← Nat.div_add_mod g ℓ]
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
    rw [← hspec, hmod]
  -- that element normalises the subgroup, hence descends to the fixed field
  have hnorm : ∀ u ∈ H, τ⁻¹ * u * τ ∈ H := by
    intro u hu
    rw [hHdef, Subgroup.mem_inf] at hu ⊢
    refine ⟨mul_mem (mul_mem (inv_mem hτS) hu.1) hτS, ?_⟩
    simpa using (MonoidHom.normal_ker ρ).conj_mem u hu.2 τ⁻¹
  have hnorm' : ∀ u ∈ H, τ * u * τ⁻¹ ∈ H := by
    intro u hu
    rw [hHdef, Subgroup.mem_inf] at hu ⊢
    refine ⟨mul_mem (mul_mem hτS hu.1) (inv_mem hτS), ?_⟩
    exact (MonoidHom.normal_ker ρ).conj_mem u hu.2 τ
  have hFmap : (fixedField H).map (τ : Gal(N/ℚ)).toAlgHom = fixedField H :=
    map_fixedField_eq H hnorm hnorm'
  set δ : Gal(↥F/ℚ) := fixedFieldAut H hFmap with hδdef
  set δR : ↥F →+* ↥F := (δ : ↥F ≃ₐ[ℚ] ↥F).toAlgHom.toRingHom with hδRdef
  -- the induced automorphism fixes the place below and moves the root of unity correctly
  have hτW : τ • W' = W' := HeightOneSpectrum.ext hτS
  have hδv0 : δ • primeUnder (𝓞 ↥F) W' = primeUnder (𝓞 ↥F) W' := by
    have hkey := primeUnder_smul_fixedFieldAut H hFmap W'
    rw [hτW] at hkey
    exact hkey.symm
  have hδv : ∀ x : ↥F, (primeUnder (𝓞 ↥F) W').valuation ↥F (δR x)
      = (primeUnder (𝓞 ↥F) W').valuation ↥F x :=
    fun x => valuation_map_eq_of_smul_eq hδv0 x
  have hδζ : δR ζF = ζF ^ g := by
    refine Subtype.ext ?_
    show τ (ζF : N) = ((ζF ^ g : ↥F) : N)
    rw [SubmonoidClass.coe_pow]
    exact hτζ
  have hτcom : ∀ x : ↥F, (τ : N ≃+* N) (algebraMap ↥F N x) = algebraMap ↥F N (δR x) := fun _ => rfl
  have hcyc : IsCyclotomicPlace ℓ g ((primeUnder (𝓞 ↥F) W').valuation ↥F) (ζF - 1) δR
      (RingHom.id ↥F) :=
    isCyclotomicPlace_of_ringHom hℓ hζF' (primeUnder (𝓞 ↥F) W') hff hunif δR hδv hδζ hg hg1
  -- the homomorphism from the Galois group over the fixed field into `D`
  have hHle : H ≤ S := by rw [hHdef]; exact inf_le_left
  have hmemS : ∀ σ : Gal(N/↥F), fixedFieldHom H σ ∈ S := by
    intro σ
    refine hHle ?_
    have hmem : fixedFieldHom H σ ∈ (fixedFieldHom H).range := ⟨σ, rfl⟩
    rwa [fixedFieldHom_range H] at hmem
  set Ψ : Gal(N/↥F) →* ↥D :=
    MonoidHom.codRestrict (f.comp (fixedFieldHom H)) D (fun σ => hD _ (hmemS σ)) with hΨdef
  have hΨval : ∀ σ : Gal(N/↥F), (Ψ σ : G) = f (fixedFieldHom H σ) := fun _ => rfl
  -- every element of `I` inside `D` comes from an element of inertia over the fixed field
  have hcop1 : Nat.Coprime ℓ (ℓ - 1) :=
    hℓ.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hsurj : ∀ x : ↥D, (x : G) ∈ I →
      ∃ σ : Gal(N/↥F), σ ∈ Ideal.inertia Gal(N/↥F) W ∧ Ψ σ = x := by
    intro x hxI
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := ℓ) (G := ↥I)).mp hIp
    have hcop : (Nat.card ↥I).Coprime (ℓ - 1) := by
      rw [hk]
      exact Nat.Coprime.pow_left k hcop1
    set z : ↥I := (powCoprime hcop).symm ⟨(x : G), hxI⟩ with hzdef
    have hzm : (z : G) ^ (ℓ - 1) = (x : G) := by
      have happ : powCoprime hcop z = ⟨(x : G), hxI⟩ := Equiv.apply_symm_apply _ _
      rw [powCoprime_apply] at happ
      exact congrArg Subtype.val happ
    have hzI : (z : G) ∈ (Ideal.inertia Gal(N/ℚ) W).map f := by
      rw [hI]
      exact z.2
    obtain ⟨t, htI, hft⟩ := Subgroup.mem_map.mp hzI
    have htS : t ∈ S := Ideal.inertia_le_stabilizer W htI
    have htH : t ^ (ℓ - 1) ∈ H := by
      rw [hHdef, Subgroup.mem_inf]
      refine ⟨pow_mem htS _, ?_⟩
      rw [MonoidHom.mem_ker, map_pow, ← hcardu]
      exact pow_card_eq_one'
    obtain ⟨σ, hσ⟩ := exists_fixedFieldHom_eq H htH
    refine ⟨σ, mem_inertia_fixedFieldHom H W (by rw [hσ]; exact pow_mem htI _), ?_⟩
    refine Subtype.ext ?_
    rw [hΨval, hσ, map_pow, hft, hzm]
  -- the pair of characters is dependent on inertia
  refine card_map_abelianization_le hℓ (I.subgroupOf D) ?_
  intro Θ₁ Θ₂ hΘ₁ hΘ₂
  set χ₁ : Gal(N/↥F) → ZMod ℓ := fun σ => Θ₁ (Ψ σ) with hχ₁def
  set χ₂ : Gal(N/↥F) → ZMod ℓ := fun σ => Θ₂ (Ψ σ) with hχ₂def
  have hχ₁ : ∀ x y : Gal(N/↥F), χ₁ (x * y) = χ₁ x + χ₁ y := by
    intro x y
    simp only [hχ₁def, map_mul]
    exact hΘ₁ _ _
  have hχ₂ : ∀ x y : Gal(N/↥F), χ₂ (x * y) = χ₂ x + χ₂ y := by
    intro x y
    simp only [hχ₂def, map_mul]
    exact hΘ₂ _ _
  have hconj : ∀ σ : Gal(N/↥F), ∃ σ' : Gal(N/↥F),
      (∀ x : N, σ ((τ : N ≃+* N) x) = (τ : N ≃+* N) (σ' x)) ∧ χ₁ σ' = χ₁ σ ∧ χ₂ σ' = χ₂ σ := by
    intro σ
    have hsH : fixedFieldHom H σ ∈ H := by
      have hmem : fixedFieldHom H σ ∈ (fixedFieldHom H).range := ⟨σ, rfl⟩
      rwa [fixedFieldHom_range H] at hmem
    obtain ⟨σ', hσ'⟩ := exists_fixedFieldHom_eq H (hnorm _ hsH)
    have hcomm : ∀ x : N, σ ((τ : N ≃+* N) x) = (τ : N ≃+* N) (σ' x) := by
      intro x
      show fixedFieldHom H σ (τ x) = τ (fixedFieldHom H σ' x)
      rw [hσ']
      show fixedFieldHom H σ (τ x) = τ ((τ⁻¹ * fixedFieldHom H σ * τ) x)
      show fixedFieldHom H σ (τ x) = τ (τ⁻¹ (fixedFieldHom H σ (τ x)))
      have hy : (τ * τ⁻¹) (fixedFieldHom H σ (τ x)) = fixedFieldHom H σ (τ x) := by
        rw [mul_inv_cancel]; rfl
      exact hy.symm
    set d : ↥D := ⟨f τ, hD τ hτS⟩ with hddef
    have hΨ' : Ψ σ' = d⁻¹ * Ψ σ * d := by
      refine Subtype.ext ?_
      rw [hΨval, hσ']
      push_cast [hddef, hΨval]
      rw [map_mul, map_mul, map_inv]
    exact ⟨σ', hcomm, by rw [hχ₁def]; simp only [hΨ']; exact eq_of_conj_of_add Θ₁ hΘ₁ d (Ψ σ),
      by rw [hχ₂def]; simp only [hΨ']; exact eq_of_conj_of_add Θ₂ hΘ₂ d (Ψ σ)⟩
  have hdich := inertia_character_dependent (K := ↥F) (M := N) hζF' (τ : N ≃+* N) δR hτcom hδζ W'
    hcyc χ₁ χ₂ hχ₁ hχ₂ hconj
  rcases hdich with hzero | ⟨j, hj⟩
  · left
    intro x hx
    obtain ⟨σ, hσin, hσΨ⟩ := hsurj x (Subgroup.mem_subgroupOf.mp hx)
    rw [← hσΨ]
    exact hzero σ hσin
  · right
    refine ⟨j, fun x hx => ?_⟩
    obtain ⟨σ, hσin, hσΨ⟩ := hsurj x (Subgroup.mem_subgroupOf.mp hx)
    rw [← hσΨ]
    exact hj σ hσin

end Main

end InverseGalois.CFT
