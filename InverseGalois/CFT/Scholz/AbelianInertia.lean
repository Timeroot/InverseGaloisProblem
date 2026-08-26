/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Decomposition
import InverseGalois.CFT.Scholz.InertiaRankOne

/-!
# The rank one condition seen inside the decomposition group

At a prime over the residue characteristic the inertia subgroup is an `ℓ`-group and need not be
cyclic, so the cancellation the correcting twist needs cannot be read off the inertia subgroup
alone.  It can be read off the decomposition group.  Two features of the situation conspire.

First, a homomorphism of an `ℓ`-group carrying the inertia subgroup into a group of order `ℓ` has
central image there: the decomposition group permutes that image by an automorphism of a group of
prime order, and an `ℓ`-group cannot act nontrivially on such a group.  Second, the decomposition
group modulo inertia is the Galois group of an extension of finite residue fields, hence cyclic, and
a group with a cyclic quotient has all of its commutators already among the commutators with the
kernel.  Together these say that such a homomorphism factors through the abelianization of the
decomposition group.

What is left is a statement about an abelian group: the image of the inertia subgroup in the
abelianized decomposition group.  If that image is cyclic then every homomorphism of order `ℓ` on
the inertia subgroup is a power of any surjective one, which is the rank one condition.

## Main definitions

* `InverseGalois.CFT.IsAbelianInertiaCyclicAt`: the image of the inertia subgroup in the
  abelianization of the decomposition group at a prime over `ℓ` is cyclic.

## Main results

* `InverseGalois.CFT.commutator_eq_commutator_top_of_isCyclic_quotient`: a group with a cyclic
  quotient has commutator subgroup the commutators with the kernel of that quotient.
* `InverseGalois.CFT.commute_of_isPGroup_of_map_le`: a homomorphism of an `ℓ`-group carrying a
  normal subgroup into a subgroup of order `ℓ` has central image on that subgroup.
* `InverseGalois.CFT.isInertiaRankOneAt_of_isAbelianInertiaCyclicAt`: **cyclicity of the inertia
  subgroup in the abelianized decomposition group implies the rank one condition.**

## Tags

inertia subgroup, decomposition group, abelianization, `p`-group, Scholz condition
-/

open NumberField

open scoped Pointwise

namespace InverseGalois.CFT

attribute [local instance] Ideal.Quotient.field

/-! ### Commutators against a cyclic quotient -/

section GroupTheory

variable {H G : Type*} [Group H] [Group G]

/-- **A group with a cyclic quotient has no commutators beyond those with the kernel.**  Modulo the
commutators with the kernel the kernel becomes central, and a group with central kernel and cyclic
quotient is abelian. -/
theorem commutator_eq_commutator_top_of_isCyclic_quotient (N : Subgroup H) [N.Normal]
    [IsCyclic (H ⧸ N)] : commutator H = ⁅N, (⊤ : Subgroup H)⁆ := by
  have hKN : ⁅N, (⊤ : Subgroup H)⁆ ≤ N := Subgroup.commutator_le_left N ⊤
  haveI : (⁅N, (⊤ : Subgroup H)⁆).Normal := Subgroup.commutator_normal N ⊤
  have hcomm : ∀ a b : H ⧸ ⁅N, (⊤ : Subgroup H)⁆, a * b = b * a := by
    refine commutative_of_cyclic_center_quotient
      (QuotientGroup.map ⁅N, (⊤ : Subgroup H)⁆ N (MonoidHom.id H) hKN) ?_
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have haN : a ∈ N := by
      have hx' := MonoidHom.mem_ker.mp hx
      rw [QuotientGroup.map_mk] at hx'
      exact (QuotientGroup.eq_one_iff a).mp hx'
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      show (b * a)⁻¹ * (a * b) = ⁅a⁻¹, b⁻¹⁆ by group]
    exact Subgroup.commutator_mem_commutator (inv_mem haN) (Subgroup.mem_top _)
  refine le_antisymm ?_ (by rw [commutator_def]; exact Subgroup.commutator_mono le_top le_rfl)
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  have h1 : (QuotientGroup.mk' ⁅N, (⊤ : Subgroup H)⁆) ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hcomm _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

/-! ### A prime order image inside an `ℓ`-group -/

/-- **A homomorphism of an `ℓ`-group carrying a normal subgroup into a subgroup of order `ℓ` has
central image on that subgroup.**  Conjugation permutes the image, a group of prime order, and the
exponent by which it does so is a root of unity of order dividing both a power of `ℓ` and `ℓ - 1`,
hence trivial. -/
theorem commute_of_isPGroup_of_map_le {ℓ : ℕ} (hℓ : ℓ.Prime) (hH : IsPGroup ℓ H) {N : Subgroup H}
    [N.Normal] {C : Subgroup G} (hC : Nat.card ↥C = ℓ) (ρ : H →* G) (hρ : N.map ρ ≤ C) {n : H}
    (hn : n ∈ N) (h : H) : Commute (ρ n) (ρ h) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  by_cases hc1 : ρ n = 1
  · rw [Commute, SemiconjBy, hc1, one_mul, mul_one]
  have hcC : ρ n ∈ C := hρ ⟨n, hn, rfl⟩
  have hne : (⟨ρ n, hcC⟩ : ↥C) ≠ 1 := by
    simpa [Subtype.ext_iff] using hc1
  have hord : orderOf (ρ n) = ℓ := by
    have hdvd : orderOf (ρ n) ∣ ℓ := by
      have h0 : orderOf (⟨ρ n, hcC⟩ : ↥C) ∣ Nat.card ↥C := orderOf_dvd_natCard _
      rwa [hC, Subgroup.orderOf_mk] at h0
    exact ((Nat.dvd_prime hℓ).mp hdvd).resolve_left fun h1 => hc1 (orderOf_eq_one_iff.mp h1)
  -- conjugation multiplies the exponent by a fixed integer
  have hconjC : ρ h * ρ n * (ρ h)⁻¹ ∈ C := by
    have hmem : h * n * h⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹N.Normal› n hn h
    have := hρ ⟨h * n * h⁻¹, hmem, rfl⟩
    simpa [map_mul, map_inv] using this
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ρ n ^ k = ρ h * ρ n * (ρ h)⁻¹ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card (G := ↥C) hC hne (g' := ⟨ρ h * ρ n * (ρ h)⁻¹, hconjC⟩))
    exact ⟨k, congrArg Subtype.val hk⟩
  have hpow : ∀ m : ℕ, ρ h ^ m * ρ n * (ρ h ^ m)⁻¹ = ρ n ^ (k ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hsplit : ρ h ^ (m + 1) * ρ n * (ρ h ^ (m + 1))⁻¹
          = ρ h * (ρ h ^ m * ρ n * (ρ h ^ m)⁻¹) * (ρ h)⁻¹ := by
        rw [pow_succ']
        group
      rw [hsplit, ih, ← conj_zpow, ← hk, ← zpow_mul, pow_succ']
  -- the conjugating element has `ℓ`-power order, so the exponent is one modulo `ℓ`
  obtain ⟨s, hs⟩ := IsPGroup.iff_orderOf.mp hH h
  have hgpow : ρ h ^ ℓ ^ s = 1 := by
    rw [← map_pow, ← hs, pow_orderOf_eq_one, map_one]
  have hfix : ρ n ^ (k ^ ℓ ^ s) = ρ n ^ (1 : ℤ) := by
    have := hpow (ℓ ^ s)
    rw [hgpow, one_mul, inv_one, mul_one] at this
    rw [← this, zpow_one]
  have hmod : k ^ ℓ ^ s ≡ 1 [ZMOD (ℓ : ℤ)] := by
    have := zpow_eq_zpow_iff_modEq.mp hfix
    rwa [hord] at this
  have hk1 : k ≡ 1 [ZMOD (ℓ : ℤ)] := by
    have h1 : ((k : ZMod ℓ)) ^ ℓ ^ s = 1 := by
      have h2 := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod
      push_cast at h2
      exact h2
    have h3 : ∀ (u : ZMod ℓ) (m : ℕ), u ^ ℓ ^ m = u := by
      intro u m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]
    rw [h3] at h1
    have h4 : ((k : ℤ) : ZMod ℓ) = ((1 : ℤ) : ZMod ℓ) := by push_cast; exact h1
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mp h4
  have hfixed : ρ n ^ k = ρ n := by
    have := (zpow_eq_zpow_iff_modEq (x := ρ n) (m := k) (n := 1)).mpr (by rwa [hord])
    rw [this, zpow_one]
  have hcg : ρ n = ρ h * ρ n * (ρ h)⁻¹ := by rw [← hk, hfixed]
  show ρ n * ρ h = ρ h * ρ n
  conv_lhs => rw [hcg]
  group

/-- **A homomorphism of an `ℓ`-group into a group of order `ℓ` on a normal subgroup with cyclic
quotient kills the commutators.**  All the commutators are commutators with the normal subgroup, and
those are invisible because the image of the normal subgroup is central. -/
theorem eq_one_of_mem_commutator_of_isPGroup {ℓ : ℕ} (hℓ : ℓ.Prime) (hH : IsPGroup ℓ H)
    {N : Subgroup H} [N.Normal] [IsCyclic (H ⧸ N)] {C : Subgroup G} (hC : Nat.card ↥C = ℓ)
    (ρ : H →* G) (hρ : N.map ρ ≤ C) {w : H} (hw : w ∈ commutator H) : ρ w = 1 := by
  have hle : commutator H ≤ ρ.ker := by
    rw [commutator_eq_commutator_top_of_isCyclic_quotient N, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact commute_of_isPGroup_of_map_le hℓ hH hC ρ hρ hg₁ g₂
  exact hle hw

/-! ### Cancellation against a cyclic abelianized image -/

/-- **Two homomorphisms killing the commutators are dependent on a subgroup whose image in the
abelianization is cyclic.**  Everything is determined at a generator of that image, where the
hypothesis exhibits the first value as a power of the second. -/
theorem exists_zpow_mul_eq_one_of_isCyclic_abelianization {N : Subgroup H} {C : Subgroup G}
    (θ χ : H →* G) (hcyc : IsCyclic ↥(N.map (Abelianization.of : H →* Abelianization H)))
    (hθ1 : ∀ w ∈ commutator H, θ w = 1) (hχ1 : ∀ w ∈ commutator H, χ w = 1)
    (hθ : N.map θ ≤ C) (hχ : N.map χ = C) : ∃ a : ℤ, ∀ x ∈ N, θ x * χ x ^ a = 1 := by
  obtain ⟨j, hjgen⟩ := IsCyclic.exists_generator
    (α := ↥(N.map (Abelianization.of : H →* Abelianization H)))
  obtain ⟨σ₀, hσ₀N, hσ₀⟩ := j.2
  have key : ∀ x ∈ N, ∃ m : ℤ, θ x = θ σ₀ ^ m ∧ χ x = χ σ₀ ^ m := by
    intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (hjgen ⟨Abelianization.of x, ⟨x, hx, rfl⟩⟩)
    have hval : Abelianization.of σ₀ ^ m = Abelianization.of x := by
      have := congrArg Subtype.val hm
      rw [hσ₀]
      simpa using this
    have hker : σ₀ ^ m * x⁻¹ ∈ commutator H := by
      rw [← Abelianization.ker_of H, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hval,
        mul_inv_cancel]
    refine ⟨m, ?_, ?_⟩
    · have hθw := hθ1 _ hker
      rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at hθw
      exact hθw.symm
    · have hχw := hχ1 _ hker
      rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at hχw
      exact hχw.symm
  have hCz : C ≤ Subgroup.zpowers (χ σ₀) := by
    rw [← hχ]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, -, h2⟩ := key x hx
    exact ⟨m, h2.symm⟩
  obtain ⟨k, hk⟩ := hCz (hθ ⟨σ₀, hσ₀N, rfl⟩)
  refine ⟨-k, fun x hx => ?_⟩
  obtain ⟨m, h1, h2⟩ := key x hx
  rw [h1, h2, ← hk, ← zpow_mul, ← zpow_mul, ← zpow_add,
    show k * m + m * -k = 0 by ring, zpow_zero]

end GroupTheory

/-! ### The arithmetic input at the residue characteristic -/

variable {ℓ : ℕ}

/-- **Cyclic inertia in the abelianized decomposition group at the residue characteristic.**  At a
prime of a Galois number field lying over `ℓ`, the image of the inertia subgroup in the
abelianization of the decomposition group is cyclic. -/
def IsAbelianInertiaCyclicAt (ℓ : ℕ) : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (P : Ideal (𝓞 M)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(ℓ : ℤ)})],
      IsCyclic ↥(((Ideal.inertia Gal(M/ℚ) P).subgroupOf (MulAction.stabilizer Gal(M/ℚ) P)).map
        (Abelianization.of : ↥(MulAction.stabilizer Gal(M/ℚ) P) →*
          Abelianization ↥(MulAction.stabilizer Gal(M/ℚ) P)))

variable {M : Type} [Field M] [NumberField M] [IsGalois ℚ M]

omit [IsGalois ℚ M] in
/-- **The decomposition group modulo inertia is cyclic**, being a subgroup of the Galois group of an
extension of finite residue fields. -/
theorem isCyclic_stabilizer_quotient_inertia (hℓ : ℓ.Prime) (P : Ideal (𝓞 M)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(ℓ : ℤ)})] :
    IsCyclic (↥(MulAction.stabilizer Gal(M/ℚ) P) ⧸
      (Ideal.inertia Gal(M/ℚ) P).subgroupOf (MulAction.stabilizer Gal(M/ℚ) P)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hPne : P ≠ ⊥ := ne_bot_of_liesOver ℓ P
  haveI := isMaximal_of_ne_bot P hPne
  haveI := finite_quotient_of_ne_bot P hPne
  haveI := isMaximal_under_of_ne_bot P hPne
  set f := Ideal.Quotient.stabilizerHom P (P.under ℤ) Gal(M/ℚ) with hf
  haveI : IsCyclic ↥f.range := inferInstance
  have hker : (Ideal.inertia Gal(M/ℚ) P).subgroupOf (MulAction.stabilizer Gal(M/ℚ) P) = f.ker :=
    (Ideal.Quotient.ker_stabilizerHom (G := Gal(M/ℚ)) P (P.under ℤ)).symm
  have e : (↥(MulAction.stabilizer Gal(M/ℚ) P) ⧸
      (Ideal.inertia Gal(M/ℚ) P).subgroupOf (MulAction.stabilizer Gal(M/ℚ) P)) ≃* ↥f.range :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange f)
  exact isCyclic_of_surjective e.symm e.symm.surjective

/-- **Cyclicity of the inertia subgroup in the abelianized decomposition group implies the rank one
condition.**  A homomorphism of an `ℓ`-group Galois group whose values on inertia at a prime over
`ℓ` lie in a group of order `ℓ` is central there, so on the decomposition group it kills the
commutators and only sees the abelianization, where the inertia subgroup is cyclic. -/
theorem isInertiaRankOneAt_of_isAbelianInertiaCyclicAt (hℓ : ℓ.Prime)
    (h : IsAbelianInertiaCyclicAt ℓ) : IsInertiaRankOneAt ℓ := by
  intro M _ _ _ hM P _ _ G _ C hC θ χ hθ hχ
  set D := MulAction.stabilizer Gal(M/ℚ) P with hD
  set I := Ideal.inertia Gal(M/ℚ) P with hI
  have hID : I ≤ D := Ideal.inertia_le_stabilizer P
  haveI : IsCyclic (↥D ⧸ I.subgroupOf D) := isCyclic_stabilizer_quotient_inertia hℓ P
  have hpgD : IsPGroup ℓ ↥D := hM.to_subgroup D
  -- transport the hypotheses to the decomposition group
  have hmap : ∀ (ρ : Gal(M/ℚ) →* G), I.map ρ ≤ C →
      (I.subgroupOf D).map (ρ.comp D.subtype) ≤ C := by
    rintro ρ hρ _ ⟨x, hx, rfl⟩
    exact hρ ⟨(x : Gal(M/ℚ)), Subgroup.mem_subgroupOf.mp hx, rfl⟩
  have hχD : (I.subgroupOf D).map (χ.comp D.subtype) = C := by
    refine le_antisymm (hmap χ hχ.le) ?_
    rw [← hχ]
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, hID hσ⟩, Subgroup.mem_subgroupOf.mpr hσ, rfl⟩
  have hkill : ∀ (ρ : Gal(M/ℚ) →* G), I.map ρ ≤ C →
      ∀ w ∈ commutator ↥D, (ρ.comp D.subtype) w = 1 := fun ρ hρ w hw =>
    eq_one_of_mem_commutator_of_isPGroup hℓ hpgD hC (ρ.comp D.subtype) (hmap ρ hρ) hw
  obtain ⟨a, ha⟩ := exists_zpow_mul_eq_one_of_isCyclic_abelianization
    (θ.comp D.subtype) (χ.comp D.subtype) (h M P) (hkill θ hθ) (hkill χ hχ.le)
    (hmap θ hθ) hχD
  exact ⟨a, fun σ hσ => ha ⟨σ, hID hσ⟩ (Subgroup.mem_subgroupOf.mpr hσ)⟩

end InverseGalois.CFT
