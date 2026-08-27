/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Extending a homomorphism from a normal subgroup with cyclic quotient

Let `θ : D →* G` be a homomorphism which sends a normal subgroup `I` of `D` into a central
subgroup `f.ker` of `G`, and suppose the quotient `D ⧸ I` is cyclic of an order that kills every
element of `G`.  Then the restriction of `θ` to `I` extends to a homomorphism `D →* G` whose image
lies entirely in `f.ker`.

The construction is a comparison of `θ` with a second homomorphism.  Choose a generator of the
quotient and a preimage `x` of it in `D`.  Because the quotient is cyclic and the order of `θ x`
divides its order, there is a homomorphism `D →* G` killing `I` and sending `x` to `θ x`.  It
agrees with `θ` after composing with `f`, since the two agree on `I` and at `x`, which generate
`D`; so the pointwise quotient of the two takes values in `f.ker`, and is a homomorphism because
`f.ker` is central.  On `I` the second homomorphism is trivial, so the quotient restricts to `θ`
there.

## Main results

* `InverseGalois.CFT.exists_monoidHom_apply_eq_of_forall_mem_zpowers`: **a homomorphism out of a
  cyclic group is prescribed freely on a generator**, subject to the order of the group killing the
  prescribed value.
* `InverseGalois.CFT.exists_monoidHom_range_le_ker_eqOn`: **a homomorphism into a central subgroup
  extends over a cyclic quotient**, when the order of the quotient kills the target group.

## Tags

cyclic quotient, central extension, decomposition group, inertia subgroup
-/

namespace InverseGalois.CFT

/-! ### Homomorphisms out of a cyclic group -/

/-- **A homomorphism out of a cyclic group is prescribed freely on a generator**, subject to the
only constraint there is: the order of the group has to kill the prescribed value. -/
theorem exists_monoidHom_apply_eq_of_forall_mem_zpowers {Q G : Type*} [Group Q] [Group G] {x : Q}
    (hx : ∀ y : Q, y ∈ Subgroup.zpowers x) {g : G} (hg : g ^ Nat.card Q = 1) :
    ∃ ρ : Q →* G, ρ x = g := by
  have hsurj : Function.Surjective (zpowersHom Q x) := fun y => by
    obtain ⟨k, hk⟩ := hx y
    exact ⟨Multiplicative.ofAdd k, hk⟩
  have hker : (zpowersHom Q x).ker ≤ (zpowersHom G g).ker := by
    intro a ha
    have hax : x ^ a.toAdd = 1 := MonoidHom.mem_ker.mp ha
    have hdvd : (orderOf x : ℤ) ∣ a.toAdd := orderOf_dvd_iff_zpow_eq_one.mpr hax
    rw [orderOf_eq_card_of_forall_mem_zpowers hx] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    have : g ^ a.toAdd = 1 := by
      rw [hc, zpow_mul, zpow_natCast, hg, one_zpow]
    exact MonoidHom.mem_ker.mpr this
  refine ⟨(zpowersHom Q x).liftOfRightInverseAux _ (Function.rightInverse_surjInv hsurj)
    (zpowersHom G g) hker, ?_⟩
  simpa using MonoidHom.liftOfRightInverseAux_comp_apply (zpowersHom Q x) _
    (Function.rightInverse_surjInv hsurj) (zpowersHom G g) hker (Multiplicative.ofAdd (1 : ℤ))

/-! ### Extending over a cyclic quotient -/

/-- **A homomorphism into a central subgroup extends over a cyclic quotient.**  If `θ` maps the
normal subgroup `I` into the central subgroup `f.ker`, and the order of the cyclic quotient
`D ⧸ I` kills every element of `G`, then `θ` agrees on `I` with a homomorphism defined on all of
`D` and taking values in `f.ker` throughout. -/
theorem exists_monoidHom_range_le_ker_eqOn {D G H : Type*} [Group D] [Group G] [Group H]
    {I : Subgroup D} [I.Normal] (hcyc : IsCyclic (D ⧸ I))
    (hexp : ∀ g : G, g ^ Nat.card (D ⧸ I) = 1) {f : G →* H} (hZ : f.ker ≤ Subgroup.center G)
    {θ : D →* G} (hI : ∀ σ ∈ I, θ σ ∈ f.ker) :
    ∃ μ : D →* G, μ.range ≤ f.ker ∧ ∀ σ ∈ I, μ σ = θ σ := by
  haveI := hcyc
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := D ⧸ I)
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective I y
  obtain ⟨ρ₀, hρ₀⟩ := exists_monoidHom_apply_eq_of_forall_mem_zpowers hy (hexp (θ x))
  set ρ : D →* G := ρ₀.comp (QuotientGroup.mk' I) with hρdef
  have hρI : ∀ σ ∈ I, ρ σ = 1 := by
    intro σ hσ
    have hone : (QuotientGroup.mk' I) σ = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hσ
    rw [hρdef, MonoidHom.comp_apply, hone, map_one]
  have hρx : ρ x = θ x := by rw [hρdef, MonoidHom.comp_apply, hx, hρ₀]
  have hgen : ∀ σ : D, ∃ τ ∈ I, ∃ k : ℤ, σ = τ * x ^ k := by
    intro σ
    obtain ⟨k, hk⟩ := hy ((QuotientGroup.mk' I) σ)
    have hk' : y ^ k = (QuotientGroup.mk' I) σ := hk
    refine ⟨σ * (x ^ k)⁻¹, ?_, k, by group⟩
    have hmem : σ * (x ^ k)⁻¹ ∈ (QuotientGroup.mk' I).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hx, hk', mul_inv_cancel]
    rwa [QuotientGroup.ker_mk'] at hmem
  have hfeq : ∀ σ : D, f (ρ σ) = f (θ σ) := by
    intro σ
    obtain ⟨τ, hτ, k, rfl⟩ := hgen σ
    simp only [map_mul, map_zpow]
    rw [hρI τ hτ, hρx, MonoidHom.mem_ker.mp (hI τ hτ), map_one]
  have hker : ∀ σ : D, θ σ * (ρ σ)⁻¹ ∈ f.ker := by
    intro σ
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfeq σ, mul_inv_cancel]
  refine ⟨MonoidHom.mk' (fun σ => θ σ * (ρ σ)⁻¹) ?_, ?_, ?_⟩
  · intro a b
    have hb : ∀ z : G, z * (θ b * (ρ b)⁻¹) = (θ b * (ρ b)⁻¹) * z :=
      Subgroup.mem_center_iff.mp (hZ (hker b))
    calc θ (a * b) * (ρ (a * b))⁻¹
        = θ a * ((θ b * (ρ b)⁻¹) * (ρ a)⁻¹) := by simp only [map_mul, mul_inv_rev]; group
      _ = θ a * ((ρ a)⁻¹ * (θ b * (ρ b)⁻¹)) := by rw [← hb ((ρ a)⁻¹)]
      _ = θ a * (ρ a)⁻¹ * (θ b * (ρ b)⁻¹) := by group
  · rintro _ ⟨σ, rfl⟩
    exact hker σ
  · intro σ hσ
    show θ σ * (ρ σ)⁻¹ = θ σ
    rw [hρI σ hσ, inv_one, mul_one]

/-- **A homomorphism into a central subgroup extends over a cyclic quotient whose order the order
of the target divides.**  This is the form in which the extension is used: the quotient is the
Galois group of a residue field extension, made large by enlarging the field. -/
theorem exists_monoidHom_range_le_ker_eqOn_of_card_dvd {D G H : Type*} [Group D] [Group G]
    [Finite G] [Group H] {I : Subgroup D} [I.Normal] (hcyc : IsCyclic (D ⧸ I))
    (hdvd : Nat.card G ∣ Nat.card (D ⧸ I)) {f : G →* H} (hZ : f.ker ≤ Subgroup.center G)
    {θ : D →* G} (hI : ∀ σ ∈ I, θ σ ∈ f.ker) :
    ∃ μ : D →* G, μ.range ≤ f.ker ∧ ∀ σ ∈ I, μ σ = θ σ :=
  exists_monoidHom_range_le_ker_eqOn hcyc
    (fun g => orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard g).trans hdvd)) hZ hI

end InverseGalois.CFT
