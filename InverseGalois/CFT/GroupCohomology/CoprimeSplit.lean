/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A central extension splitting over a subgroup of coprime index splits

A central extension `1 → N → E → G → 1` of finite groups which admits a section homomorphism over a
subgroup `U` of `G` whose index is coprime to the order of `N` admits a section homomorphism over
all of `G`.  The transfer homomorphism attached to the difference between the identity of `E` and
the given section over the preimage of `U` lands in `N`, and on `N` itself it is the `U.index`-th
power map; since that map is bijective on `N`, inverting it produces a retraction `E → N`, and
correcting the identity of `E` by that retraction gives a homomorphism killing `N` and inducing a
section over `G`.

This is the group-theoretic half of the descent from a cyclotomic field back to the base field in
the theory of embedding problems: an obstruction living in the second cohomology with coefficients
of order `ℓ` may be killed after adjoining the `ℓ`-th roots of unity, and the degree of that
adjunction divides `ℓ - 1`, hence is coprime to `ℓ`.

## Main results

* `InverseGalois.CFT.exists_splitting_of_coprime_index`: **a central extension of finite groups
  with a section homomorphism over a subgroup of index coprime to the order of the kernel has a
  section homomorphism.**
* `InverseGalois.CFT.nonempty_splitting_of_coprime_index`: the same statement phrased for a
  `GroupExtension` and its `Splitting`.

## Tags

group extension, central extension, transfer, splitting, coprime index, embedding problem
-/

namespace InverseGalois.CFT

open Subgroup

variable {E G : Type*} [Group E] [Group G] [Finite E]

/-- **A central extension of finite groups with a section homomorphism over a subgroup of index
coprime to the order of the kernel has a section homomorphism.**  The transfer of the difference
between the identity and the given section restricts to the `U.index`-th power map on the kernel;
inverting that power map turns the transfer into a retraction of `E` onto the kernel, and dividing
the identity of `E` by that retraction produces a homomorphism which kills the kernel and therefore
descends to a section over the quotient. -/
theorem exists_splitting_of_coprime_index
    (π : E →* G) (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    {U : Subgroup G} (hcop : Nat.Coprime U.index (Nat.card π.ker))
    (s : U →* E) (hs : ∀ u : U, π (s u) = u) :
    ∃ σ : G →* E, ∀ g, π (σ g) = g := by
  classical
  have hcen : ∀ a : E, a ∈ π.ker → ∀ x : E, a * x = x * a := fun a ha x =>
    (Subgroup.mem_center_iff.1 (hc ha) x).symm
  haveI : IsMulCommutative ↥π.ker := ⟨⟨fun a b => Subtype.ext (hcen a a.2 b)⟩⟩
  set P : Subgroup E := U.comap π with hP
  haveI : P.FiniteIndex := inferInstance
  have hPindex : P.index = U.index := Subgroup.index_comap_of_surjective U hπ
  have hmem : ∀ p : ↥P, (p : E) * (s ⟨π p, p.2⟩)⁻¹ ∈ π.ker := by
    intro p
    simp [MonoidHom.mem_ker, hs ⟨π p, p.2⟩]
  let ϕ : ↥P →* ↥π.ker :=
    { toFun := fun p => ⟨(p : E) * (s ⟨π p, p.2⟩)⁻¹, hmem p⟩
      map_one' := by
        refine Subtype.ext ?_
        have h1 : (⟨π ((1 : ↥P) : E), (1 : ↥P).2⟩ : U) = 1 := Subtype.ext (by simp)
        show ((1 : ↥P) : E) * (s ⟨π ((1 : ↥P) : E), (1 : ↥P).2⟩)⁻¹ = 1
        rw [h1, map_one, inv_one, mul_one]
        rfl
      map_mul' := by
        intro p q
        refine Subtype.ext ?_
        have hu : (⟨π ((p * q : ↥P) : E), (p * q : ↥P).2⟩ : U)
            = ⟨π p, p.2⟩ * ⟨π q, q.2⟩ := Subtype.ext (by push_cast; simp)
        show ((p : E) * q) * (s ⟨π ((p * q : ↥P) : E), (p * q : ↥P).2⟩)⁻¹
          = ((p : E) * (s ⟨π p, p.2⟩)⁻¹) * ((q : E) * (s ⟨π q, q.2⟩)⁻¹)
        rw [hu, map_mul, mul_inv_rev,
          mul_assoc (p : E) (s ⟨π (p : E), p.2⟩)⁻¹ ((q : E) * (s ⟨π (q : E), q.2⟩)⁻¹),
          ← hcen _ (hmem q) (s ⟨π (p : E), p.2⟩)⁻¹]
        group }
  have hϕker : ∀ p : ↥P, π (p : E) = 1 → (ϕ p : E) = (p : E) := by
    intro p hp
    have h1 : (⟨π (p : E), p.2⟩ : U) = 1 := Subtype.ext hp
    show (p : E) * (s ⟨π (p : E), p.2⟩)⁻¹ = (p : E)
    rw [h1, map_one, inv_one, mul_one]
  set ψ : E →* ↥π.ker := MonoidHom.transfer ϕ with hψ
  have hψker : ∀ a : ↥π.ker, ψ (a : E) = a ^ U.index := by
    intro a
    have key : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * (a : E) ^ k * g₀ ∈ P →
        g₀⁻¹ * (a : E) ^ k * g₀ = (a : E) ^ k := by
      intro k g₀ _
      rw [mul_assoc, hcen _ (pow_mem a.2 k) g₀, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hψ, MonoidHom.transfer_eq_pow ϕ (a : E) key]
    refine Subtype.ext ?_
    rw [hϕker _ (by rw [map_pow, MonoidHom.mem_ker.1 a.2, one_pow])]
    push_cast
    rw [hPindex]
  have hbij : Function.Bijective ((powMonoidHom U.index : ↥π.ker →* ↥π.ker)) :=
    Nat.Coprime.pow_left_bijective hcop.symm
  let ε : ↥π.ker ≃* ↥π.ker := MulEquiv.ofBijective (powMonoidHom U.index) hbij
  let ρ : E →* ↥π.ker := (ε.symm : ↥π.ker →* ↥π.ker).comp ψ
  have hρ : ∀ a : ↥π.ker, ρ (a : E) = a := by
    intro a
    show ε.symm (ψ (a : E)) = a
    rw [hψker a]
    exact ε.symm_apply_eq.2 rfl
  let θ : E →* E :=
    { toFun := fun e => e * ((ρ e : E))⁻¹
      map_one' := by simp
      map_mul' := by
        intro x y
        show x * y * ((ρ (x * y) : E))⁻¹ = (x * ((ρ x : E))⁻¹) * (y * ((ρ y : E))⁻¹)
        rw [map_mul, Subgroup.coe_mul, mul_inv_rev,
          mul_assoc x ((ρ x : E))⁻¹ (y * ((ρ y : E))⁻¹),
          ← mul_assoc ((ρ x : E))⁻¹ y ((ρ y : E))⁻¹,
          hcen _ (inv_mem (ρ x).2) y,
          hcen _ (inv_mem (ρ y).2) ((ρ x : E))⁻¹]
        group }
  have hθπ : ∀ e, π (θ e) = π e := by
    intro e
    show π (e * ((ρ e : E))⁻¹) = π e
    rw [map_mul, map_inv, MonoidHom.mem_ker.1 (ρ e).2, inv_one, mul_one]
  have hθker : ∀ a ∈ π.ker, θ a = 1 := by
    intro a ha
    show a * ((ρ a : E))⁻¹ = 1
    rw [hρ ⟨a, ha⟩]
    exact mul_inv_cancel a
  refine ⟨(QuotientGroup.lift π.ker θ hθker).comp
    (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.toMonoidHom, ?_⟩
  intro g
  obtain ⟨e, rfl⟩ := hπ g
  have he : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π e)
      = (e : E ⧸ π.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show π (QuotientGroup.lift π.ker θ hθker
    ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π e))) = π e
  rw [he]
  exact hθπ e

/-- **A central group extension of finite groups which splits over a subgroup of index coprime to
the order of the kernel splits.**  This is `exists_splitting_of_coprime_index` phrased for a
`GroupExtension`, whose kernel is the range of the inclusion. -/
theorem nonempty_splitting_of_coprime_index {N : Type*} [Group N]
    (S : GroupExtension N E G) (hc : S.inl.range ≤ Subgroup.center E)
    {U : Subgroup G} (hcop : Nat.Coprime U.index (Nat.card N))
    (s : U →* E) (hs : ∀ u : U, S.rightHom (s u) = u) :
    Nonempty S.Splitting := by
  have hker : S.rightHom.ker = S.inl.range := S.range_inl_eq_ker_rightHom.symm
  have hcard : Nat.card ↥S.rightHom.ker = Nat.card N := by
    rw [hker]
    exact (Nat.card_congr (MonoidHom.ofInjective S.inl_injective).toEquiv).symm
  obtain ⟨σ, hσ⟩ := exists_splitting_of_coprime_index S.rightHom S.rightHom_surjective
    (hker ▸ hc) (U := U) (by rwa [hcard]) s hs
  exact ⟨{ toMonoidHom := σ, rightInverse_rightHom := hσ }⟩

end InverseGalois.CFT
