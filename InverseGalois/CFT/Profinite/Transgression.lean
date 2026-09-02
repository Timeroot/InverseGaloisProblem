/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.InfRes
import InverseGalois.CFT.GroupCohomology.Transgression

/-!
# Inflation and restriction in degree two for a topological group

Let `π` be a surjective smooth homomorphism from a topological group onto a discrete group, and let
the kernel act trivially on the coefficients.  A smooth two cocycle whose restriction to the kernel
is the coboundary of a smooth cochain, and whose transgression is the coboundary of a smooth
homomorphism, is inflated from the quotient.  This is the exactness of

  `1 → H²(Q, M) → H²(G, M) → H²(N, M)`

in the middle, in the relative form which asks the transgression to vanish rather than the whole
first cohomology of the kernel, and for continuous rather than abstract cochains.

The abstract statement corrects a cocycle by three successive twists, and each correction is built
by reading the decomposition of an element along its coset; so a correction is constant along any
normal subgroup of the kernel acting trivially along which its data is constant.  That is what makes
the argument continuous, but it has to be read in the right order: the subgroup along which the
first two corrections are constant can be chosen from the cocycle and its trivialisation, while the
third and fourth are constant only along a subgroup small enough for the trivialisation of the
transgression, which is produced by the first two.  The proof therefore shrinks twice, once before
the transgression is read and once after.

## Main results

* `InverseGalois.CFT.exists_comapH2_eq_of_transgression`: **a class of the second cohomology of a
  topological group whose restriction to the kernel of a smooth surjection onto a discrete group is
  trivial and whose transgression is trivial is inflated from the quotient.**

## Tags

profinite group, Galois cohomology, inflation, restriction, transgression, smooth cochain
-/

namespace InverseGalois.CFT

open groupCohomology

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q] [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction Q M]
variable {π : G →* Q} (hπ : ∀ (g : G) (m : M), g • m = π g • m)

/-- **A class of the second cohomology of a topological group whose restriction to the kernel of a
smooth surjection onto a discrete group is trivial and whose transgression is trivial is inflated
from the quotient.**  The kernel is asked to act trivially on the coefficients, which is the case of
an embedding problem split by the corresponding extension; the trivialisation of the restriction and
the trivialisation of the transgression are asked to be smooth, which is what keeps the corrections
smooth.  The transgression is asked to be trivial for every smooth cocycle trivial along the kernel,
since the correction proceeds by successive twists. -/
theorem exists_comapH2_eq_of_transgression (hsm : IsSmoothHom π) (hsurj : Function.Surjective π)
    (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a)
    {b : G → M} (hbs : IsSmooth₁ b)
    (hb : ∀ x ∈ π.ker, ∀ y ∈ π.ker, a (x, y) = x • b y / b (x * y) * b x)
    (htr : ∀ c : G × G → M, IsMulCocycle₂ c → IsSmooth₂ c →
      (∀ n ∈ π.ker, ∀ y : G, c (n, y) = 1) →
      ∃ φ : G → M, IsSmooth₁ φ ∧ (∀ x ∈ π.ker, ∀ y ∈ π.ker, φ (x * y) = φ x * φ y) ∧
        ∀ σ : G, ∀ x ∈ π.ker, transgression c σ x = σ • φ (σ⁻¹ * x * σ) / φ x) :
    ∃ x : SmoothH2 Q M, comapH2 π hπ hsm x = smoothH2Mk a ha has := by
  obtain ⟨K, hK, hKle⟩ : ∃ K : Subgroup G, IsOpenNormal K ∧ K ≤ π.ker := by
    obtain ⟨K, hK, hle⟩ := hsm ⊥ isOpenNormal_bot
    exact ⟨K, hK, fun x hx =>
      MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp (Subgroup.mem_comap.mp (hle hx)))⟩
  obtain ⟨s, hs, hsc, hs1⟩ := exists_cosetSection π.ker
  obtain ⟨R, hR, hRle, haR, hbR⟩ : ∃ R : Subgroup G, IsOpenNormal R ∧ R ≤ π.ker ∧
      (∀ x y : G, ∀ n ∈ R, ∀ m ∈ R, a (x * n, y * m) = a (x, y)) ∧
      (∀ g : G, ∀ n ∈ R, b (g * n) = b g) := by
    obtain ⟨N₁, hN₁, ha₁⟩ := has
    obtain ⟨N₂, hN₂, hb₁⟩ := hbs
    exact ⟨N₁ ⊓ N₂ ⊓ K, (hN₁.inf hN₂).inf hK, fun x hx => hKle hx.2,
      fun x y n hn m hm => ha₁ x y n hn.1.1 m hm.1.1, fun g n hn => hb₁ g n hn.1.2⟩
  obtain ⟨u₁, h₁, hi₁⟩ := exists_twist_eq_one_on_subgroup hb
  obtain ⟨u₂, h₂, hi₂⟩ :=
    exists_twist_eq_one_of_mem_left_of_section hs hsc hs1 (isMulCocycle₂_twist ha u₁) h₁
  rw [twist_twist] at h₂
  have hu₁R : ∀ g : G, ∀ n ∈ R, u₁ (g * n) = u₁ g := hi₁ R hRle hbR
  have hu₂R : ∀ g : G, ∀ n ∈ R, u₂ (g * n) = u₂ g :=
    hi₂ R hRle hR.normal fun x y n hn m hm =>
      twist_eq_of_mem hR.normal (fun n hn => htriv n (hRle hn)) haR hu₁R x y hn hm
  have hu₁₂R : ∀ g : G, ∀ n ∈ R, (u₁ * u₂) (g * n) = (u₁ * u₂) g := by
    intro g n hn
    simp only [Pi.mul_apply, hu₁R g n hn, hu₂R g n hn]
  obtain ⟨φ, hφs, hφ, hcls⟩ := htr _ (isMulCocycle₂_twist ha (u₁ * u₂))
    ⟨R, hR, fun x y n hn m hm =>
      twist_eq_of_mem hR.normal (fun n hn => htriv n (hRle hn)) haR hu₁₂R x y hn hm⟩ h₂
  obtain ⟨R', hR', hR'le, hR'R, hφR'⟩ : ∃ R' : Subgroup G, IsOpenNormal R' ∧ R' ≤ π.ker ∧
      R' ≤ R ∧ (∀ g : G, ∀ n ∈ R', φ (g * n) = φ g) := by
    obtain ⟨N₃, hN₃, hφ₁⟩ := hφs
    exact ⟨R ⊓ N₃, hR.inf hN₃, fun x hx => hRle hx.1, fun x hx => hx.1,
      fun g n hn => hφ₁ g n hn.2⟩
  have htrivR' : ∀ n ∈ R', ∀ m : M, n • m = m := fun n hn => htriv n (hR'le hn)
  have hu₁₂R' : ∀ g : G, ∀ n ∈ R', (u₁ * u₂) (g * n) = (u₁ * u₂) g :=
    fun g n hn => hu₁₂R g n (hR'R hn)
  have hcR' : ∀ x y : G, ∀ n ∈ R', ∀ m ∈ R',
      twist a (u₁ * u₂) (x * n, y * m) = twist a (u₁ * u₂) (x, y) :=
    fun x y n hn m hm => twist_eq_of_mem hR'.normal htrivR'
      (fun x y n hn m hm => haR x y n (hR'R hn) m (hR'R hm)) hu₁₂R' x y hn hm
  have hφ' : ∀ x ∈ π.ker, ∀ y ∈ π.ker, φ (x * y) = x • φ y * φ x := by
    intro x hx y hy
    rw [hφ x hx y hy, htriv x hx, mul_comm]
  have hcls' : ∀ σ : G, ∃ t : M, ∀ x ∈ π.ker,
      twist a (u₁ * u₂) (σ, σ⁻¹ * x * σ) = σ • φ (σ⁻¹ * x * σ) / φ x * (x • t / t) := by
    refine fun σ => ⟨1, fun x hx => ?_⟩
    have h := hcls σ x hx
    rw [transgression_apply] at h
    rw [h, smul_one, div_one, mul_one]
  obtain ⟨u₃, h₃, hTr, hi₃⟩ := exists_twist_conj_eq_smul_div hs hsc hs1 h₂ hφ' hcls'
  have hu₃R' : ∀ g : G, ∀ n ∈ R', u₃ (g * n) = u₃ g := hi₃ R' hR'le hR'.normal hφR'
  obtain ⟨u₄, h₄, h₅, hi₄⟩ := exists_twist_eq_one_of_mem_of_section hs hsc hs1
    (isMulCocycle₂_twist (isMulCocycle₂_twist ha (u₁ * u₂)) u₃) h₃ hTr
  have hu₄R' : ∀ g : G, ∀ n ∈ R', u₄ (g * n) = u₄ g := hi₄ R' hR'le hR'.normal htrivR'
  rw [twist_twist, twist_twist] at h₄ h₅
  have husm : IsSmooth₁ (u₁ * u₂ * (u₃ * u₄)) := by
    refine ⟨R', hR', fun g n hn => ?_⟩
    simp only [Pi.mul_apply, hu₁R g n (hR'R hn), hu₂R g n (hR'R hn), hu₃R' g n hn, hu₄R' g n hn]
  have hcos : ∀ x y : G, ∀ n ∈ π.ker, ∀ m ∈ π.ker,
      twist a (u₁ * u₂ * (u₃ * u₄)) (x * n, y * m) = twist a (u₁ * u₂ * (u₃ * u₄)) (x, y) := by
    intro x y n hn m hm
    rw [apply_mul_right_eq_of_eq_one (isMulCocycle₂_twist ha _) h₅ _ _ hm,
      apply_mul_left_eq_of_eq_one (isMulCocycle₂_twist ha _) h₄ h₅ _ _ hn]
  have hcyc : IsMulCocycle₂ (twist a (u₁ * u₂ * (u₃ * u₄))) := isMulCocycle₂_twist ha _
  have hcsm : IsSmooth₂ (twist a (u₁ * u₂ * (u₃ * u₄))) :=
    ⟨K, hK, fun x y n hn m hm => hcos x y n (hKle hn) m (hKle hm)⟩
  obtain ⟨z, hz⟩ := exists_comapH2_eq hπ hsm hsurj hcyc hcsm hcos
  refine ⟨z, ?_⟩
  rw [hz]
  refine ((smoothH2Mk_eq_iff ha has hcyc hcsm).mpr ⟨u₁ * u₂ * (u₃ * u₄), husm, ?_⟩).symm
  funext p
  rw [eq_twist_mul_coboundary₂ a (u₁ * u₂ * (u₃ * u₄)) p]
  apply Additive.ofMul.injective
  simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]
  abel

end InverseGalois.CFT
