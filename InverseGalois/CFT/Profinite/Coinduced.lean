/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Coeff
import InverseGalois.CFT.Profinite.Corestriction

/-!
# The module coinduced from a subgroup, and Shapiro's lemma in low degrees

The functions on a group that are equivariant for a subgroup acting on the left form a module for
the whole group, acting by translation on the right: the *coinduced* module.  Evaluating at the
neutral element is a homomorphism of modules for the subgroup, so restricting a class to the
subgroup and then evaluating gives a map of cohomology groups, the map of Shapiro's lemma.

This file constructs the coinduced module for smooth cochains and proves that the map of Shapiro's
lemma is **injective** in the first and in the second cohomology.  Injectivity is the half that a
local to global principle consumes: a class of the coinduced module that dies on the subgroup dies
altogether, so the everywhere locally trivial classes of a coinduced module are governed by the
everywhere locally trivial classes over the smaller group.

The first degree is formal.  A one cocycle `u` with values in the coinduced module is determined by
the function `x ↦ u x 1`, because the cocycle relation read at the neutral element gives
`u y x = u (x * y) 1 / u x 1`; the same relation read the other way gives
`u (h * x) 1 = h • u x 1 * u h 1`, so a primitive of the restricted cocycle turns `x ↦ u x 1`
itself into an element of the coinduced module, and that element is a primitive of `u`.

The second degree needs a set of representatives for the cosets of the subgroup.  A two cocycle `a`
is again determined by `Φ x y = a (x, y) 1`, through
`a (x, y) z = Φ (z * x) y * Φ z x / Φ z (x * y)`, and the ansatz
`U x z = Φ z x * w (z * x) / w z` solves the coboundary equation for *any* function `w`, the values
of `w` cancelling in threes.  The equivariance of `U x` is then a single condition on `w`, and a
primitive `v` of the restricted cocycle solves it: put `w x = v (τ x) / Φ (τ x) (ρ x)`, where
`x = τ x * ρ x` splits `x` into a part in the subgroup and a representative of its coset.

## Main definitions

* `InverseGalois.CFT.smoothCoind`: **the module coinduced from a subgroup.**
* `InverseGalois.CFT.smoothCoindEval`: evaluation at the neutral element.
* `InverseGalois.CFT.smoothShapiroH1`, `InverseGalois.CFT.smoothShapiroH2`: **the map of Shapiro's
  lemma**, restriction to the subgroup followed by evaluation.
* `InverseGalois.CFT.coindRep`, `InverseGalois.CFT.coindPart`: the representative of the coset of
  an element, and the part of the element lying in the subgroup.

## Main results

* `InverseGalois.CFT.smoothShapiroH1_injective`: **Shapiro's map is injective in the first
  cohomology**, with no hypothesis on the subgroup at all.
* `InverseGalois.CFT.smoothShapiroH2_injective`: **Shapiro's map is injective in the second
  cohomology**, for a normal subgroup with an open normal core.
* `InverseGalois.CFT.sha1_smoothCoind_eq_bot`, `InverseGalois.CFT.sha2_smoothCoind_eq_bot`: **a
  coinduced module has no everywhere locally trivial class**, in either degree, as soon as the
  subgroup one coinduces from belongs to the family of subgroups.

## Tags

profinite group, Galois cohomology, coinduced module, Shapiro's lemma, restriction
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### Identities in a commutative group -/

section Algebra

variable {M : Type*} [CommGroup M]

private theorem coindAlgOne (X Y Z : M) : X * Y / (X / Z * Y) = Z := by
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_div]
  abel

private theorem coindAlgTwo (X Y Z S T : M) : X * Y / Z / (S * T / Z) = Y * (X / S) / T := by
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_div]
  abel

private theorem coindAlgThree (A B C D Y P Q : M) (h : A * B = C * D) :
    A * (Y * P / D) / (Y * Q / B) = C * P / Q := by
  have hA : A = C * D / B := by rw [← h, mul_div_cancel_right]
  rw [hA]
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_div]
  abel

private theorem coindAlgFour (A B C W₀ W₂ W₃ : M) :
    A * W₃ / W₂ / (B * W₃ / W₀) * (C * W₂ / W₀) = A * C / B := by
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_div]
  abel

end Algebra

/-! ### The coinduced module -/

section Coind

variable {G : Type*} [Group G] (H : Subgroup G) (M : Type*) [CommGroup M]
  [MulDistribMulAction ↥H M]

/-- **The module coinduced from a subgroup**: the functions on the group that are equivariant for
the subgroup acting on the left. -/
def smoothCoind : Subgroup (G → M) where
  carrier := {f | ∀ (h : ↥H) (x : G), f ((h : G) * x) = h • f x}
  one_mem' := by
    intro h x
    simp
  mul_mem' := by
    intro f₁ f₂ hf₁ hf₂ h x
    simp only [Pi.mul_apply, hf₁ h x, hf₂ h x, smul_mul']
  inv_mem' := by
    intro f hf h x
    simp only [Pi.inv_apply, hf h x, smul_inv']

variable {H M}

/-- Membership in the coinduced module is equivariance for the subgroup. -/
theorem mem_smoothCoind {f : G → M} :
    f ∈ smoothCoind H M ↔ ∀ (h : ↥H) (x : G), f ((h : G) * x) = h • f x := Iff.rfl

/-- An element of the coinduced module is equivariant for the subgroup. -/
theorem smoothCoind_apply_mul (f : ↥(smoothCoind H M)) (h : ↥H) (x : G) :
    (f : G → M) ((h : G) * x) = h • (f : G → M) x := f.2 h x

variable (H M)

/-- **The group acts on the module coinduced from a subgroup** by translation on the right. -/
instance smoothCoindAction : MulDistribMulAction G ↥(smoothCoind H M) where
  smul g f := ⟨fun x => (f : G → M) (x * g), by
    intro h x
    show (f : G → M) ((h : G) * x * g) = h • (f : G → M) (x * g)
    rw [mul_assoc]
    exact smoothCoind_apply_mul f h (x * g)⟩
  one_smul f := Subtype.ext (funext fun x => by
    show (f : G → M) (x * 1) = (f : G → M) x
    rw [mul_one])
  mul_smul g₁ g₂ f := Subtype.ext (funext fun x => by
    show (f : G → M) (x * (g₁ * g₂)) = (f : G → M) (x * g₁ * g₂)
    rw [mul_assoc])
  smul_mul _ _ _ := Subtype.ext (funext fun _ => rfl)
  smul_one _ := Subtype.ext (funext fun _ => rfl)

variable {H M}

/-- The action on the coinduced module is translation on the right. -/
theorem smoothCoind_smul_apply (g : G) (f : ↥(smoothCoind H M)) (x : G) :
    ((g • f : ↥(smoothCoind H M)) : G → M) x = (f : G → M) (x * g) := rfl

variable (H M)

/-- **Evaluation at the neutral element**, out of the module coinduced from a subgroup. -/
def smoothCoindEval : ↥(smoothCoind H M) →* M where
  toFun f := (f : G → M) 1
  map_one' := rfl
  map_mul' _ _ := rfl

variable {H M}

@[simp]
theorem smoothCoindEval_apply (f : ↥(smoothCoind H M)) :
    smoothCoindEval H M f = (f : G → M) 1 := rfl

/-- **Evaluation at the neutral element is equivariant for the subgroup.** -/
theorem smoothCoindEval_smul (h : ↥H) (f : ↥(smoothCoind H M)) :
    smoothCoindEval H M (h • f) = h • smoothCoindEval H M f := by
  show (f : G → M) (1 * (h : G)) = h • (f : G → M) 1
  rw [one_mul, ← mul_one ((h : G))]
  exact smoothCoind_apply_mul f h 1

end Coind

/-! ### The map of Shapiro's lemma -/

section Shapiro

variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) (M : Type*) [CommGroup M]
  [MulDistribMulAction ↥H M]

/-- **The map of Shapiro's lemma in the first cohomology**: restrict a class of the coinduced
module to the subgroup, then evaluate at the neutral element. -/
def smoothShapiroH1 : SmoothH1 G ↥(smoothCoind H M) →* SmoothH1 ↥H M :=
  (coeffH1 (smoothCoindEval H M) smoothCoindEval_smul).comp (resH1 H)

/-- **The map of Shapiro's lemma in the second cohomology**: restrict a class of the coinduced
module to the subgroup, then evaluate at the neutral element. -/
def smoothShapiroH2 : SmoothH2 G ↥(smoothCoind H M) →* SmoothH2 ↥H M :=
  (coeffH2 (smoothCoindEval H M) smoothCoindEval_smul).comp (resH2 H)

variable {H M}

/-- Shapiro's map is computed on cocycles. -/
theorem smoothShapiroH1_smoothH1Mk {u : G → ↥(smoothCoind H M)} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u)
    (hu' : IsMulCocycle₁ fun h : ↥H => (u (h : G) : G → M) 1)
    (hs' : IsSmooth₁ fun h : ↥H => (u (h : G) : G → M) 1) :
    smoothShapiroH1 H M (smoothH1Mk u hu hs)
      = smoothH1Mk (fun h : ↥H => (u (h : G) : G → M) 1) hu' hs' := rfl

/-- Shapiro's map is computed on cocycles. -/
theorem smoothShapiroH2_smoothH2Mk {a : G × G → ↥(smoothCoind H M)} (ha : IsMulCocycle₂ a)
    (hs : IsSmooth₂ a)
    (ha' : IsMulCocycle₂ fun p : ↥H × ↥H => (a ((p.1 : G), (p.2 : G)) : G → M) 1)
    (hs' : IsSmooth₂ fun p : ↥H × ↥H => (a ((p.1 : G), (p.2 : G)) : G → M) 1) :
    smoothShapiroH2 H M (smoothH2Mk a ha hs)
      = smoothH2Mk (fun p : ↥H × ↥H => (a ((p.1 : G), (p.2 : G)) : G → M) 1) ha' hs' := rfl

end Shapiro

/-! ### The first cohomology -/

section DegreeOne

variable {G : Type*} [Group G] [TopologicalSpace G] {H : Subgroup G} {M : Type*} [CommGroup M]
  [MulDistribMulAction ↥H M]

omit [TopologicalSpace G] in
/-- **A one cocycle of the coinduced module is determined by its values at the neutral element.**
The cocycle relation read at the neutral element expresses every value of the cocycle as a ratio of
two of them. -/
theorem smoothCoind_cocycle₁_apply {u : G → ↥(smoothCoind H M)} (hu : IsMulCocycle₁ u) (x y : G) :
    (u y : G → M) x = (u (x * y) : G → M) 1 / (u x : G → M) 1 := by
  have h := congrArg (fun t : ↥(smoothCoind H M) => (t : G → M) 1) (hu x y)
  simp only [Subgroup.coe_mul, Pi.mul_apply, smoothCoind_smul_apply, one_mul] at h
  rw [h, mul_div_cancel_right]

omit [TopologicalSpace G] in
/-- **A one cocycle of the coinduced module is almost equivariant**: its values at the neutral
element transform under the subgroup up to the value at the element of the subgroup. -/
theorem smoothCoind_cocycle₁_smul {u : G → ↥(smoothCoind H M)} (hu : IsMulCocycle₁ u) (h : ↥H)
    (x : G) :
    (u ((h : G) * x) : G → M) 1 = h • (u x : G → M) 1 * (u (h : G) : G → M) 1 := by
  have hc := congrArg (fun t : ↥(smoothCoind H M) => (t : G → M) 1) (hu (h : G) x)
  simp only [Subgroup.coe_mul, Pi.mul_apply, smoothCoind_smul_apply, one_mul] at hc
  rw [hc, ← mul_one ((h : G)), smoothCoind_apply_mul (u x) h 1, mul_one]

/-- **Shapiro's map is injective in the first cohomology.**  A primitive of the restricted cocycle
translates the values of the cocycle at the neutral element into an element of the coinduced
module, and that element is a primitive of the cocycle itself. -/
theorem smoothShapiroH1_injective : Function.Injective (smoothShapiroH1 H M) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective c
  have hu' : IsMulCocycle₁ fun h : ↥H => (u (h : G) : G → M) 1 :=
    isMulCocycle₁_coeffMap₁ (smoothCoindEval H M) smoothCoindEval_smul
      (isMulCocycle₁_comap₁ H.subtype (fun _ _ => rfl) hu)
  have hs' : IsSmooth₁ fun h : ↥H => (u (h : G) : G → M) 1 :=
    ((isSmoothHom_subtype H).isSmooth₁ hs).coeffMap₁ (smoothCoindEval H M)
  rw [smoothShapiroH1_smoothH1Mk hu hs hu' hs', smoothH1Mk_eq_one_iff] at hc
  obtain ⟨t, ht⟩ := hc
  have ht' : ∀ h : ↥H, h • t / t = (u (h : G) : G → M) 1 := fun h => congrFun ht h
  have hmem : (fun z : G => (u z : G → M) 1 * t) ∈ smoothCoind H M := by
    intro h z
    show (u ((h : G) * z) : G → M) 1 * t = h • ((u z : G → M) 1 * t)
    rw [smoothCoind_cocycle₁_smul hu h z, ← ht' h, smul_mul', mul_assoc, div_mul_cancel]
  rw [smoothH1Mk_eq_one_iff]
  refine ⟨⟨_, hmem⟩, funext fun g => Subtype.ext (funext fun z => ?_)⟩
  show (u (z * g) : G → M) 1 * t / ((u z : G → M) 1 * t) = (u g : G → M) z
  rw [smoothCoind_cocycle₁_apply hu z g, mul_div_mul_right_eq_div]

/-- **A coinduced module has no everywhere locally trivial class in the first cohomology**, as soon
as the subgroup one coinduces from is itself one of the subgroups where triviality is imposed. -/
theorem sha1_smoothCoind_eq_bot {S : Set (Subgroup G)} (hH : H ∈ S) :
    sha1 ↥(smoothCoind H M) S = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun c hc => ?_
  refine (injective_iff_map_eq_one _).1 smoothShapiroH1_injective c ?_
  show coeffH1 (smoothCoindEval H M) smoothCoindEval_smul (resH1 H c) = 1
  rw [mem_sha1.1 hc H hH, _root_.map_one]

end DegreeOne

/-! ### Representatives for the cosets -/

section Representatives

variable {G : Type*} [Group G] (H : Subgroup G) (σ : G ⧸ H → G)

/-- The representative of the coset of an element, for a chosen section of the projection. -/
def coindRep : G → G := fun x => σ (x : G ⧸ H)

theorem coindRep_apply (x : G) : coindRep H σ x = σ (x : G ⧸ H) := rfl

/-- Multiplying on the left by an element of the subgroup does not change the coset. -/
theorem coindRep_subgroup_mul [H.Normal] (h : ↥H) (x : G) :
    coindRep H σ ((h : G) * x) = coindRep H σ x := by
  refine congrArg σ (QuotientGroup.eq.2 ?_)
  have hc := ‹H.Normal›.conj_mem ((h : G)⁻¹) (H.inv_mem h.2) x⁻¹
  simpa [mul_assoc] using hc

/-- Multiplying on the right by an element of the subgroup does not change the coset. -/
theorem coindRep_mul_mem (x : G) {n : G} (hn : n ∈ H) : coindRep H σ (x * n) = coindRep H σ x := by
  refine congrArg σ (QuotientGroup.eq.2 ?_)
  have hrw : (x * n)⁻¹ * x = n⁻¹ * (x⁻¹ * x) := by group
  rw [hrw, inv_mul_cancel, mul_one]
  exact H.inv_mem hn

/-- An element and the representative of its coset differ by an element of the subgroup. -/
theorem mul_inv_coindRep_mem [H.Normal] (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x) (x : G) :
    x * (coindRep H σ x)⁻¹ ∈ H := by
  have hmem : (coindRep H σ x)⁻¹ * x ∈ H := QuotientGroup.eq.1 (hσ (x : G ⧸ H))
  have hrw : x * (coindRep H σ x)⁻¹ = x * ((coindRep H σ x)⁻¹ * x) * x⁻¹ := by group
  rw [hrw]
  exact ‹H.Normal›.conj_mem _ hmem x

/-- The part of an element lying in the subgroup, for a chosen section of the projection. -/
def coindPart [H.Normal] (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x) : G → ↥H :=
  fun x => ⟨x * (coindRep H σ x)⁻¹, mul_inv_coindRep_mem H σ hσ x⟩

variable [H.Normal] (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x)

theorem coindPart_apply (x : G) :
    (coindPart H σ hσ x : G) = x * (coindRep H σ x)⁻¹ := rfl

/-- The two parts of an element multiply back to it. -/
theorem coindPart_mul_coindRep (x : G) :
    (coindPart H σ hσ x : G) * coindRep H σ x = x := by
  rw [coindPart_apply, inv_mul_cancel_right]

/-- Multiplying on the left by an element of the subgroup multiplies the part in the subgroup. -/
theorem coindPart_subgroup_mul (h : ↥H) (x : G) :
    coindPart H σ hσ ((h : G) * x) = h * coindPart H σ hσ x := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, coindPart_apply, coindPart_apply, coindRep_subgroup_mul H σ h x, mul_assoc]

/-- Multiplying on the right by an element of the subgroup multiplies the part in the subgroup by a
conjugate of that element. -/
theorem coindPart_mul_mem (x : G) {n : G} (hn : n ∈ H) (n' : ↥H)
    (hn' : (n' : G) = coindRep H σ x * n * (coindRep H σ x)⁻¹) :
    coindPart H σ hσ (x * n) = coindPart H σ hσ x * n' := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, hn', coindPart_apply, coindPart_apply, coindRep_mul_mem H σ x hn]
  group

end Representatives

/-! ### The second cohomology -/

section DegreeTwo

variable {G : Type*} [Group G] [TopologicalSpace G] {H : Subgroup G} {M : Type*} [CommGroup M]
  [MulDistribMulAction ↥H M]

omit [TopologicalSpace G] in
/-- **The cocycle relation of the coinduced module, read at the neutral element.** -/
theorem smoothCoind_cocycle₂_one {a : G × G → ↥(smoothCoind H M)} (ha : IsMulCocycle₂ a)
    (x y j : G) :
    (a (x * y, j) : G → M) 1 * (a (x, y) : G → M) 1
      = (a (y, j) : G → M) x * (a (x, y * j) : G → M) 1 := by
  have h := congrArg (fun t : ↥(smoothCoind H M) => (t : G → M) 1) (ha x y j)
  simpa only [Subgroup.coe_mul, Pi.mul_apply, smoothCoind_smul_apply, one_mul] using h

omit [TopologicalSpace G] in
/-- **A two cocycle of the coinduced module is determined by its values at the neutral
element.** -/
theorem smoothCoind_cocycle₂_apply {a : G × G → ↥(smoothCoind H M)} (ha : IsMulCocycle₂ a)
    (x y z : G) :
    (a (x, y) : G → M) z
      = (a (z * x, y) : G → M) 1 * (a (z, x) : G → M) 1 / (a (z, x * y) : G → M) 1 := by
  rw [smoothCoind_cocycle₂_one ha z x y, mul_div_cancel_right]

omit [TopologicalSpace G] in
/-- **The values of a two cocycle of the coinduced module at the neutral element are almost
equivariant.** -/
theorem smoothCoind_cocycle₂_smul {a : G × G → ↥(smoothCoind H M)} (ha : IsMulCocycle₂ a)
    (h : ↥H) (z x : G) :
    (a ((h : G) * z, x) : G → M) 1 * (a ((h : G), z) : G → M) 1
      = h • (a (z, x) : G → M) 1 * (a ((h : G), z * x) : G → M) 1 := by
  rw [smoothCoind_cocycle₂_one ha (h : G) z x, ← mul_one ((h : G)),
    smoothCoind_apply_mul (a (z, x)) h 1, mul_one]

/-- **Shapiro's map is injective in the second cohomology.**  Splitting an element of the group
into a part in the subgroup and a representative of its coset turns a primitive of the restricted
cocycle into a function whose divided differences are equivariant, and those differences are a
primitive of the cocycle itself. -/
theorem smoothShapiroH2_injective [H.Normal] (hcore : HasOpenNormalCore H) :
    Function.Injective (smoothShapiroH2 H M) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : G ⧸ H → G, ∀ x : G ⧸ H, (σ x : G ⧸ H) = x :=
    ⟨Function.surjInv QuotientGroup.mk_surjective, Function.surjInv_eq _⟩
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective c
  have ha' : IsMulCocycle₂ fun p : ↥H × ↥H => (a ((p.1 : G), (p.2 : G)) : G → M) 1 :=
    isMulCocycle₂_coeffMap₂ (smoothCoindEval H M) smoothCoindEval_smul
      (isMulCocycle₂_comap₂ H.subtype (fun _ _ => rfl) ha)
  have hs' : IsSmooth₂ fun p : ↥H × ↥H => (a ((p.1 : G), (p.2 : G)) : G → M) 1 :=
    ((isSmoothHom_subtype H).isSmooth₂ hs).coeffMap₂ (smoothCoindEval H M)
  rw [smoothShapiroH2_smoothH2Mk ha hs ha' hs', smoothH2Mk_eq_one_iff] at hc
  obtain ⟨v, hv, hvb⟩ := hc
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G → G → M, ∀ x y : G, Φ x y = (a (x, y) : G → M) 1 :=
    ⟨_, fun _ _ => rfl⟩
  have hC4 : ∀ x y z : G, (a (x, y) : G → M) z = Φ (z * x) y * Φ z x / Φ z (x * y) := by
    intro x y z
    rw [hΦ, hΦ, hΦ]
    exact smoothCoind_cocycle₂_apply ha x y z
  have hC3 : ∀ (h : ↥H) (z x : G),
      Φ ((h : G) * z) x * Φ (h : G) z = h • Φ z x * Φ (h : G) (z * x) := by
    intro h z x
    rw [hΦ, hΦ, hΦ, hΦ]
    exact smoothCoind_cocycle₂_smul ha h z x
  have hvb' : ∀ h₁ h₂ : ↥H, h₁ • v h₂ / v (h₁ * h₂) * v h₁ = Φ (h₁ : G) (h₂ : G) := by
    intro h₁ h₂
    rw [hΦ]
    exact congrFun hvb (h₁, h₂)
  obtain ⟨w, hwdef⟩ : ∃ w : G → M, ∀ x : G,
      w x = v (coindPart H σ hσ x) / Φ (coindPart H σ hσ x : G) (coindRep H σ x) :=
    ⟨_, fun _ => rfl⟩
  -- the key equivariance property of the primitive
  have hwmul : ∀ (h : ↥H) (t : G), w ((h : G) * t) = v h * (h • w t) / Φ (h : G) t := by
    intro h t
    have hp : coindPart H σ hσ ((h : G) * t) = h * coindPart H σ hσ t :=
      coindPart_subgroup_mul H σ hσ h t
    have hr : coindRep H σ ((h : G) * t) = coindRep H σ t := coindRep_subgroup_mul H σ h t
    have hvhp : v (h * coindPart H σ hσ t)
        = h • v (coindPart H σ hσ t) * v h / Φ (h : G) (coindPart H σ hσ t : G) := by
      rw [← hvb' h (coindPart H σ hσ t)]
      exact (coindAlgOne _ _ _).symm
    have hcc : Φ ((h : G) * (coindPart H σ hσ t : G)) (coindRep H σ t)
        = h • Φ (coindPart H σ hσ t : G) (coindRep H σ t) * Φ (h : G) t
          / Φ (h : G) (coindPart H σ hσ t : G) := by
      have hkey := hC3 h (coindPart H σ hσ t : G) (coindRep H σ t)
      rw [coindPart_mul_coindRep H σ hσ t] at hkey
      rw [eq_div_iff_mul_eq']
      exact hkey
    rw [hwdef ((h : G) * t), hwdef t, hp, hr, Subgroup.coe_mul, hvhp, hcc, smul_div']
    exact coindAlgTwo _ _ _ _ _
  -- the lift of the cocycle to the coinduced module
  have hUmem : ∀ x : G, (fun z : G => Φ z x * w (z * x) / w z) ∈ smoothCoind H M := by
    intro x h z
    show Φ ((h : G) * z) x * w ((h : G) * z * x) / w ((h : G) * z)
      = h • (Φ z x * w (z * x) / w z)
    rw [mul_assoc (h : G) z x, hwmul h (z * x), hwmul h z, smul_div', smul_mul']
    exact coindAlgThree _ _ _ _ _ _ _ (hC3 h z x)
  -- smoothness of the lift
  obtain ⟨N₁, hN₁, hN₁a⟩ := hs
  obtain ⟨N₂', hN₂', hN₂v⟩ := hv
  obtain ⟨N₂, hN₂, hN₂H, hN₂mem⟩ := hcore N₂' hN₂'
  have hwsm : ∀ (y : G) (n : G), n ∈ N₁ ⊓ N₂ → w (y * n) = w y := by
    intro y n hn
    have hnH : n ∈ H := hN₂H hn.2
    have hr : coindRep H σ (y * n) = coindRep H σ y := coindRep_mul_mem H σ y hnH
    have hconj2 : coindRep H σ y * n * (coindRep H σ y)⁻¹ ∈ N₂ :=
      hN₂.normal.conj_mem n hn.2 (coindRep H σ y)
    have hconj1 : coindRep H σ y * n * (coindRep H σ y)⁻¹ ∈ N₁ :=
      hN₁.normal.conj_mem n hn.1 (coindRep H σ y)
    obtain ⟨n', hn'⟩ : ∃ n' : ↥H, (n' : G) = coindRep H σ y * n * (coindRep H σ y)⁻¹ :=
      ⟨⟨_, hN₂H hconj2⟩, rfl⟩
    have hp : coindPart H σ hσ (y * n) = coindPart H σ hσ y * n' :=
      coindPart_mul_mem H σ hσ y hnH n' hn'
    have hae : Φ ((coindPart H σ hσ y : G) * (n' : G)) (coindRep H σ y)
        = Φ (coindPart H σ hσ y : G) (coindRep H σ y) := by
      rw [hΦ, hΦ]
      have hz := hN₁a (coindPart H σ hσ y : G) (coindRep H σ y) (n' : G) (hn' ▸ hconj1) 1
        N₁.one_mem
      rw [mul_one] at hz
      rw [hz]
    rw [hwdef (y * n), hwdef y, hp, hr, hN₂v _ n' (hN₂mem n' (hn' ▸ hconj2)), Subgroup.coe_mul,
      hae]
  have hUsm : ∀ x : G, ∀ n ∈ N₁ ⊓ N₂,
      (⟨_, hUmem (x * n)⟩ : ↥(smoothCoind H M)) = ⟨_, hUmem x⟩ := by
    intro x n hn
    refine Subtype.ext (funext fun z => ?_)
    show Φ z (x * n) * w (z * (x * n)) / w z = Φ z x * w (z * x) / w z
    have hxn : Φ z (x * n) = Φ z x := by
      rw [hΦ, hΦ]
      have hz := hN₁a z x 1 N₁.one_mem n hn.1
      rw [mul_one] at hz
      rw [hz]
    rw [show z * (x * n) = z * x * n from (mul_assoc z x n).symm, hwsm (z * x) n hn, hxn]
  -- the lift is a primitive of the cocycle
  rw [smoothH2Mk_eq_one_iff]
  refine ⟨fun x => ⟨_, hUmem x⟩, ⟨N₁ ⊓ N₂, hN₁.inf hN₂, hUsm⟩, funext fun p => ?_⟩
  obtain ⟨x, y⟩ := p
  refine Subtype.ext (funext fun z => ?_)
  show Φ (z * x) y * w (z * x * y) / w (z * x)
      / (Φ z (x * y) * w (z * (x * y)) / w z) * (Φ z x * w (z * x) / w z)
    = (a (x, y) : G → M) z
  rw [hC4 x y z, mul_assoc z x y]
  exact coindAlgFour _ _ _ _ _ _

/-- **A coinduced module has no everywhere locally trivial class in the second cohomology**, as
soon as the subgroup one coinduces from is itself one of the subgroups where triviality is
imposed. -/
theorem sha2_smoothCoind_eq_bot [H.Normal] (hcore : HasOpenNormalCore H) {S : Set (Subgroup G)}
    (hH : H ∈ S) : sha2 ↥(smoothCoind H M) S = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun c hc => ?_
  refine (injective_iff_map_eq_one _).1 (smoothShapiroH2_injective hcore) c ?_
  show coeffH2 (smoothCoindEval H M) smoothCoindEval_smul (resH2 H c) = 1
  rw [mem_sha2.1 hc H hH, _root_.map_one]

end DegreeTwo

end InverseGalois.CFT
