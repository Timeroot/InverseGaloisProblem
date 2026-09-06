/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Coeff

/-!
# Products of coefficients, and the algebra of coefficient maps

A cochain with values in a product of coefficient groups is a family of cochains, one for each
factor, and it is a cocycle exactly when every member of the family is one.  Smoothness is the only
condition which does not read off factor by factor for free: a smooth cochain is constant on the
cosets of a single open normal subgroup, while a family of smooth cochains carries one subgroup
apiece.  For a finite family the intersection of those subgroups is again open and normal, and it
smooths the cochain into the product; so **for a finite product of coefficients smoothness is
smoothness in each factor**, and the first cohomology of the product is the product of the first
cohomologies.

Transport along an isomorphism of the coefficients is the other half of the same bookkeeping: an
equivariant isomorphism of coefficient groups induces an isomorphism of first cohomologies, its
inverse being induced by the inverse isomorphism.  The two together let a computation of the first
cohomology be made one factor at a time and then carried to any group isomorphic to the product.

Underneath both is the plainest fact about the construction: a map of coefficient groups acts on
cochains by composition, so the passage from a coefficient map to the map it induces in cohomology
**respects composition, the identity, the trivial map, and — the coefficients being abelian —
pointwise multiplication of coefficient maps**.  Multiplicativity in the coefficient map is what
makes the assignment a homomorphism of the group of endomorphisms of the coefficients, and hence
turns an endomorphism which is a power into that same power in cohomology.

## Main definitions

* `InverseGalois.CFT.smoothH1PiHom`: the comparison of the first cohomology of a product of
  coefficients with the product of the first cohomologies.
* `InverseGalois.CFT.coeffH1Equiv`: the isomorphism of first cohomologies induced by an equivariant
  isomorphism of the coefficients.
* `InverseGalois.CFT.coeffH1End`: for a trivially acted on coefficient group, the endomorphisms of
  the coefficients acting on a fixed class.

## Main results

* `InverseGalois.CFT.isSmooth₁_pi_iff`: **a cochain into a finite product is smooth exactly when
  each of its components is.**
* `InverseGalois.CFT.smoothH1PiEquiv`: **the first cohomology of a finite product of coefficients
  is the product of the first cohomologies.**
* `InverseGalois.CFT.coeffH1_mul`, `InverseGalois.CFT.coeffH1_comp`: the map induced in cohomology
  is multiplicative and compositional in the coefficient map.
* `InverseGalois.CFT.coeffH1_zpow`: **raising to a power in the coefficients raises to that power
  in cohomology.**

## Tags

profinite group, Galois cohomology, smooth cochain, product, coefficients
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### A finite intersection of levels -/

section OpenNormal

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **A finite intersection of open normal subgroups is open and normal.** -/
theorem IsOpenNormal.iInf {ι : Type*} [Fintype ι] {N : ι → Subgroup G}
    (h : ∀ i, IsOpenNormal (N i)) : IsOpenNormal (⨅ i, N i) := by
  rw [← Finset.inf_univ_eq_iInf]
  exact Finset.inf_induction isOpenNormal_top (fun _ ha _ hb => ha.inf hb) fun i _ => h i

end OpenNormal

/-! ### Smoothness in a product -/

section Smooth

variable {G : Type*} [Group G] [TopologicalSpace G] {ι : Type*} {M : ι → Type*}

/-- The components of a smooth cochain are smooth. -/
theorem IsSmooth₁.apply {u : G → ∀ i, M i} (hu : IsSmooth₁ u) (i : ι) :
    IsSmooth₁ fun g => u g i := by
  obtain ⟨N, hN, h⟩ := hu
  exact ⟨N, hN, fun x n hn => congrFun (h x n hn) i⟩

/-- **A one cochain into a finite product is smooth exactly when each of its components is.** -/
theorem isSmooth₁_pi_iff [Fintype ι] (u : G → ∀ i, M i) :
    IsSmooth₁ u ↔ ∀ i, IsSmooth₁ fun g => u g i := by
  refine ⟨fun hu => hu.apply, fun h => ?_⟩
  choose N hN hu using h
  refine ⟨⨅ i, N i, IsOpenNormal.iInf hN, fun x n hn => ?_⟩
  exact funext fun i => hu i x n (Subgroup.mem_iInf.1 hn i)

end Smooth

/-! ### Cocycles in a product -/

section Cocycle

variable {G : Type*} [Group G] {ι : Type*} {M : ι → Type*} [∀ i, CommGroup (M i)]
variable [∀ i, MulDistribMulAction G (M i)]

/-- **A one cochain into a product is a cocycle exactly when each of its components is.** -/
theorem isMulCocycle₁_pi_iff (u : G → ∀ i, M i) :
    IsMulCocycle₁ u ↔ ∀ i, IsMulCocycle₁ fun g => u g i :=
  ⟨fun h i g x => congrFun (h g x) i, fun h g x => funext fun i => h i g x⟩

end Cocycle

/-! ### The first cohomology of a product -/

section Cohomology

variable {G : Type*} [Group G] [TopologicalSpace G] {ι : Type*} {M : ι → Type*}
variable [∀ i, CommGroup (M i)] [∀ i, MulDistribMulAction G (M i)]

variable (G M) in
/-- **The comparison of the first cohomology of a product of coefficients with the product of the
first cohomologies**, given in each factor by the projection to it. -/
def smoothH1PiHom : SmoothH1 G (∀ i, M i) →* ∀ i, SmoothH1 G (M i) where
  toFun x i := coeffH1 (Pi.evalMonoidHom M i) (fun _ _ => rfl) x
  map_one' := funext fun i => map_one (coeffH1 (Pi.evalMonoidHom M i) (fun _ _ => rfl))
  map_mul' x y := funext fun i => map_mul (coeffH1 (Pi.evalMonoidHom M i) (fun _ _ => rfl)) x y

@[simp]
theorem smoothH1PiHom_smoothH1Mk {u : G → ∀ i, M i} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u)
    (i : ι) :
    smoothH1PiHom G M (smoothH1Mk u hu hs) i
      = smoothH1Mk (fun g => u g i) ((isMulCocycle₁_pi_iff u).1 hu i) (hs.apply i) := rfl

/-- The comparison is injective: a family of coboundaries is the coboundary of the family of the
elements they come from. -/
theorem smoothH1PiHom_injective : Function.Injective (smoothH1PiHom G M) := by
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  have h : ∀ i, ∃ t : M i, (fun g : G => g • t / t) = fun g => u g i := by
    intro i
    have hi := congrFun hx i
    rw [smoothH1PiHom_smoothH1Mk] at hi
    exact (smoothH1Mk_eq_one_iff _ _).1 hi
  choose t ht using h
  refine (smoothH1Mk_eq_one_iff hu hs).2 ⟨t, funext fun g => funext fun i => ?_⟩
  exact congrFun (ht i) g

/-- The comparison is surjective: a family of smooth cocycles assembles into a smooth cocycle,
because the family is finite. -/
theorem smoothH1PiHom_surjective [Fintype ι] : Function.Surjective (smoothH1PiHom G M) := by
  intro y
  choose u hu hs hy using fun i => smoothH1Mk_surjective (y i)
  refine ⟨smoothH1Mk (fun g i => u i g) ((isMulCocycle₁_pi_iff _).2 hu)
    ((isSmooth₁_pi_iff _).2 hs), funext fun i => ?_⟩
  rw [smoothH1PiHom_smoothH1Mk]
  exact hy i

variable (G M) in
/-- **The first cohomology of a finite product of coefficients is the product of the first
cohomologies.** -/
noncomputable def smoothH1PiEquiv [Fintype ι] : SmoothH1 G (∀ i, M i) ≃* ∀ i, SmoothH1 G (M i) :=
  MulEquiv.ofBijective (smoothH1PiHom G M)
    ⟨smoothH1PiHom_injective, smoothH1PiHom_surjective⟩

@[simp]
theorem smoothH1PiEquiv_smoothH1Mk [Fintype ι] {u : G → ∀ i, M i} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u) (i : ι) :
    smoothH1PiEquiv G M (smoothH1Mk u hu hs) i
      = smoothH1Mk (fun g => u g i) ((isMulCocycle₁_pi_iff u).1 hu i) (hs.apply i) := rfl

end Cohomology

/-! ### Transport along an isomorphism of the coefficients -/

section Transport

variable {G M N : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup N]
variable [MulDistribMulAction G M] [MulDistribMulAction G N] (φ : M ≃* N)
variable (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)

include hφ

omit [TopologicalSpace G] in
/-- The inverse of an equivariant isomorphism of the coefficients is equivariant. -/
theorem symm_smul_eq (g : G) (n : N) : φ.symm (g • n) = g • φ.symm n := by
  refine φ.injective ?_
  rw [MulEquiv.apply_symm_apply, hφ, MulEquiv.apply_symm_apply]

/-- **An equivariant isomorphism of the coefficients induces an isomorphism of the first
cohomologies.** -/
def coeffH1Equiv : SmoothH1 G M ≃* SmoothH1 G N where
  toFun := coeffH1 (φ : M →* N) hφ
  invFun := coeffH1 (φ.symm : N →* M) (symm_smul_eq φ hφ)
  left_inv x := by
    obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
    exact congrArg (fun c : ↥(smoothCocycle₁ G M) => (QuotientGroup.mk c : SmoothH1 G M))
      (Subtype.ext (funext fun g => φ.symm_apply_apply (u g)))
  right_inv x := by
    obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
    exact congrArg (fun c : ↥(smoothCocycle₁ G N) => (QuotientGroup.mk c : SmoothH1 G N))
      (Subtype.ext (funext fun g => φ.apply_symm_apply (u g)))
  map_mul' x y := map_mul (coeffH1 (φ : M →* N) hφ) x y

@[simp]
theorem coeffH1Equiv_smoothH1Mk {u : G → M} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) :
    coeffH1Equiv φ hφ (smoothH1Mk u hu hs)
      = smoothH1Mk (coeffMap₁ (φ : M →* N) u) (isMulCocycle₁_coeffMap₁ _ hφ hu)
          (hs.coeffMap₁ _) := rfl

end Transport

/-! ### The algebra of coefficient maps -/

section Algebra

variable {G M N P : Type*} [Group G] [TopologicalSpace G]
variable [CommGroup M] [CommGroup N] [CommGroup P]
variable [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G P]

/-- The identity of the coefficients induces the identity. -/
theorem coeffH1_id (hid : ∀ (g : G) (m : M), MonoidHom.id M (g • m) = g • MonoidHom.id M m)
    (x : SmoothH1 G M) : coeffH1 (MonoidHom.id M) hid x = x := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  rfl

/-- The trivial map of the coefficients induces the trivial map. -/
theorem coeffH1_one (h1 : ∀ (g : G) (m : M), (1 : M →* N) (g • m) = g • (1 : M →* N) m)
    (x : SmoothH1 G M) : coeffH1 (1 : M →* N) h1 x = 1 := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  rfl

/-- **Composing the coefficient maps composes the maps induced in cohomology.** -/
theorem coeffH1_comp (φ : M →* N) (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (ψ : N →* P)
    (hψ : ∀ (g : G) (n : N), ψ (g • n) = g • ψ n)
    (hcomp : ∀ (g : G) (m : M), (ψ.comp φ) (g • m) = g • (ψ.comp φ) m) (x : SmoothH1 G M) :
    coeffH1 ψ hψ (coeffH1 φ hφ x) = coeffH1 (ψ.comp φ) hcomp x := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  rfl

/-- **The map induced in cohomology is multiplicative in the coefficient map.** -/
theorem coeffH1_mul (φ ψ : M →* N) (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)
    (hψ : ∀ (g : G) (m : M), ψ (g • m) = g • ψ m)
    (hmul : ∀ (g : G) (m : M), (φ * ψ) (g • m) = g • (φ * ψ) m) (x : SmoothH1 G M) :
    coeffH1 (φ * ψ) hmul x = coeffH1 φ hφ x * coeffH1 ψ hψ x := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  rfl

variable (htriv : ∀ (g : G) (m : M), g • m = m)

include htriv

variable (M) in
/-- **The endomorphisms of a trivially acted on coefficient group acting on a fixed class.**  It is
a homomorphism because the map induced in cohomology is multiplicative in the coefficient map. -/
def coeffH1End (x : SmoothH1 G M) : (M →* M) →* SmoothH1 G M where
  toFun φ := coeffH1 φ (fun g m => by rw [htriv, htriv]) x
  map_one' := coeffH1_one _ x
  map_mul' φ ψ := coeffH1_mul φ ψ _ _ _ x

theorem coeffH1End_apply (x : SmoothH1 G M) (φ : M →* M)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) :
    coeffH1End M htriv x φ = coeffH1 φ hφ x := rfl

/-- **Raising to a power in the coefficients raises to that power in cohomology.** -/
theorem coeffH1_zpow (n : ℤ) (φ : M →* M) (hn : ∀ m : M, φ m = m ^ n)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (x : SmoothH1 G M) :
    coeffH1 φ hφ x = x ^ n := by
  have hid : φ = MonoidHom.id M ^ n := MonoidHom.ext fun m => hn m
  rw [show coeffH1 φ hφ x = coeffH1End M htriv x φ from rfl, hid, map_zpow]
  exact congrArg (· ^ n) (coeffH1_id (fun g m => by rw [htriv, htriv]) x)

end Algebra

end InverseGalois.CFT
