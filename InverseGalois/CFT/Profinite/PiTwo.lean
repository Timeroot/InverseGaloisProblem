/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Pi
import InverseGalois.CFT.Profinite.Res

/-!
# Products of coefficients in the second cohomology

The bookkeeping which reads the first cohomology of a finite product of coefficient groups factor
by factor reads the second cohomology the same way.  A two cochain with values in a product is a
family of two cochains, and it satisfies the cocycle identity exactly when every member of the
family does, because the identity is an equation between values.  Smoothness is again the only
condition that needs the family to be finite: each component is constant on the cosets of an open
normal subgroup of its own, and for finitely many components the intersection of those subgroups is
still open and normal.

The comparison of the second cohomology of the product with the product of the second cohomologies
is therefore bijective for a finite family.  Its injectivity is where the finiteness is spent a
second time: a class dying in every factor is a family of coboundaries, and the family of the one
cochains they are the coboundaries of has to be assembled into a single smooth one cochain.

Transport along an equivariant isomorphism of the coefficients works in degree two exactly as it
does in degree one, the inverse isomorphism inducing the inverse map.  Composed with the projections
it lets a computation in a group merely isomorphic to a product be made one factor at a time.

Restriction to a subgroup, finally, commutes with a map of the coefficients, since both operations
are composition of the cocycle with something: with the inclusion on the source, with the
coefficient map on the target.  So a map of the coefficients carries everywhere locally trivial
classes to everywhere locally trivial classes.

## Main definitions

* `InverseGalois.CFT.smoothH2PiHom`: the comparison of the second cohomology of a product of
  coefficients with the product of the second cohomologies.
* `InverseGalois.CFT.smoothH2PiEquiv`: **the second cohomology of a finite product of coefficients
  is the product of the second cohomologies.**
* `InverseGalois.CFT.coeffH2Equiv`: the isomorphism of second cohomologies induced by an equivariant
  isomorphism of the coefficients.

## Main results

* `InverseGalois.CFT.isSmooth₂_pi_iff`: **a two cochain into a finite product is smooth exactly
  when each of its components is.**
* `InverseGalois.CFT.isMulCocycle₂_pi_iff`: **a two cochain into a product is a cocycle exactly
  when each of its components is.**
* `InverseGalois.CFT.smoothH2PiHom_injective`: **a class of the second cohomology of a finite
  product dying in every factor is trivial.**
* `InverseGalois.CFT.coeffH2_mem_sha2`: **a map of the coefficients carries everywhere locally
  trivial classes to everywhere locally trivial classes.**

## Tags

profinite group, Galois cohomology, second cohomology, product, functoriality, locally trivial
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### Smoothness in a product -/

section Smooth

variable {G : Type*} [Group G] [TopologicalSpace G] {ι : Type*} {M : ι → Type*}

/-- The components of a smooth two cochain are smooth. -/
theorem IsSmooth₂.apply {a : G × G → ∀ i, M i} (ha : IsSmooth₂ a) (i : ι) :
    IsSmooth₂ fun p => a p i := by
  obtain ⟨N, hN, h⟩ := ha
  exact ⟨N, hN, fun x y n hn m hm => congrFun (h x y n hn m hm) i⟩

/-- **A two cochain into a finite product is smooth exactly when each of its components is.** -/
theorem isSmooth₂_pi_iff [Fintype ι] (a : G × G → ∀ i, M i) :
    IsSmooth₂ a ↔ ∀ i, IsSmooth₂ fun p => a p i := by
  refine ⟨fun ha => ha.apply, fun h => ?_⟩
  choose N hN ha using h
  refine ⟨⨅ i, N i, IsOpenNormal.iInf hN, fun x y n hn m hm => funext fun i => ?_⟩
  exact ha i x y n (Subgroup.mem_iInf.1 hn i) m (Subgroup.mem_iInf.1 hm i)

end Smooth

/-! ### Cocycles in a product -/

section Cocycle

variable {G : Type*} [Group G] {ι : Type*} {M : ι → Type*} [∀ i, CommGroup (M i)]
variable [∀ i, MulDistribMulAction G (M i)]

/-- **A two cochain into a product is a cocycle exactly when each of its components is.** -/
theorem isMulCocycle₂_pi_iff (a : G × G → ∀ i, M i) :
    IsMulCocycle₂ a ↔ ∀ i, IsMulCocycle₂ fun p => a p i :=
  ⟨fun h i g x y => congrFun (h g x y) i, fun h g x y => funext fun i => h i g x y⟩

end Cocycle

/-! ### The second cohomology of a product -/

section Cohomology

variable {G : Type*} [Group G] [TopologicalSpace G] {ι : Type*} {M : ι → Type*}
variable [∀ i, CommGroup (M i)] [∀ i, MulDistribMulAction G (M i)]

variable (G M) in
/-- **The comparison of the second cohomology of a product of coefficients with the product of the
second cohomologies**, given in each factor by the projection to it. -/
def smoothH2PiHom : SmoothH2 G (∀ i, M i) →* ∀ i, SmoothH2 G (M i) where
  toFun x i := coeffH2 (Pi.evalMonoidHom M i) (fun _ _ => rfl) x
  map_one' := funext fun i => map_one (coeffH2 (Pi.evalMonoidHom M i) (fun _ _ => rfl))
  map_mul' x y := funext fun i => map_mul (coeffH2 (Pi.evalMonoidHom M i) (fun _ _ => rfl)) x y

@[simp]
theorem smoothH2PiHom_smoothH2Mk {a : G × G → ∀ i, M i} (ha : IsMulCocycle₂ a) (hs : IsSmooth₂ a)
    (i : ι) :
    smoothH2PiHom G M (smoothH2Mk a ha hs) i
      = smoothH2Mk (fun p => a p i) ((isMulCocycle₂_pi_iff a).1 ha i) (hs.apply i) := rfl

/-- **A class of the second cohomology of a finite product dying in every factor is trivial**: the
factors furnish a family of one cochains, and the family is smooth because it is finite. -/
theorem smoothH2PiHom_injective [Fintype ι] : Function.Injective (smoothH2PiHom G M) := by
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
  have h : ∀ i, ∃ u : G → M i, IsSmooth₁ u ∧ coboundary₂ u = fun p => a p i := by
    intro i
    have hi := congrFun hx i
    rw [smoothH2PiHom_smoothH2Mk] at hi
    exact (smoothH2Mk_eq_one_iff _ _).1 hi
  choose u hu hcb using h
  refine (smoothH2Mk_eq_one_iff ha hs).2
    ⟨fun g i => u i g, (isSmooth₁_pi_iff _).2 hu, funext fun p => funext fun i => ?_⟩
  exact congrFun (hcb i) p

/-- The comparison is surjective: a family of smooth cocycles assembles into a smooth cocycle,
because the family is finite. -/
theorem smoothH2PiHom_surjective [Fintype ι] : Function.Surjective (smoothH2PiHom G M) := by
  intro y
  choose a ha hs hy using fun i => smoothH2Mk_surjective (y i)
  refine ⟨smoothH2Mk (fun p i => a i p) ((isMulCocycle₂_pi_iff _).2 ha)
    ((isSmooth₂_pi_iff _).2 hs), funext fun i => ?_⟩
  rw [smoothH2PiHom_smoothH2Mk]
  exact hy i

variable (G M) in
/-- **The second cohomology of a finite product of coefficients is the product of the second
cohomologies.** -/
noncomputable def smoothH2PiEquiv [Fintype ι] : SmoothH2 G (∀ i, M i) ≃* ∀ i, SmoothH2 G (M i) :=
  MulEquiv.ofBijective (smoothH2PiHom G M)
    ⟨smoothH2PiHom_injective, smoothH2PiHom_surjective⟩

@[simp]
theorem smoothH2PiEquiv_smoothH2Mk [Fintype ι] {a : G × G → ∀ i, M i} (ha : IsMulCocycle₂ a)
    (hs : IsSmooth₂ a) (i : ι) :
    smoothH2PiEquiv G M (smoothH2Mk a ha hs) i
      = smoothH2Mk (fun p => a p i) ((isMulCocycle₂_pi_iff a).1 ha i) (hs.apply i) := rfl

end Cohomology

/-! ### Transport along an isomorphism of the coefficients -/

section Transport

variable {G M N : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup N]
variable [MulDistribMulAction G M] [MulDistribMulAction G N] (φ : M ≃* N)
variable (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)

include hφ

/-- **An equivariant isomorphism of the coefficients induces an isomorphism of the second
cohomologies.** -/
def coeffH2Equiv : SmoothH2 G M ≃* SmoothH2 G N where
  toFun := coeffH2 (φ : M →* N) hφ
  invFun := coeffH2 (φ.symm : N →* M) (symm_smul_eq φ hφ)
  left_inv x := by
    obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
    exact congrArg (fun c : ↥(smoothCocycle₂ G M) => (QuotientGroup.mk c : SmoothH2 G M))
      (Subtype.ext (funext fun p => φ.symm_apply_apply (a p)))
  right_inv x := by
    obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
    exact congrArg (fun c : ↥(smoothCocycle₂ G N) => (QuotientGroup.mk c : SmoothH2 G N))
      (Subtype.ext (funext fun p => φ.apply_symm_apply (a p)))
  map_mul' x y := map_mul (coeffH2 (φ : M →* N) hφ) x y

@[simp]
theorem coeffH2Equiv_smoothH2Mk {a : G × G → M} (ha : IsMulCocycle₂ a) (hs : IsSmooth₂ a) :
    coeffH2Equiv φ hφ (smoothH2Mk a ha hs)
      = smoothH2Mk (coeffMap₂ (φ : M →* N) a) (isMulCocycle₂_coeffMap₂ _ hφ ha)
          (hs.coeffMap₂ _) := rfl

end Transport

/-! ### The algebra of coefficient maps in degree two -/

section Algebra

variable {G M N P : Type*} [Group G] [TopologicalSpace G]
variable [CommGroup M] [CommGroup N] [CommGroup P]
variable [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G P]

/-- The identity of the coefficients induces the identity. -/
theorem coeffH2_id (hid : ∀ (g : G) (m : M), MonoidHom.id M (g • m) = g • MonoidHom.id M m)
    (x : SmoothH2 G M) : coeffH2 (MonoidHom.id M) hid x = x := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
  rfl

/-- **Composing the coefficient maps composes the maps induced in cohomology.** -/
theorem coeffH2_comp (φ : M →* N) (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (ψ : N →* P)
    (hψ : ∀ (g : G) (n : N), ψ (g • n) = g • ψ n)
    (hcomp : ∀ (g : G) (m : M), (ψ.comp φ) (g • m) = g • (ψ.comp φ) m) (x : SmoothH2 G M) :
    coeffH2 ψ hψ (coeffH2 φ hφ x) = coeffH2 (ψ.comp φ) hcomp x := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
  rfl

end Algebra

/-! ### Restriction and the coefficients -/

section Restrict

variable {G M N : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup N]
variable [MulDistribMulAction G M] [MulDistribMulAction G N] (φ : M →* N)
variable (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)

include hφ

/-- **Restriction to a subgroup commutes with a map of the coefficients**: both are composition of
the cocycle with something. -/
theorem resH2_coeffH2 (H : Subgroup G) (x : SmoothH2 G M) :
    resH2 H (coeffH2 φ hφ x)
      = coeffH2 φ (fun (h : H) (m : M) => hφ (h : G) m) (resH2 H x) := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
  rfl

/-- **A map of the coefficients carries everywhere locally trivial classes to everywhere locally
trivial classes.** -/
theorem coeffH2_mem_sha2 {S : Set (Subgroup G)} {x : SmoothH2 G M} (hx : x ∈ sha2 M S) :
    coeffH2 φ hφ x ∈ sha2 N S := by
  refine mem_sha2.2 fun D hD => ?_
  rw [resH2_coeffH2 φ hφ D x, mem_sha2.1 hx D hD, map_one]

end Restrict

end InverseGalois.CFT
