/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.TransgressionClass

/-!
# A transgression restricted to a subgroup

A transgression is a family of maps of a topological group into the coefficients, indexed by the
group itself, and restricting both variables to a subgroup gives a family which satisfies the same
four conditions with respect to the part of the normal subgroup lying inside.  The restricted family
therefore has a class of its own, in the first cohomology of the subgroup with values in the first
cohomology of that part, and the vanishing of that class is exactly the local condition which the
descent theorem of the previous file asks for.

This is what turns the descent into a Hasse principle in the ordinary sense: the hypothesis is no
longer a hand-written list of properties of an auxiliary function on each member of the family, but
the triviality of one cohomology class per member, which is what a local-global principle in
arithmetic delivers.  Only the elementary direction of the equivalence between the two is needed,
so the subgroup is not required to have a basis of open normal subgroups.

## Main definitions

* `InverseGalois.CFT.restrictCochain`: a family of maps, restricted to a subgroup in both variables.
* `InverseGalois.CFT.localTransClass`: **the class of a transgression restricted to a subgroup.**

## Main results

* `InverseGalois.CFT.IsTransgressionDatum.restrict`: **a transgression restricts to a transgression
  of a subgroup.**
* `InverseGalois.CFT.localTransClass_eq_one`: the restricted class vanishes when the transgression
  is, on the subgroup, the coboundary of a smooth homomorphism.
* `InverseGalois.CFT.exists_comapH2_eq_of_localTransClass`: **a locally trivial class of the second
  cohomology whose restriction to the kernel of a smooth surjection onto a discrete group is trivial
  is inflated from the quotient**, as soon as a transgression whose restricted classes all vanish
  has itself a vanishing class.

## Tags

profinite group, Galois cohomology, transgression, restriction, Hasse principle
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### The part of a normal subgroup inside a subgroup -/

section Inter

variable {G : Type*} [Group G] [TopologicalSpace G] (N D : Subgroup G)

/-- The part of a subgroup lying inside another one, viewed inside their intersection. -/
def interHom : ↥(N.subgroupOf D) →* ↥(D ⊓ N) where
  toFun y := ⟨((y : ↥D) : G), Subgroup.mem_inf.2 ⟨(y : ↥D).2, Subgroup.mem_subgroupOf.1 y.2⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [TopologicalSpace G] in
@[simp]
theorem coe_interHom (y : ↥(N.subgroupOf D)) : ((interHom N D y : ↥(D ⊓ N)) : G) = ((y : ↥D) : G) :=
  rfl

/-- The passage to the intersection is continuous for the subspace topologies. -/
theorem continuous_interHom : Continuous (interHom N D) := by
  have h : Continuous fun y : ↥(N.subgroupOf D) => ((y : ↥D) : G) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact continuous_induced_rng.2 h

variable {N D}

/-- The part of an open subgroup inside a subgroup is open there. -/
theorem isOpen_subgroupOf (hop : IsOpen (N : Set G)) :
    IsOpen ((N.subgroupOf D : Subgroup ↥D) : Set ↥D) :=
  hop.preimage (continuous_subtype D)

variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]

omit [TopologicalSpace G] in
/-- A subgroup acting trivially still acts trivially on the part of it inside another subgroup. -/
theorem trivial_subgroupOf (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) :
    ∀ n ∈ N.subgroupOf D, ∀ m : M, n • m = m :=
  fun n hn m => htriv (n : G) (Subgroup.mem_subgroupOf.1 hn) m

end Inter

/-! ### The restriction of a transgression -/

section Restrict

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]
variable {N : Subgroup G} {t : G → G → M}

variable (t) in
/-- **A family of maps of a group into the coefficients, restricted to a subgroup in both
variables.** -/
def restrictCochain (D : Subgroup G) : ↥D → ↥D → M := fun σ x => t (σ : G) (x : G)

omit [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M] in
@[simp]
theorem restrictCochain_apply (D : Subgroup G) (σ x : ↥D) :
    restrictCochain t D σ x = t (σ : G) (x : G) := rfl

/-- **A transgression restricts to a transgression of a subgroup**, the four conditions being
inherited term by term from the ambient ones. -/
theorem IsTransgressionDatum.restrict (h : IsTransgressionDatum N M t) (D : Subgroup G) :
    IsTransgressionDatum (N.subgroupOf D) M (restrictCochain t D) where
  isSmooth := by
    obtain ⟨R, hR, hcon⟩ := h.isSmooth
    exact ⟨R.comap D.subtype, isOpenNormal_comap_subtype D hR,
      fun σ x n hn => hcon (σ : G) (x : G) (n : G) (Subgroup.mem_comap.1 hn)⟩
  map_mul σ x hx y hy :=
    h.map_mul (σ : G) (x : G) (Subgroup.mem_subgroupOf.1 hx) (y : G)
      (Subgroup.mem_subgroupOf.1 hy)
  cocycle σ τ x hx := h.cocycle (σ : G) (τ : G) (x : G) (Subgroup.mem_subgroupOf.1 hx)
  smul_left n hn σ x hx :=
    h.smul_left (n : G) (Subgroup.mem_subgroupOf.1 hn) (σ : G) (x : G)
      (Subgroup.mem_subgroupOf.1 hx)

variable [IsTopologicalGroup G] [hN : N.Normal]

/-- **The class of a transgression restricted to a subgroup**, in the first cohomology of that
subgroup with values in the first cohomology of the part of the normal subgroup lying inside it. -/
def localTransClass (h : IsTransgressionDatum N M t) (htriv : ∀ n ∈ N, ∀ m : M, n • m = m)
    (hop : IsOpen (N : Set G)) (D : Subgroup G) :
    SmoothH1 ↥D (SmoothH1 ↥(N.subgroupOf D) M) :=
  transClass (h.restrict D) (trivial_subgroupOf htriv) (isOpen_subgroupOf hop)

/-- **The restricted class of a transgression vanishes when the transgression is, on the subgroup,
the coboundary of a smooth homomorphism.** -/
theorem localTransClass_eq_one (h : IsTransgressionDatum N M t)
    (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (hop : IsOpen (N : Set G)) (D : Subgroup G) {e : G → M}
    (hes : IsSmooth₁ fun x : ↥(D ⊓ N) => e (x : G))
    (hem : ∀ x ∈ D ⊓ N, ∀ y ∈ D ⊓ N, e (x * y) = e x * e y)
    (he : ∀ σ ∈ D, ∀ x ∈ D, x ∈ N → t σ x = σ • e (σ⁻¹ * x * σ) / e x) :
    localTransClass h htriv hop D = 1 :=
  transClass_eq_one (φ := fun σ : ↥D => e (σ : G)) (h.restrict D) (trivial_subgroupOf htriv)
    (isOpen_subgroupOf hop) (isSmooth₁_comp (continuous_interHom N D) hes)
    (fun x hx y hy => hem (x : G) (Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_subgroupOf.1 hx⟩)
      (y : G) (Subgroup.mem_inf.2 ⟨y.2, Subgroup.mem_subgroupOf.1 hy⟩))
    (fun σ x hx => he (σ : G) σ.2 (x : G) x.2 (Subgroup.mem_subgroupOf.1 hx))

end Restrict

/-! ### Inflation from the vanishing of the restricted transgression classes -/

section Package

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [CommGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction Q M]
variable {π : G →* Q} (hπ : ∀ (g : G) (m : M), g • m = π g • m)

/-- **A locally trivial class of the second cohomology of a topological group whose restriction to
the kernel of a smooth surjection onto a discrete group is trivial is inflated from the quotient**,
as soon as a transgression all of whose restricted classes vanish has itself a vanishing class.
The hypothesis is now a Hasse principle in the ordinary sense, one cohomology class per member of
the family, and nothing else about the family is used. -/
theorem exists_comapH2_eq_of_localTransClass (hbasis : HasOpenNormalBasis G) (hsm : IsSmoothHom π)
    (hsurj : Function.Surjective π) (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a)
    {b : G → M} (hbs : IsSmooth₁ b)
    (hb : ∀ x ∈ π.ker, ∀ y ∈ π.ker, a (x, y) = x • b y / b (x * y) * b x)
    {S : Set (Subgroup G)} (hmem : smoothH2Mk a ha has ∈ sha2 M S)
    (hsha : ∀ (t : G → G → M) (h : IsTransgressionDatum π.ker M t),
      (∀ D ∈ S, localTransClass h htriv
        (isOpenNormal_ker_of_isSmoothHom hsm).isOpen D = 1) →
      transClass h htriv (isOpenNormal_ker_of_isSmoothHom hsm).isOpen = 1) :
    ∃ x : SmoothH2 Q M, comapH2 π hπ hsm x = smoothH2Mk a ha has := by
  refine exists_comapH2_eq_of_transClass hπ hbasis hsm hsurj htriv ha has hbs hb hmem ?_
  intro t h hloc
  refine hsha t h fun D hD => ?_
  obtain ⟨e, hes, hem, he⟩ := hloc D hD
  exact localTransClass_eq_one h htriv (isOpenNormal_ker_of_isSmoothHom hsm).isOpen D hes hem he

end Package

end InverseGalois.CFT
