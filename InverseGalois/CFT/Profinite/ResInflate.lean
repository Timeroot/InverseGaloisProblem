/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Res
import InverseGalois.CFT.Profinite.TransgressionCoeff
import InverseGalois.CFT.Profinite.TransgressionInflate

/-!
# Inflation from the vanishing of a restriction

The criterion for a class of the second cohomology to be inflated from a quotient asks for a
primitive of its cocycle on the kernel, as a cochain on the whole group.  What an argument actually
produces is the vanishing of the restriction of the class to the kernel, which is a primitive
defined on the kernel alone.  The gap between the two is filled by extending a cochain by one
outside an open subgroup: the extension is again constant on the cosets of an open normal subgroup,
because an open subgroup of an open subgroup is open in the whole group and therefore contains an
open normal subgroup of it, and multiplying an element outside the subgroup by an element of the
subgroup keeps it outside.

With the extension in hand the criterion reads as it should: **a locally trivial class of the second
cohomology which dies on the kernel of a smooth surjection onto a discrete group is inflated from
that group**, as soon as the locally trivial classes of the first cohomology at the level of the
quotient are trivial.  This is the form in which a vanishing theorem over a field feeds into a
transgression argument.

The same extension serves the weaker hypothesis under which the obstruction is not asked to vanish
but only to be annihilated by a map of the coefficients: **a homomorphism of the coefficients
killing the inflated everywhere locally trivial obstructions carries a locally trivial class dying
on the kernel into the image of inflation.**

## Main results

* `InverseGalois.CFT.exists_isSmooth₁_extend`: **a smooth one cochain on an open subgroup is the
  restriction of a smooth one cochain on the whole group.**
* `InverseGalois.CFT.exists_comapH2_eq_of_resH2_eq_one`,
  `InverseGalois.CFT.exists_comapH2_eq_of_resH2_eq_one_of_eq_ker`: **a locally trivial class of the
  second cohomology whose restriction to the kernel of a smooth surjection onto a discrete group is
  trivial is inflated from that group.**
* `InverseGalois.CFT.exists_comapH2_eq_coeffH2_of_resH2_eq_one`,
  `InverseGalois.CFT.exists_comapH2_eq_coeffH2_of_resH2_eq_one_of_eq_ker`: **the same after a map of
  the coefficients killing the inflated everywhere locally trivial obstructions.**

## Tags

profinite group, Galois cohomology, inflation, restriction, transgression, open subgroup
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### Extending a smooth cochain from an open subgroup -/

section Extend

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*}

/-- **An open subgroup of an open subgroup is open in the whole group**, the inclusion of an open
subspace being an open map. -/
theorem isOpen_coe_map_subtype {H : Subgroup G} (hH : IsOpen (H : Set G)) {N : Subgroup ↥H}
    (hN : IsOpen (N : Set ↥H)) : IsOpen ((N.map H.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map, Subgroup.coe_subtype]
  exact hH.isOpenMap_subtype_val _ hN

/-- **A smooth one cochain on an open subgroup is the restriction of a smooth one cochain on the
whole group.**  Extend it by one; the open normal subgroup on whose cosets it is constant contains
an open normal subgroup of the ambient group, and translating by an element of that subgroup moves
neither the elements of the subgroup nor those outside it out of their halves. -/
theorem exists_isSmooth₁_extend [One M] (hbasis : HasOpenNormalBasis G) {H : Subgroup G}
    (hH : IsOpen (H : Set G)) {u : ↥H → M} (hu : IsSmooth₁ u) :
    ∃ b : G → M, IsSmooth₁ b ∧ ∀ (x : G) (hx : x ∈ H), b x = u ⟨x, hx⟩ := by
  classical
  obtain ⟨N, hN, hcst⟩ := hu
  obtain ⟨R, hR, hRle⟩ := hbasis (N.map H.subtype) (isOpen_coe_map_subtype hH hN.isOpen)
  have hRH : ∀ g ∈ R, g ∈ H := by
    rintro g hg
    obtain ⟨y, -, rfl⟩ := hRle hg
    exact y.2
  refine ⟨fun g => if hg : g ∈ H then u ⟨g, hg⟩ else 1, ⟨R, hR, fun x n hn => ?_⟩,
    fun x hx => dif_pos hx⟩
  dsimp only
  by_cases hx : x ∈ H
  · have hxn : x * n ∈ H := H.mul_mem hx (hRH n hn)
    obtain ⟨y, hy, hyn⟩ := hRle hn
    rw [dif_pos hxn, dif_pos hx]
    have hmk : (⟨x * n, hxn⟩ : ↥H) = (⟨x, hx⟩ : ↥H) * y := Subtype.ext (by
      rw [Subgroup.coe_mul]
      exact congrArg (x * ·) hyn.symm)
    rw [hmk, hcst ⟨x, hx⟩ y hy]
  · have hxn : x * n ∉ H := fun hc => hx (by
      have hmem := H.mul_mem hc (H.inv_mem (hRH n hn))
      rwa [mul_inv_cancel_right] at hmem)
    rw [dif_neg hxn, dif_neg hx]

end Extend

/-! ### Inflation from the vanishing of the restriction to the kernel -/

section Package

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [CommGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction Q M]
variable {π : G →* Q} (hπ : ∀ (g : G) (m : M), g • m = π g • m)

/-- **A locally trivial class of the second cohomology whose restriction to the kernel of a smooth
surjection onto a discrete group is trivial is inflated from that group**, as soon as the everywhere
locally trivial classes of the first cohomology of the quotient, with values in the first cohomology
of the kernel, are trivial.  The vanishing of the restriction is a primitive of the cocycle on the
kernel, and extending it by one outside the kernel makes it the smooth cochain on the whole group
which the inflation criterion asks for. -/
theorem exists_comapH2_eq_of_resH2_eq_one (hbasis : HasOpenNormalBasis G) (hsm : IsSmoothHom π)
    (hsurj : Function.Surjective π) (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m)
    {S : Set (Subgroup G)} {z : SmoothH2 G M} (hmem : z ∈ sha2 M S)
    (hres : resH2 π.ker z = 1)
    (hsha1 : sha1Level M π.ker (isOpenNormal_ker_of_isSmoothHom hsm).isOpen S = ⊥) :
    ∃ x : SmoothH2 Q M, comapH2 π hπ hsm x = z := by
  obtain ⟨a, ha, has, rfl⟩ := smoothH2Mk_surjective z
  obtain ⟨u, hus, hu⟩ := (resH2_eq_one_iff π.ker ha has).1 hres
  obtain ⟨b, hbs, hb⟩ :=
    exists_isSmooth₁_extend hbasis (isOpenNormal_ker_of_isSmoothHom hsm).isOpen hus
  refine exists_comapH2_eq_of_sha1Level_eq_bot hπ hbasis hsm hsurj htriv ha has hbs ?_ hmem hsha1
  intro x hx y hy
  rw [hb y hy, hb x hx, hb (x * y) (Subgroup.mul_mem _ hx hy)]
  exact (congrFun hu (⟨x, hx⟩, ⟨y, hy⟩)).symm

/-- **A locally trivial class of the second cohomology which dies on a subgroup recognised as the
kernel of a smooth surjection onto a discrete group is inflated from that group.**  This is the
previous statement with the kernel presented by any subgroup equal to it, which is what a Galois
correspondence produces: the automorphisms fixing an intermediate field are the kernel of
restriction to it, but they are named as a fixing subgroup. -/
theorem exists_comapH2_eq_of_resH2_eq_one_of_eq_ker (hbasis : HasOpenNormalBasis G)
    (hsm : IsSmoothHom π) (hsurj : Function.Surjective π)
    (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m) {N : Subgroup G} [N.Normal] (hN : N = π.ker)
    (hop : IsOpen (N : Set G)) {S : Set (Subgroup G)} {z : SmoothH2 G M} (hmem : z ∈ sha2 M S)
    (hres : resH2 N z = 1) (hsha1 : sha1Level M N hop S = ⊥) :
    ∃ x : SmoothH2 Q M, comapH2 π hπ hsm x = z := by
  subst hN
  exact exists_comapH2_eq_of_resH2_eq_one hπ hbasis hsm hsurj htriv hmem hres hsha1

end Package

/-! ### Inflation after a map of the coefficients -/

section PackageCoeff

variable {G Q M M' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [CommGroup M] [CommGroup M']
  [MulDistribMulAction G M] [MulDistribMulAction G M'] [MulDistribMulAction Q M']
variable {π : G →* Q} (hπ' : ∀ (g : G) (m : M'), g • m = π g • m)

/-- **A homomorphism of the coefficients killing the inflated everywhere locally trivial
obstructions carries a locally trivial class of the second cohomology dying on the kernel of a
smooth surjection onto a discrete group into the image of inflation.**  The vanishing of the
restriction is a primitive of the cocycle on the kernel, and extending it by one outside the kernel
makes it the smooth cochain on the whole group which the descent asks for; the obstruction group
itself is not asked to be trivial. -/
theorem exists_comapH2_eq_coeffH2_of_resH2_eq_one (hbasis : HasOpenNormalBasis G)
    (hsm : IsSmoothHom π) (hsurj : Function.Surjective π)
    (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m) (htriv' : ∀ n ∈ π.ker, ∀ m : M', n • m = m)
    (φ : M →* M') (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)
    {S : Set (Subgroup G)} {z : SmoothH2 G M} (hmem : z ∈ sha2 M S) (hres : resH2 π.ker z = 1)
    (hkill : ∀ x ∈ sha1Level M π.ker (isOpenNormal_ker_of_isSmoothHom hsm).isOpen S,
      coeffTransH1 π.ker φ hφ
        (inflH1 π.ker (SmoothH1 ↥π.ker M) (isOpenNormal_ker_of_isSmoothHom hsm).isOpen x) = 1) :
    ∃ y : SmoothH2 Q M', comapH2 π hπ' hsm y = coeffH2 φ hφ z := by
  obtain ⟨a, ha, has, rfl⟩ := smoothH2Mk_surjective z
  obtain ⟨u, hus, hu⟩ := (resH2_eq_one_iff π.ker ha has).1 hres
  obtain ⟨b, hbs, hb⟩ :=
    exists_isSmooth₁_extend hbasis (isOpenNormal_ker_of_isSmoothHom hsm).isOpen hus
  refine exists_comapH2_eq_coeffH2_of_sha1Level hπ' hbasis hsm hsurj htriv htriv' φ hφ
    ha has hbs ?_ hmem hkill
  intro x hx y hy
  rw [hb y hy, hb x hx, hb (x * y) (Subgroup.mul_mem _ hx hy)]
  exact (congrFun hu (⟨x, hx⟩, ⟨y, hy⟩)).symm

/-- **The same with the kernel presented by any subgroup equal to it**, which is what a Galois
correspondence produces: the automorphisms fixing an intermediate field are the kernel of
restriction to it, but they are named as a fixing subgroup. -/
theorem exists_comapH2_eq_coeffH2_of_resH2_eq_one_of_eq_ker (hbasis : HasOpenNormalBasis G)
    (hsm : IsSmoothHom π) (hsurj : Function.Surjective π)
    (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m) (htriv' : ∀ n ∈ π.ker, ∀ m : M', n • m = m)
    (φ : M →* M') (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)
    {N : Subgroup G} [N.Normal] (hN : N = π.ker) (hop : IsOpen (N : Set G))
    {S : Set (Subgroup G)} {z : SmoothH2 G M} (hmem : z ∈ sha2 M S) (hres : resH2 N z = 1)
    (hkill : ∀ x ∈ sha1Level M N hop S,
      coeffTransH1 N φ hφ (inflH1 N (SmoothH1 ↥N M) hop x) = 1) :
    ∃ y : SmoothH2 Q M', comapH2 π hπ' hsm y = coeffH2 φ hφ z := by
  subst hN
  exact exists_comapH2_eq_coeffH2_of_resH2_eq_one hπ' hbasis hsm hsurj htriv htriv' φ hφ hmem hres
    hkill

end PackageCoeff

end InverseGalois.CFT
