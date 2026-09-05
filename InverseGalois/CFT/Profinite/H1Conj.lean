/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Res

/-!
# The conjugation action on the first cohomology of a normal subgroup

An element of a topological group conjugates a normal subgroup into itself, so it carries a cochain
on the subgroup to another one; combining that substitution with the action on the coefficients
preserves cocycles, coboundaries and smoothness, and therefore acts on the first cohomology of the
subgroup.  The subgroup itself acts trivially: conjugating a cocycle by an element of the subgroup
changes it by the coboundary of the value the cocycle already takes there.  So the first cohomology
of a normal subgroup is a module over the quotient, and the module is smooth as soon as the subgroup
is open.

This is the coefficient module of the transgression of the inflation-restriction sequence, and for
the Galois group of a number field and the subgroup fixing a finite Galois extension it is the
module which Kummer theory identifies with the units of that extension modulo powers.

## Main definitions

* `InverseGalois.CFT.conjMemHom`: conjugation of a normal subgroup by an element of the ambient
  group, as an endomorphism of the subgroup.
* `InverseGalois.CFT.conjCochain`: the conjugate of a cochain on the subgroup.
* `InverseGalois.CFT.conjH1`: **the conjugation action on the first cohomology of the subgroup.**
* `InverseGalois.CFT.conjMulDistribMulAction`: that action, packaged as a module structure.

## Main results

* `InverseGalois.CFT.conjH1_smoothH1Mk`: the action read on the class of a cocycle.
* `InverseGalois.CFT.conjCochain_eq_mul_of_mem`: conjugating a cocycle by an element of the
  subgroup multiplies it by a coboundary.
* `InverseGalois.CFT.conjH1_eq_self_of_mem`: **the subgroup acts trivially**, so the action is one
  of the quotient.
* `InverseGalois.CFT.exists_isOpenNormal_conjH1_eq_self`: the action is smooth when the subgroup is
  open.

## Tags

profinite group, Galois cohomology, normal subgroup, conjugation, inflation-restriction,
transgression
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### Two elementary facts about one cocycles -/

section Cocycle

variable {H M : Type*} [Group H] [CommGroup M] [MulDistribMulAction H M]

/-- A one cocycle takes the value one at the unit. -/
theorem map_one_of_isMulCocycle₁ {u : H → M} (hu : IsMulCocycle₁ u) : u 1 = 1 := by
  have h := hu 1 1
  rw [mul_one, one_smul] at h
  exact left_eq_mul.1 h

/-- The value of a one cocycle at an inverse. -/
theorem map_inv_of_isMulCocycle₁ {u : H → M} (hu : IsMulCocycle₁ u) (a : H) :
    u a⁻¹ = a⁻¹ • (u a)⁻¹ := by
  have h := hu a a⁻¹
  rw [mul_inv_cancel, map_one_of_isMulCocycle₁ hu] at h
  have h2 : a • u a⁻¹ = (u a)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    exact h.symm
  rw [← h2, inv_smul_smul]

end Cocycle

/-! ### Two classes of the first cohomology agree when their quotient is a coboundary -/

section Eq

variable {H : Type*} [Group H] [TopologicalSpace H]
variable {M : Type*} [CommGroup M] [MulDistribMulAction H M]

/-- **Two smooth one cocycles have the same class exactly when their quotient is a coboundary.** -/
theorem smoothH1Mk_eq_iff {u v : H → M} (hu : IsMulCocycle₁ u) (hus : IsSmooth₁ u)
    (hv : IsMulCocycle₁ v) (hvs : IsSmooth₁ v) :
    smoothH1Mk u hu hus = smoothH1Mk v hv hvs ↔
      ∃ t : M, (fun g : H => g • t / t) = fun g => u g / v g := by
  have hfun : (v⁻¹ * u : H → M) = fun g => u g / v g := by
    funext g
    show (v g)⁻¹ * u g = u g / v g
    rw [div_eq_mul_inv, mul_comm]
  have hkey : (smoothH1Mk v hv hvs = smoothH1Mk u hu hus) ↔
      ((⟨v, hv, hvs⟩ : smoothCocycle₁ H M)⁻¹ * ⟨u, hu, hus⟩ ∈
        (smoothCoboundary₁ H M).subgroupOf (smoothCocycle₁ H M)) := QuotientGroup.eq
  rw [eq_comm, hkey, Subgroup.mem_subgroupOf]
  show (v⁻¹ * u : H → M) ∈ smoothCoboundary₁ H M ↔ _
  rw [hfun]
  exact Iff.rfl

end Eq

/-! ### Conjugation of a normal subgroup -/

section Conj

variable {G : Type*} [Group G] {N : Subgroup G}
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- The conjugate `σ⁻¹ x σ` of an element of a normal subgroup, again in the subgroup. -/
def conjMem (hN : N.Normal) (σ : G) (x : ↥N) : ↥N :=
  ⟨σ⁻¹ * (x : G) * σ, by simpa using hN.conj_mem (x : G) x.2 σ⁻¹⟩

@[simp]
theorem conjMem_coe (hN : N.Normal) (σ : G) (x : ↥N) :
    ((conjMem hN σ x : ↥N) : G) = σ⁻¹ * (x : G) * σ := rfl

/-- **Conjugation by an element of the ambient group, as an endomorphism of a normal
subgroup.** -/
def conjMemHom (hN : N.Normal) (σ : G) : ↥N →* ↥N where
  toFun := conjMem hN σ
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    simp only [conjMem_coe, Subgroup.coe_mul]
    group)

@[simp]
theorem conjMemHom_coe (hN : N.Normal) (σ : G) (x : ↥N) :
    ((conjMemHom hN σ x : ↥N) : G) = σ⁻¹ * (x : G) * σ := rfl

@[simp]
theorem conjMemHom_one (hN : N.Normal) (x : ↥N) : conjMemHom hN 1 x = x :=
  Subtype.ext (by simp)

/-- Conjugating twice is conjugating by the product. -/
theorem conjMemHom_comp (hN : N.Normal) (σ τ : G) (x : ↥N) :
    conjMemHom hN τ (conjMemHom hN σ x) = conjMemHom hN (σ * τ) x :=
  Subtype.ext (by simp only [conjMemHom_coe, mul_inv_rev]; group)

/-! ### Conjugation of a cochain -/

/-- **The conjugate of a cochain on a normal subgroup** by an element of the ambient group. -/
def conjCochain (hN : N.Normal) (σ : G) (u : ↥N → M) : ↥N → M :=
  fun x => σ • u (conjMemHom hN σ x)

theorem conjCochain_apply (hN : N.Normal) (σ : G) (u : ↥N → M) (x : ↥N) :
    conjCochain hN σ u x = σ • u (conjMemHom hN σ x) := rfl

@[simp]
theorem conjCochain_one (hN : N.Normal) (u : ↥N → M) : conjCochain hN 1 u = u := by
  funext x
  rw [conjCochain_apply, conjMemHom_one, one_smul]

/-- Conjugating a cochain twice is conjugating by the product. -/
theorem conjCochain_comp (hN : N.Normal) (σ τ : G) (u : ↥N → M) :
    conjCochain hN σ (conjCochain hN τ u) = conjCochain hN (σ * τ) u := by
  funext x
  rw [conjCochain_apply, conjCochain_apply, conjCochain_apply, conjMemHom_comp, mul_smul]

theorem conjCochain_mul (hN : N.Normal) (σ : G) (u v : ↥N → M) :
    conjCochain hN σ (u * v) = conjCochain hN σ u * conjCochain hN σ v := by
  funext x
  show σ • (u (conjMemHom hN σ x) * v (conjMemHom hN σ x)) = _
  rw [smul_mul']
  rfl

/-- Conjugation moves the coefficients through the action of the subgroup. -/
theorem smul_conjMemHom_smul (hN : N.Normal) (σ : G) (x : ↥N) (m : M) :
    σ • ((conjMemHom hN σ x) • m) = (x : G) • (σ • m) := by
  show σ • ((σ⁻¹ * (x : G) * σ) • m) = (x : G) • (σ • m)
  rw [← mul_smul, ← mul_smul]
  congr 1
  group

/-- **The conjugate of a one cocycle is a one cocycle.** -/
theorem isMulCocycle₁_conjCochain (hN : N.Normal) {u : ↥N → M} (hu : IsMulCocycle₁ u) (σ : G) :
    IsMulCocycle₁ (conjCochain hN σ u) := by
  intro x y
  show σ • u (conjMemHom hN σ (x * y)) = (x : G) • (σ • u (conjMemHom hN σ y))
    * σ • u (conjMemHom hN σ x)
  rw [map_mul, hu, smul_mul', smul_conjMemHom_smul]

/-- **The conjugate of a coboundary is a coboundary.** -/
theorem conjCochain_smul_div (hN : N.Normal) (σ : G) (t : M) :
    conjCochain hN σ (fun x : ↥N => x • t / t) = fun x : ↥N => x • (σ • t) / (σ • t) := by
  funext x
  show σ • ((conjMemHom hN σ x) • t / t) = (x : G) • (σ • t) / (σ • t)
  rw [smul_div', smul_conjMemHom_smul]

/-- **Conjugating a one cocycle by an element of the subgroup multiplies it by the coboundary of
the value the cocycle takes there.** -/
theorem conjCochain_eq_mul_of_mem (hN : N.Normal) {u : ↥N → M} (hu : IsMulCocycle₁ u) {g : G}
    (hg : g ∈ N) :
    conjCochain hN g u = u * fun x : ↥N => x • u ⟨g, hg⟩ / u ⟨g, hg⟩ := by
  set a : ↥N := ⟨g, hg⟩ with ha
  funext x
  have hax : conjMemHom hN g x = a⁻¹ * x * a := Subtype.ext (by simp [ha])
  have h1 : u (a⁻¹ * x * a) = a⁻¹ • ((x : ↥N) • u a * u x) * (a⁻¹ • (u a)⁻¹) := by
    rw [mul_assoc, hu a⁻¹ (x * a), hu x a, map_inv_of_isMulCocycle₁ hu]
  show (a : ↥N) • u (conjMemHom hN g x) = u x * ((x : ↥N) • u a / u a)
  rw [hax, h1, smul_mul', smul_inv_smul, smul_inv_smul]
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

end Conj

/-! ### The action on cohomology -/

section ConjTop

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] {N : Subgroup G}
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- Conjugation of a normal subgroup is continuous. -/
theorem continuous_conjMemHom (hN : N.Normal) (σ : G) :
    Continuous (conjMemHom hN σ) :=
  Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

/-- **The conjugate of a smooth cochain is smooth.** -/
theorem isSmooth₁_conjCochain (hN : N.Normal) {u : ↥N → M} (hs : IsSmooth₁ u)
    (σ : G) : IsSmooth₁ (conjCochain hN σ u) := by
  obtain ⟨R, hR, hu⟩ := hs
  refine ⟨R.comap (conjMemHom hN σ), ⟨hR.normal.comap _, ?_⟩, fun x n hn => ?_⟩
  · rw [Subgroup.coe_comap]
    exact hR.isOpen.preimage (continuous_conjMemHom hN σ)
  · show σ • u (conjMemHom hN σ (x * n)) = σ • u (conjMemHom hN σ x)
    rw [map_mul, hu _ _ hn]

/-- Conjugation as an endomorphism of the smooth one cocycles of a normal subgroup. -/
def conjCocycleHom (hN : N.Normal) (σ : G) :
    smoothCocycle₁ ↥N M →* smoothCocycle₁ ↥N M where
  toFun u := ⟨conjCochain hN σ (u : ↥N → M), isMulCocycle₁_conjCochain hN u.2.1 σ,
    isSmooth₁_conjCochain hN u.2.2 σ⟩
  map_one' := Subtype.ext (funext fun _ => by
    show σ • (1 : M) = 1
    rw [smul_one])
  map_mul' u v := Subtype.ext (conjCochain_mul hN σ (u : ↥N → M) (v : ↥N → M))

/-- **The conjugation action on the first cohomology of a normal subgroup.** -/
def conjH1 (hN : N.Normal) (σ : G) : SmoothH1 ↥N M →* SmoothH1 ↥N M :=
  QuotientGroup.map _ _ (conjCocycleHom hN σ) <| by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨t, ht⟩ := hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact ⟨σ • t, (conjCochain_smul_div hN σ t).symm.trans (congrArg (conjCochain hN σ) ht)⟩

@[simp]
theorem conjH1_smoothH1Mk (hN : N.Normal) (σ : G) {u : ↥N → M}
    (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) :
    conjH1 hN σ (smoothH1Mk u hu hs)
      = smoothH1Mk (conjCochain hN σ u) (isMulCocycle₁_conjCochain hN hu σ)
        (isSmooth₁_conjCochain hN hs σ) := rfl

/-- The unit acts as the identity. -/
theorem conjH1_one (hN : N.Normal) (z : SmoothH1 ↥N M) :
    conjH1 (M := M) hN 1 z = z := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  rw [conjH1_smoothH1Mk, (smoothH1Mk_eq_iff _ _ hu hs)]
  exact ⟨1, by funext x; rw [conjCochain_one]; simp⟩

/-- Acting twice is acting by the product. -/
theorem conjH1_comp (hN : N.Normal) (σ τ : G) (z : SmoothH1 ↥N M) :
    conjH1 hN σ (conjH1 hN τ z) = conjH1 (M := M) hN (σ * τ) z := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  rw [conjH1_smoothH1Mk, conjH1_smoothH1Mk, conjH1_smoothH1Mk,
    (smoothH1Mk_eq_iff _ _ (isMulCocycle₁_conjCochain hN hu (σ * τ))
      (isSmooth₁_conjCochain hN hs (σ * τ)))]
  exact ⟨1, by funext x; rw [conjCochain_comp]; simp⟩

/-- **The conjugation action of the ambient group on the first cohomology of a normal
subgroup.** -/
def conjMulDistribMulAction (hN : N.Normal) :
    MulDistribMulAction G (SmoothH1 ↥N M) where
  smul σ z := conjH1 hN σ z
  one_smul := conjH1_one hN
  mul_smul σ τ z := (conjH1_comp hN σ τ z).symm
  smul_mul σ z w := map_mul (conjH1 hN σ) z w
  smul_one σ := map_one (conjH1 hN σ)

/-- **An element of the subgroup acts trivially on the first cohomology of the subgroup**, so the
conjugation action is an action of the quotient. -/
theorem conjH1_eq_self_of_mem (hN : N.Normal) {g : G} (hg : g ∈ N)
    (z : SmoothH1 ↥N M) : conjH1 hN g z = z := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  rw [conjH1_smoothH1Mk, (smoothH1Mk_eq_iff _ _ hu hs)]
  refine ⟨u ⟨g, hg⟩, funext fun x => ?_⟩
  rw [conjCochain_eq_mul_of_mem hN hu hg]
  show (x : ↥N) • u ⟨g, hg⟩ / u ⟨g, hg⟩ = u x * ((x : ↥N) • u ⟨g, hg⟩ / u ⟨g, hg⟩) / u x
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_div]
  abel

/-- **The conjugation action is smooth when the subgroup is open**: the subgroup itself is an open
normal subgroup acting trivially. -/
theorem exists_isOpenNormal_conjH1_eq_self (hN : IsOpenNormal N) :
    ∃ R : Subgroup G, IsOpenNormal R ∧
      ∀ n ∈ R, ∀ z : SmoothH1 ↥N M, conjH1 hN.normal n z = z :=
  ⟨N, hN, fun _ hn z => conjH1_eq_self_of_mem hN.normal hn z⟩

end ConjTop

end InverseGalois.CFT
