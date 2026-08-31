/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Cochain
import InverseGalois.CFT.Profinite.Res

/-!
# The cup product of two classes of the first cohomology of a topological group

A pairing of the coefficients of two smooth modules over a topological group with the coefficients
of a third, multiplicative in each variable and compatible with the three actions, multiplies
smooth cochains: the product of two cochains of degree one is the cochain of degree two whose value
on a pair of group elements is the pairing of the value of the first factor at the first entry with
the translate by that entry of the value of the second factor at the second entry.

The product of two cocycles is a cocycle, the product of two smooth cochains is smooth — the
subgroup at which the product becomes constant is the intersection of the three subgroups at which
the two factors and the action become constant — and a product with a coboundary is a coboundary,
on either side, with an explicit primitive.  So the product descends to classes.

This is the multiplicative mirror, for the cohomology computed by smooth cochains, of the additive
cup product of `InverseGalois.CFT.cup₁₁`.

Pulling a product back along a homomorphism of topological groups is the product of the pullbacks,
so in particular restriction to a subgroup is multiplicative for the cup product.  A product one of
whose factors restricts trivially to every subgroup of a family therefore restricts trivially to
every subgroup of that family: the cup product pairs the everywhere locally trivial classes of the
first cohomology with everything, into the everywhere locally trivial classes of the second.

## Main definitions

* `InverseGalois.CFT.mulCup₁₁`: the product of two cochains of degree one along a pairing of the
  coefficients.
* `InverseGalois.CFT.mulCupCocycle₁₁`: the product of two smooth cocycles of degree one, as a
  smooth cocycle of degree two.
* `InverseGalois.CFT.cupSmoothH1`: **the cup product of two classes of the first cohomology of a
  topological group**, a bimultiplicative map to the second cohomology.

## Main results

* `InverseGalois.CFT.isMulCocycle₂_mulCup₁₁`: **the product of two cocycles of degree one is a
  cocycle of degree two.**
* `InverseGalois.CFT.isSmooth₂_mulCup₁₁`: the product of two smooth cochains is smooth.
* `InverseGalois.CFT.mulCup₁₁_mem_smoothCoboundary₂_left` and
  `InverseGalois.CFT.mulCup₁₁_mem_smoothCoboundary₂_right`: **a product with a coboundary of degree
  one is a coboundary of degree two**, on either side.
* `InverseGalois.CFT.cupSmoothH1_apply`: the cup product of two classes is the class of the product
  of any two cocycles representing them.
* `InverseGalois.CFT.comapH2_cupSmoothH1` and `InverseGalois.CFT.resH2_cupSmoothH1`: **the cup
  product commutes with pullback along a homomorphism**, and hence with restriction to a subgroup.
* `InverseGalois.CFT.cupSmoothH1_mem_sha2_left` and
  `InverseGalois.CFT.cupSmoothH1_mem_sha2_right`: **a cup product one of whose factors is
  everywhere locally trivial is everywhere locally trivial.**

## Tags

profinite group, Galois cohomology, cup product, smooth cochain, cocycle, coboundary
-/

namespace InverseGalois.CFT

open groupCohomology

section Cup

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M N P : Type*} [CommGroup M] [CommGroup N] [CommGroup P]
variable [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G P]

/-- The product of two cochains of degree one along a pairing of the coefficients: its value on a
pair of group elements is the pairing of the value of the first factor at the first entry with the
translate by that entry of the value of the second factor at the second entry. -/
def mulCup₁₁ (Φ : M →* N →* P) (u : G → M) (v : G → N) : G × G → P :=
  fun p => Φ (u p.1) (p.1 • v p.2)

omit [TopologicalSpace G] [MulDistribMulAction G M] [MulDistribMulAction G P] in
@[simp]
theorem mulCup₁₁_apply (Φ : M →* N →* P) (u : G → M) (v : G → N) (x y : G) :
    mulCup₁₁ Φ u v (x, y) = Φ (u x) (x • v y) := rfl

omit [TopologicalSpace G] [MulDistribMulAction G M] [MulDistribMulAction G P] in
theorem mulCup₁₁_mul_left (Φ : M →* N →* P) (u u' : G → M) (v : G → N) :
    mulCup₁₁ Φ (u * u') v = mulCup₁₁ Φ u v * mulCup₁₁ Φ u' v := by
  funext p
  simp [mulCup₁₁]

omit [TopologicalSpace G] [MulDistribMulAction G M] [MulDistribMulAction G P] in
theorem mulCup₁₁_mul_right (Φ : M →* N →* P) (u : G → M) (v v' : G → N) :
    mulCup₁₁ Φ u (v * v') = mulCup₁₁ Φ u v * mulCup₁₁ Φ u v' := by
  funext p
  simp [mulCup₁₁, smul_mul']

omit [TopologicalSpace G] [MulDistribMulAction G M] [MulDistribMulAction G P] in
theorem mulCup₁₁_one_left (Φ : M →* N →* P) (v : G → N) :
    mulCup₁₁ Φ (1 : G → M) v = 1 := by
  funext p
  simp [mulCup₁₁]

omit [TopologicalSpace G] [MulDistribMulAction G M] [MulDistribMulAction G P] in
theorem mulCup₁₁_one_right (Φ : M →* N →* P) (u : G → M) :
    mulCup₁₁ Φ u (1 : G → N) = 1 := by
  funext p
  simp [mulCup₁₁]

omit [TopologicalSpace G] in
/-- **The product of two cocycles of degree one is a cocycle of degree two.**  The cocycle identity
of the first factor splits its value at a product into a translate and a remainder; the translate
pairs with the second factor into the translate of the product, and the remainder pairs with the
cocycle identity of the second factor into the value at the other product. -/
theorem isMulCocycle₂_mulCup₁₁ (Φ : M →* N →* P)
    (hΦ : ∀ (g : G) (m : M) (n : N), Φ (g • m) (g • n) = g • Φ m n)
    {u : G → M} (hu : IsMulCocycle₁ u) {v : G → N} (hv : IsMulCocycle₁ v) :
    IsMulCocycle₂ (mulCup₁₁ Φ u v) := by
  intro g h j
  simp only [mulCup₁₁_apply, hu g h, map_mul, MonoidHom.mul_apply, mul_smul,
    hΦ g (u h) (h • v j)]
  rw [mul_assoc, ← map_mul, ← smul_mul', ← hv h j]

omit [MulDistribMulAction G M] [MulDistribMulAction G P] in
/-- The product of two smooth cochains of degree one is smooth: it becomes constant on the cosets
of the intersection of the two subgroups at which the factors become constant and the subgroup that
acts trivially on the coefficients of the second factor. -/
theorem isSmooth₂_mulCup₁₁ [IsSmoothAction G N] (Φ : M →* N →* P)
    {u : G → M} (hu : IsSmooth₁ u) {v : G → N} (hv : IsSmooth₁ v) :
    IsSmooth₂ (mulCup₁₁ Φ u v) := by
  obtain ⟨K, hK, hu⟩ := hu
  obtain ⟨K', hK', hv⟩ := hv
  obtain ⟨K'', hK'', hact⟩ := IsSmoothAction.exists_isOpenNormal (G := G) (M := N)
  refine ⟨K ⊓ K' ⊓ K'', (hK.inf hK').inf hK'', fun x y n hn m hm => ?_⟩
  simp only [mulCup₁₁_apply, hu x n hn.1.1, hv y m hm.1.2, mul_smul, hact n hn.2]

/-- **The product of a coboundary of degree one with a cocycle of degree one is a coboundary of
degree two**, with primitive the pairing of the coefficient of the coboundary with the cocycle. -/
theorem mulCup₁₁_mem_smoothCoboundary₂_left (Φ : M →* N →* P)
    (hΦ : ∀ (g : G) (m : M) (n : N), Φ (g • m) (g • n) = g • Φ m n)
    {u : G → M} (hu : u ∈ smoothCoboundary₁ G M)
    {v : G → N} (hv : IsMulCocycle₁ v) (hvs : IsSmooth₁ v) :
    mulCup₁₁ Φ u v ∈ smoothCoboundary₂ G P := by
  obtain ⟨s, rfl⟩ := hu
  obtain ⟨K, hK, hvs⟩ := hvs
  refine ⟨fun y => Φ s (v y), ⟨K, hK, fun y m hm => ?_⟩, ?_⟩
  · show Φ s (v (y * m)) = Φ s (v y)
    rw [hvs y m hm]
  funext p
  obtain ⟨x, y⟩ := p
  have hx : x • Φ s (v y) = Φ (x • s) (x • v y) := (hΦ x s (v y)).symm
  rw [coboundary₂_apply, hx, mulCup₁₁_apply, hv x y, map_mul, map_div, MonoidHom.div_apply,
    div_mul_eq_div_div, div_mul_cancel]

/-- **The product of a cocycle of degree one with a coboundary of degree one is a coboundary of
degree two**, with primitive the inverse of the pairing of the cocycle with the translated
coefficient of the coboundary. -/
theorem mulCup₁₁_mem_smoothCoboundary₂_right [IsSmoothAction G N] (Φ : M →* N →* P)
    (hΦ : ∀ (g : G) (m : M) (n : N), Φ (g • m) (g • n) = g • Φ m n)
    {u : G → M} (hu : IsMulCocycle₁ u) (hus : IsSmooth₁ u)
    {v : G → N} (hv : v ∈ smoothCoboundary₁ G N) :
    mulCup₁₁ Φ u v ∈ smoothCoboundary₂ G P := by
  obtain ⟨t, rfl⟩ := hv
  obtain ⟨K, hK, hus⟩ := hus
  obtain ⟨K', hK', hact⟩ := IsSmoothAction.exists_isOpenNormal (G := G) (M := N)
  refine ⟨fun x => (Φ (u x) (x • t))⁻¹, ⟨K ⊓ K', hK.inf hK', fun x n hn => ?_⟩, ?_⟩
  · show (Φ (u (x * n)) ((x * n) • t))⁻¹ = (Φ (u x) (x • t))⁻¹
    rw [hus x n hn.1, mul_smul, hact n hn.2]
  funext p
  obtain ⟨x, y⟩ := p
  have hxy : x • (y • t) = (x * y) • t := (mul_smul x y t).symm
  show x • (Φ (u y) (y • t))⁻¹ / (Φ (u (x * y)) ((x * y) • t))⁻¹ * (Φ (u x) (x • t))⁻¹
      = Φ (u x) (x • (y • t / t))
  rw [smul_inv', ← hΦ x (u y) (y • t), hxy, hu x y, map_mul, MonoidHom.mul_apply,
    smul_div', hxy, map_div, mul_inv, div_mul_cancel_left, inv_inv, ← div_eq_mul_inv]

end Cup

/-! ### The cup product on cohomology -/

section Descent

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M N P : Type*} [CommGroup M] [CommGroup N] [CommGroup P]
variable [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G P]
variable [IsSmoothAction G N]
variable (Φ : M →* N →* P) (hΦ : ∀ (g : G) (m : M) (n : N), Φ (g • m) (g • n) = g • Φ m n)

/-- The product of two smooth cocycles of degree one, as a smooth cocycle of degree two. -/
def mulCupCocycle₁₁ (u : smoothCocycle₁ G M) (v : smoothCocycle₁ G N) : smoothCocycle₂ G P :=
  ⟨mulCup₁₁ Φ u.1 v.1, isMulCocycle₂_mulCup₁₁ Φ hΦ u.2.1 v.2.1,
    isSmooth₂_mulCup₁₁ Φ u.2.2 v.2.2⟩

@[simp]
theorem mulCupCocycle₁₁_coe (u : smoothCocycle₁ G M) (v : smoothCocycle₁ G N) :
    (mulCupCocycle₁₁ Φ hΦ u v : G × G → P) = mulCup₁₁ Φ u.1 v.1 := rfl

/-- The product of a fixed smooth cocycle of degree one with a varying one, as a homomorphism to
the second cohomology. -/
def mulCupHom (u : smoothCocycle₁ G M) : smoothCocycle₁ G N →* SmoothH2 G P where
  toFun v := QuotientGroup.mk (mulCupCocycle₁₁ Φ hΦ u v)
  map_one' := by
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    exact mulCup₁₁_one_right Φ u.1
  map_mul' v v' := by
    rw [← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext (mulCup₁₁_mul_right Φ u.1 v.1 v'.1))

@[simp]
theorem mulCupHom_apply (u : smoothCocycle₁ G M) (v : smoothCocycle₁ G N) :
    mulCupHom Φ hΦ u v = QuotientGroup.mk (mulCupCocycle₁₁ Φ hΦ u v) := rfl

/-- The class of the product of two cocycles of degree one does not change when the second factor
is changed by a coboundary. -/
def mulCupLift (u : smoothCocycle₁ G M) : SmoothH1 G N →* SmoothH2 G P :=
  QuotientGroup.lift _ (mulCupHom Φ hΦ u) fun v hv => by
    rw [MonoidHom.mem_ker, mulCupHom_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact mulCup₁₁_mem_smoothCoboundary₂_right Φ hΦ u.2.1 u.2.2
      ((Subgroup.mem_subgroupOf).1 hv)

@[simp]
theorem mulCupLift_mk (u : smoothCocycle₁ G M) (v : smoothCocycle₁ G N) :
    mulCupLift Φ hΦ u (QuotientGroup.mk v) = QuotientGroup.mk (mulCupCocycle₁₁ Φ hΦ u v) := rfl

/-- The product of two smooth cocycles of degree one, as a homomorphism in the first factor with
values in the homomorphisms from the first cohomology to the second. -/
def mulCupLiftHom : smoothCocycle₁ G M →* SmoothH1 G N →* SmoothH2 G P where
  toFun u := mulCupLift Φ hΦ u
  map_one' := by
    refine MonoidHom.ext fun x => ?_
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
    rw [mulCupLift_mk, MonoidHom.one_apply, ← QuotientGroup.mk_one]
    exact congrArg QuotientGroup.mk (Subtype.ext (mulCup₁₁_one_left Φ v.1))
  map_mul' u u' := by
    refine MonoidHom.ext fun x => ?_
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
    rw [mulCupLift_mk, MonoidHom.mul_apply, mulCupLift_mk, mulCupLift_mk, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext (mulCup₁₁_mul_left Φ u.1 u'.1 v.1))

@[simp]
theorem mulCupLiftHom_apply (u : smoothCocycle₁ G M) :
    mulCupLiftHom Φ hΦ u = mulCupLift Φ hΦ u := rfl

/-- **The cup product of two classes of the first cohomology of a topological group**, a
bimultiplicative map to the second cohomology of the coefficients paired. -/
def cupSmoothH1 : SmoothH1 G M →* SmoothH1 G N →* SmoothH2 G P :=
  QuotientGroup.lift _ (mulCupLiftHom Φ hΦ) fun u hu => by
    rw [MonoidHom.mem_ker]
    refine MonoidHom.ext fun x => ?_
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
    rw [mulCupLiftHom_apply, mulCupLift_mk, MonoidHom.one_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact mulCup₁₁_mem_smoothCoboundary₂_left Φ hΦ ((Subgroup.mem_subgroupOf).1 hu) v.2.1 v.2.2

/-- **The cup product of two classes is the class of the product of any two cocycles representing
them.** -/
@[simp]
theorem cupSmoothH1_apply {u : G → M} (hu : IsMulCocycle₁ u) (hus : IsSmooth₁ u)
    {v : G → N} (hv : IsMulCocycle₁ v) (hvs : IsSmooth₁ v) :
    cupSmoothH1 Φ hΦ (smoothH1Mk u hu hus) (smoothH1Mk v hv hvs)
      = smoothH2Mk (mulCup₁₁ Φ u v) (isMulCocycle₂_mulCup₁₁ Φ hΦ hu hv)
          (isSmooth₂_mulCup₁₁ Φ hus hvs) := rfl

end Descent

/-! ### Pulling a product back along a homomorphism -/

section Comap

variable {G Q : Type*} [Group G] [Group Q]
variable {M N P : Type*} [CommGroup M] [CommGroup N] [CommGroup P]
variable [MulDistribMulAction G N] [MulDistribMulAction Q N]

/-- **The pullback of a product of two cochains of degree one is the product of the pullbacks**,
for a homomorphism along which the action on the second factor of the pairing is compatible. -/
theorem comap₂_mulCup₁₁ (Φ : M →* N →* P) {π : G →* Q}
    (hπ : ∀ (g : G) (n : N), g • n = π g • n) (u : Q → M) (v : Q → N) :
    comap₂ π (mulCup₁₁ Φ u v) = mulCup₁₁ Φ (comap₁ π u) (comap₁ π v) := by
  funext p
  obtain ⟨x, y⟩ := p
  show Φ (u (π x)) (π x • v (π y)) = Φ (u (π x)) (x • v (π y))
  rw [hπ x (v (π y))]

end Comap

section ComapClass

variable {G Q : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
variable {M N P : Type*} [CommGroup M] [CommGroup N] [CommGroup P]
variable [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G P]
variable [MulDistribMulAction Q M] [MulDistribMulAction Q N] [MulDistribMulAction Q P]
variable [IsSmoothAction G N] [IsSmoothAction Q N]

/-- **The cup product commutes with pullback along a homomorphism of topological groups.** -/
theorem comapH2_cupSmoothH1 (Φ : M →* N →* P)
    (hΦG : ∀ (g : G) (m : M) (n : N), Φ (g • m) (g • n) = g • Φ m n)
    (hΦQ : ∀ (q : Q) (m : M) (n : N), Φ (q • m) (q • n) = q • Φ m n)
    {π : G →* Q} (hπM : ∀ (g : G) (m : M), g • m = π g • m)
    (hπN : ∀ (g : G) (n : N), g • n = π g • n)
    (hπP : ∀ (g : G) (p : P), g • p = π g • p) (hsm : IsSmoothHom π)
    (α : SmoothH1 Q M) (β : SmoothH1 Q N) :
    comapH2 π hπP hsm (cupSmoothH1 Φ hΦQ α β)
      = cupSmoothH1 Φ hΦG (comapH1 π hπM hsm α) (comapH1 π hπN hsm β) := by
  obtain ⟨u, hu, hus, rfl⟩ := smoothH1Mk_surjective α
  obtain ⟨v, hv, hvs, rfl⟩ := smoothH1Mk_surjective β
  rw [cupSmoothH1_apply, comapH2_smoothH2Mk, comapH1_smoothH1Mk, comapH1_smoothH1Mk,
    cupSmoothH1_apply]
  exact congrArg QuotientGroup.mk (Subtype.ext (comap₂_mulCup₁₁ Φ hπN u v))

end ComapClass

/-! ### Restriction of a product, and the everywhere locally trivial classes -/

section Res

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M N P : Type*} [CommGroup M] [CommGroup N] [CommGroup P]
variable [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G P]
variable [IsSmoothAction G N]
variable (Φ : M →* N →* P) (hΦ : ∀ (g : G) (m : M) (n : N), Φ (g • m) (g • n) = g • Φ m n)

/-- **The cup product commutes with restriction to a subgroup.** -/
theorem resH2_cupSmoothH1 (H : Subgroup G) (α : SmoothH1 G M) (β : SmoothH1 G N) :
    resH2 H (cupSmoothH1 Φ hΦ α β)
      = cupSmoothH1 (G := ↥H) Φ (fun h m n => hΦ (h : G) m n) (resH1 H α) (resH1 H β) :=
  comapH2_cupSmoothH1 (G := ↥H) (Q := G) (π := H.subtype) Φ (fun h m n => hΦ (h : G) m n) hΦ
    (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (isSmoothHom_subtype H) α β

/-- **A cup product whose first factor is everywhere locally trivial is everywhere locally
trivial.** -/
theorem cupSmoothH1_mem_sha2_left {S : Set (Subgroup G)} {α : SmoothH1 G M}
    (hα : α ∈ sha1 M S) (β : SmoothH1 G N) : cupSmoothH1 Φ hΦ α β ∈ sha2 P S := by
  refine mem_sha2.2 fun D hD => ?_
  rw [resH2_cupSmoothH1, mem_sha1.1 hα D hD, map_one, MonoidHom.one_apply]

/-- **A cup product whose second factor is everywhere locally trivial is everywhere locally
trivial.** -/
theorem cupSmoothH1_mem_sha2_right {S : Set (Subgroup G)} (α : SmoothH1 G M)
    {β : SmoothH1 G N} (hβ : β ∈ sha1 N S) : cupSmoothH1 Φ hΦ α β ∈ sha2 P S := by
  refine mem_sha2.2 fun D hD => ?_
  rw [resH2_cupSmoothH1, mem_sha1.1 hβ D hD, map_one]

end Res

end InverseGalois.CFT
