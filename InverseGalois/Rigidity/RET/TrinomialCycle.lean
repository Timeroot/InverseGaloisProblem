/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.TrinomialOrd
import InverseGalois.Rigidity.RET.InertiaGen

/-!
# The local monodromy of the trinomial family over the origin

At a place of the trinomial cover lying over the origin all the roots of

`Y ^ (m + 1) - c X ^ m Y - X ^ m`

vanish to one and the same order, and any two of them agree one step beyond that order after
rescaling by exactly one `(m+1)`-st root of unity.  That root of unity is a function of the pair of
roots, and this file develops it: it is multiplicative in the sense of a cocycle, invariant under
the deck transformations that fix the place, and it separates the roots.

The consequence is the arithmetic of a totally ramified fibre.  A deck transformation which fixes
the place and one root fixes them all, hence is the identity; so the decomposition group — which at
a geometric place is the whole inertia group — acts *freely* on the roots.  Comparing the ratio at
`σ y` with the ratio at `y` turns the cocycle into a genuine character of that group with values in
the `(m+1)`-st roots of unity, injective because the action is free.

## Main definitions

* `Rigidity.RET.rootRatio` — the root of unity relating two roots beyond their common order.
* `Rigidity.RET.inertiaChar` — the character of the decomposition group it induces.

## Main results

* `Rigidity.RET.rootRatio_mul` — the cocycle relation.
* `Rigidity.RET.rootRatio_smul` — invariance under a deck transformation fixing the place.
* `Rigidity.RET.eq_one_of_fixes_root` — the decomposition group acts freely on the roots.
* `Rigidity.RET.inertiaChar_injective` — the induced character is injective.
-/

open Polynomial IsDedekindDomain Pointwise

noncomputable section

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

attribute [local instance] Rigidity.RET.instSMulCommDeck

variable {m : ℕ} {c : k}

/-! ### Constants of the base, and the action of the deck group on them -/

/-- The constants of the base multiply inside the integral model. -/
theorem baseC_mul (L : LineCover) (a b : k) : baseC L (a * b) = baseC L a * baseC L b := by
  rw [baseC, Polynomial.C_mul, map_mul]

/-- **The deck group fixes the constants of the base.** -/
theorem smul_baseC (L : LineCover) (σ : L.deck) (a : k) : σ • baseC L a = baseC L a :=
  smul_algebraMap_poly (Ω := L.M) σ (Polynomial.C a)

/-- **Vanishing to a prescribed order at a place is preserved by the deck transformations fixing
that place.** -/
theorem smul_mem_pow_of_smul_asIdeal_eq (L : LineCover) {v : HeightOneSpectrum (Bring L.M)}
    {σ : L.deck} (hσ : σ • v.asIdeal = v.asIdeal) {x : Bring L.M} {j : ℕ}
    (h : x ∈ v.asIdeal ^ j) : σ • x ∈ v.asIdeal ^ j := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
    exact Ideal.zero_mem _
  · refine mem_pow_of_le_intOrd (K := L.M) ?_
    rw [intOrd_smul_eq hσ]
    exact le_intOrd_of_mem_pow (K := L.M) hx h

/-! ### The root of unity relating two elements -/

/-- **At most one constant brings an element into agreement with a multiple of a second one beyond
the order of that second one**: two such constants would differ by a unit. -/
theorem baseC_inj_of_mem_pow (L : LineCover) {v : HeightOneSpectrum (Bring L.M)}
    {y y' : Bring L.M} (hy' : y' ≠ 0) {ζ ζ' : k}
    (h : y - baseC L ζ * y' ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1))
    (h' : y - baseC L ζ' * y' ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1)) : ζ = ζ' := by
  by_contra hne
  have hd : ζ' - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hmem : baseC L (ζ' - ζ) * y' ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1) := by
    have hsub := Ideal.sub_mem _ h h'
    have heq : (y - baseC L ζ * y') - (y - baseC L ζ' * y') = baseC L (ζ' - ζ) * y' := by
      rw [baseC_sub]; ring
    rwa [heq] at hsub
  have hne0 : baseC L (ζ' - ζ) * y' ≠ 0 := mul_ne_zero (baseC_ne_zero L hd) hy'
  have hle := le_intOrd_of_mem_pow (K := L.M) hne0 hmem
  rw [intOrd_mul (baseC_ne_zero L hd) hy', intOrd_eq_zero_of_isUnit (isUnit_baseC L hd),
    zero_add] at hle
  have hnn : 0 ≤ intOrd L.M v y' := intOrd_nonneg y'
  push_cast at hle
  omega

open Classical in
/-- **The root of unity relating two elements at a place**: the constant `ζ` of order dividing `n`
for which `y - ζ y'` vanishes one step beyond `y'` itself, when there is one. -/
def rootRatio (L : LineCover) (v : HeightOneSpectrum (Bring L.M)) (n : ℕ)
    (y y' : Bring L.M) : k :=
  if h : ∃ ζ : k, ζ ^ n = 1 ∧
      y - baseC L ζ * y' ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1) then h.choose else 1

/-- The defining property of the relating root of unity, whenever one exists. -/
theorem rootRatio_spec (L : LineCover) {v : HeightOneSpectrum (Bring L.M)} {n : ℕ}
    {y y' : Bring L.M}
    (hex : ∃ ζ : k, ζ ^ n = 1 ∧
      y - baseC L ζ * y' ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1)) :
    rootRatio L v n y y' ^ n = 1 ∧
      y - baseC L (rootRatio L v n y y') * y'
        ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1) := by
  unfold rootRatio
  rw [dif_pos hex]
  exact hex.choose_spec

/-- **The relating constant is determined by its defining property.** -/
theorem rootRatio_eq_of_mem (L : LineCover) {v : HeightOneSpectrum (Bring L.M)} {n : ℕ}
    {y y' : Bring L.M} (hy' : y' ≠ 0)
    (hex : ∃ ζ : k, ζ ^ n = 1 ∧
      y - baseC L ζ * y' ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1))
    {ζ : k} (hζ : y - baseC L ζ * y' ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1)) :
    rootRatio L v n y y' = ζ :=
  baseC_inj_of_mem_pow L hy' (rootRatio_spec L hex).2 hζ

/-- An element relates to itself by `1`. -/
theorem rootRatio_self (L : LineCover) {v : HeightOneSpectrum (Bring L.M)} {n : ℕ}
    {y : Bring L.M} (hy : y ≠ 0) : rootRatio L v n y y = 1 := by
  have hmem : y - baseC L 1 * y ∈ v.asIdeal ^ ((intOrd L.M v y).toNat + 1) := by
    rw [baseC_one, one_mul, sub_self]
    exact Ideal.zero_mem _
  exact rootRatio_eq_of_mem L hy ⟨1, one_pow n, hmem⟩ hmem

/-! ### The relating root of unity for two roots of the trinomial family -/

/-- **Two roots of the trinomial family are related by an `(m+1)`-st root of unity** at a place
where the coordinate vanishes. -/
theorem exists_rootRatio (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L)) {y y' : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M))
    (hy' : y' ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    ∃ ζ : k, ζ ^ (m + 1) = 1 ∧
      y - baseC L ζ * y' ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1) := by
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_base (m + 1) (Nat.succ_pos m)
  obtain ⟨i, hi, -⟩ := exists_unique_root_label L hm hc hX hω hy hy'
  refine ⟨ω ^ (i : ℕ), ?_, hi⟩
  rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]

/-- **The relating root of unity is a cocycle**: relating through a third root multiplies the two
constants. -/
theorem rootRatio_mul (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L))
    {y y' y'' : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M))
    (hy' : y' ∈ (ramTrinomial m c).rootSet (Bring L.M))
    (hy'' : y'' ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    rootRatio L v (m + 1) y y''
      = rootRatio L v (m + 1) y y' * rootRatio L v (m + 1) y' y'' := by
  have hy''0 : y'' ≠ 0 := root_ne_zero L hy''
  have hord : intOrd L.M v y' = intOrd L.M v y'' := intOrd_root_eq_intOrd_root L hm hX hy' hy''
  have h1 := (rootRatio_spec L (exists_rootRatio L hm hc hX hy hy')).2
  have h2 := (rootRatio_spec L (exists_rootRatio L hm hc hX hy' hy'')).2
  rw [← hord] at h2
  have h3 : baseC L (rootRatio L v (m + 1) y y') * y'
      - baseC L (rootRatio L v (m + 1) y y' * rootRatio L v (m + 1) y' y'') * y''
      ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1) := by
    have hmul := Ideal.mul_mem_left (v.asIdeal ^ ((intOrd L.M v y').toNat + 1))
      (baseC L (rootRatio L v (m + 1) y y')) h2
    have heq : baseC L (rootRatio L v (m + 1) y y')
          * (y' - baseC L (rootRatio L v (m + 1) y' y'') * y'')
        = baseC L (rootRatio L v (m + 1) y y') * y'
          - baseC L (rootRatio L v (m + 1) y y' * rootRatio L v (m + 1) y' y'') * y'' := by
      rw [baseC_mul]; ring
    rwa [heq] at hmul
  have h4 : y - baseC L (rootRatio L v (m + 1) y y' * rootRatio L v (m + 1) y' y'') * y''
      ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1) := by
    have hsum := Ideal.add_mem _ h1 h3
    have heq : (y - baseC L (rootRatio L v (m + 1) y y') * y')
          + (baseC L (rootRatio L v (m + 1) y y') * y'
            - baseC L (rootRatio L v (m + 1) y y' * rootRatio L v (m + 1) y' y'') * y'')
        = y - baseC L (rootRatio L v (m + 1) y y' * rootRatio L v (m + 1) y' y'') * y'' := by
      ring
    rwa [heq] at hsum
  rw [hord] at h4
  exact rootRatio_eq_of_mem L hy''0 (exists_rootRatio L hm hc hX hy hy'') h4

/-- **The relating root of unity is invariant under a deck transformation fixing the place.** -/
theorem rootRatio_smul (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L))
    {σ : L.deck} (hσ : σ • v.asIdeal = v.asIdeal) {y y' : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M))
    (hy' : y' ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    rootRatio L v (m + 1) (σ • y) (σ • y') = rootRatio L v (m + 1) y y' := by
  have hsy : σ • y ∈ (ramTrinomial m c).rootSet (Bring L.M) := Polynomial.smul_mem_rootSet σ hy
  have hsy' : σ • y' ∈ (ramTrinomial m c).rootSet (Bring L.M) := Polynomial.smul_mem_rootSet σ hy'
  have hsy'0 : σ • y' ≠ 0 := root_ne_zero L hsy'
  have hord : intOrd L.M v (σ • y') = intOrd L.M v y' := intOrd_smul_eq hσ y'
  have h1 := (rootRatio_spec L (exists_rootRatio L hm hc hX hy hy')).2
  have h2 : σ • (y - baseC L (rootRatio L v (m + 1) y y') * y')
      ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1) :=
    smul_mem_pow_of_smul_asIdeal_eq L hσ h1
  rw [smul_sub, smul_mul', smul_baseC, ← hord] at h2
  exact rootRatio_eq_of_mem L hsy'0 (exists_rootRatio L hm hc hX hsy hsy') h2

/-- **The relating root of unity separates the roots**: two roots relating to a third by the same
constant are equal. -/
theorem eq_of_rootRatio_eq (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L))
    {y y' y'' : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M))
    (hy' : y' ∈ (ramTrinomial m c).rootSet (Bring L.M))
    (hy'' : y'' ∈ (ramTrinomial m c).rootSet (Bring L.M))
    (h : rootRatio L v (m + 1) y y'' = rootRatio L v (m + 1) y' y'') : y = y' := by
  by_contra hne
  have h1 := (rootRatio_spec L (exists_rootRatio L hm hc hX hy hy'')).2
  have h2 := (rootRatio_spec L (exists_rootRatio L hm hc hX hy' hy'')).2
  rw [← h] at h2
  have hsub : y - y' ∈ v.asIdeal ^ ((intOrd L.M v y'').toNat + 1) := by
    have hd := Ideal.sub_mem _ h1 h2
    have heq : (y - baseC L (rootRatio L v (m + 1) y y'') * y'')
        - (y' - baseC L (rootRatio L v (m + 1) y y'') * y'') = y - y' := by ring
    rwa [heq] at hd
  rw [← intOrd_root_eq_intOrd_root L hm hX hy' hy''] at hsub
  exact sub_notMem_pow_of_ne L hm hc hX hy hy' hne hsub

/-! ### The decomposition group acts freely on the roots -/

/-- **A deck transformation fixing a place over the origin and one root of the trinomial family is
the identity.**  Relating every root to the fixed one produces the same constant before and after
the transformation, so every root is fixed, and the action on the roots is faithful. -/
theorem eq_one_of_fixes_root (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly (ramTrinomial m c))]
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L))
    {σ : L.deck} (hσ : σ • v.asIdeal = v.asIdeal) {y₀ : Bring L.M}
    (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) (hfix : σ • y₀ = y₀) : σ = 1 := by
  have hkey : ∀ z ∈ (ramTrinomial m c).rootSet (Bring L.M), σ • z = z := by
    intro z hz
    have hsz : σ • z ∈ (ramTrinomial m c).rootSet (Bring L.M) := Polynomial.smul_mem_rootSet σ hz
    have h1 : rootRatio L v (m + 1) (σ • z) y₀ = rootRatio L v (m + 1) z y₀ := by
      have hinv := rootRatio_smul L hm hc hX hσ hz hy₀
      rwa [hfix] at hinv
    exact eq_of_rootRatio_eq L hm hc hX hsz hz hy₀ h1
  have hperm : MulAction.toPermHom L.deck ((ramTrinomial m c).rootSet (Bring L.M)) σ = 1 := by
    refine Equiv.ext fun z => ?_
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq]
    refine Subtype.ext ?_
    rw [Polynomial.rootSet.coe_smul]
    exact hkey z z.2
  exact toPermHom_injective L (ramTrinomial m c) (ramTrinomial_monic hm c)
    (hperm.trans (map_one _).symm)

/-- **Inertia at a place over the origin acts freely on the roots of the trinomial family.**  At a
geometric place inertia is the whole decomposition group, so this is the previous statement read for
inertia elements. -/
theorem eq_one_of_mem_geomInertia_of_fixes_root (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly (ramTrinomial m c))]
    (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP (0 : k))]
    {σ : L.deck} (hσ : σ ∈ geomInertia L.M Q) {y₀ : Bring L.M}
    (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) (hfix : σ • y₀ = y₀) : σ = 1 := by
  have hstab : σ • Q = Q := Ideal.inertia_le_stabilizer Q hσ
  refine eq_one_of_fixes_root L hm hc (v := coverPlace L 0 Q)
    (intOrd_baseX_pos L Q) ?_ hy₀ hfix
  simpa using hstab

/-! ### The character of the decomposition group -/

/-- **The relating root of unity turns the cocycle into a character.**  Comparing `στ y₀` with
`y₀` through `σ y₀` and using the invariance of the constant under `σ` multiplies the two
values. -/
theorem rootRatio_smul_mul (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L))
    {σ : L.deck} (hσ : σ • v.asIdeal = v.asIdeal) (τ : L.deck) {y₀ : Bring L.M}
    (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    rootRatio L v (m + 1) ((σ * τ) • y₀) y₀
      = rootRatio L v (m + 1) (σ • y₀) y₀ * rootRatio L v (m + 1) (τ • y₀) y₀ := by
  have hsy : σ • y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M) := Polynomial.smul_mem_rootSet σ hy₀
  have hty : τ • y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M) := Polynomial.smul_mem_rootSet τ hy₀
  have hsty : (σ * τ) • y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M) :=
    Polynomial.smul_mem_rootSet (σ * τ) hy₀
  rw [rootRatio_mul L hm hc hX hsty hsy hy₀, mul_smul σ τ y₀,
    rootRatio_smul L hm hc hX hσ hty hy₀]
  ring

set_option synthInstance.maxHeartbeats 400000 in
/-- The **decomposition group at a place** of a cover of the line: the deck transformations that
fix the place. -/
def placeStab (L : LineCover) (v : HeightOneSpectrum (Bring L.M)) : Subgroup L.deck :=
  MulAction.stabilizer L.deck v.asIdeal

set_option synthInstance.maxHeartbeats 400000 in
theorem mem_placeStab_iff (L : LineCover) {v : HeightOneSpectrum (Bring L.M)} {σ : L.deck} :
    σ ∈ placeStab L v ↔ σ • v.asIdeal = v.asIdeal := Iff.rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- At a geometric place the decomposition group is the inertia group. -/
theorem geomInertia_eq_placeStab (L : LineCover) (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] : geomInertia L.M Q = placeStab L (coverPlace L t Q) := by
  show geomInertia L.M Q = MulAction.stabilizer L.deck (coverPlace L t Q).asIdeal
  rw [coverPlace_asIdeal]
  exact geomInertia_eq_stabilizer t Q

/-- The character of the decomposition group at a place over the origin, recording how a deck
transformation moves a chosen root. -/
def inertiaChar (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L)) {y₀ : Bring L.M}
    (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    placeStab L v →* k where
  toFun σ := rootRatio L v (m + 1) ((σ : L.deck) • y₀) y₀
  map_one' := by
    rw [OneMemClass.coe_one, one_smul]
    exact rootRatio_self L (root_ne_zero L hy₀)
  map_mul' σ τ := by
    rw [Submonoid.coe_mul]
    exact rootRatio_smul_mul L hm hc hX ((mem_placeStab_iff L).mp σ.2) (τ : L.deck) hy₀

@[simp] theorem inertiaChar_apply (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L)) {y₀ : Bring L.M}
    (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) (σ : placeStab L v) :
    inertiaChar L hm hc hX hy₀ σ = rootRatio L v (m + 1) ((σ : L.deck) • y₀) y₀ := rfl

/-- **The character takes values in the `(m+1)`-st roots of unity.** -/
theorem inertiaChar_pow (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L)) {y₀ : Bring L.M}
    (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) (σ : placeStab L v) :
    inertiaChar L hm hc hX hy₀ σ ^ (m + 1) = 1 :=
  (rootRatio_spec L (exists_rootRatio L hm hc hX
    (Polynomial.smul_mem_rootSet (σ : L.deck) hy₀) hy₀)).1

/-- **The character of the decomposition group is injective.**  Its kernel consists of the deck
transformations fixing the chosen root, and those are trivial. -/
theorem inertiaChar_injective (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly (ramTrinomial m c))]
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L)) {y₀ : Bring L.M}
    (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    Function.Injective (inertiaChar L hm hc hX hy₀) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hsy : (σ : L.deck) • y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M) :=
    Polynomial.smul_mem_rootSet (σ : L.deck) hy₀
  have hval : rootRatio L v (m + 1) ((σ : L.deck) • y₀) y₀
      = rootRatio L v (m + 1) y₀ y₀ := by
    rw [rootRatio_self L (root_ne_zero L hy₀)]
    exact hσ
  have hfix : (σ : L.deck) • y₀ = y₀ := eq_of_rootRatio_eq L hm hc hX hsy hy₀ hy₀ hval
  exact Subtype.ext
    (eq_one_of_fixes_root L hm hc hX ((mem_placeStab_iff L).mp σ.2) hy₀ hfix)

/-- **The decomposition group at a place over the origin has order dividing `m + 1`.**  It embeds,
through the character, into the group of `(m+1)`-st roots of unity of the constant field. -/
theorem card_stabilizer_dvd (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly (ramTrinomial m c))]
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L)) {y₀ : Bring L.M}
    (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    Nat.card (placeStab L v) ∣ m + 1 := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  have hmem : ∀ σ, (inertiaChar L hm hc hX hy₀).toHomUnits σ ∈ rootsOfUnity (m + 1) k := by
    intro σ
    rw [mem_rootsOfUnity', MonoidHom.coe_toHomUnits]
    exact inertiaChar_pow L hm hc hX hy₀ σ
  have hinj : Function.Injective
      ((inertiaChar L hm hc hX hy₀).toHomUnits.codRestrict (rootsOfUnity (m + 1) k) hmem) := by
    intro a b hab
    refine inertiaChar_injective L hm hc hX hy₀ ?_
    have hcoe := congrArg (fun z : rootsOfUnity (m + 1) k => ((z : kˣ) : k)) hab
    simpa only [MonoidHom.codRestrict_apply, MonoidHom.coe_toHomUnits] using hcoe
  have hdvd := Subgroup.card_dvd_of_injective _ hinj
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_base (m + 1) (Nat.succ_pos m)
  have hcard : Nat.card (rootsOfUnity (m + 1) k) = m + 1 := by
    rw [Nat.card_eq_fintype_card]
    exact hω.card_rootsOfUnity
  rwa [hcard] at hdvd

/-- **Inertia at a place over the origin has order dividing `m + 1`.** -/
theorem card_geomInertia_dvd (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly (ramTrinomial m c))]
    (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP (0 : k))] {y₀ : Bring L.M}
    (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    Nat.card (geomInertia L.M Q) ∣ m + 1 := by
  have hstab := card_stabilizer_dvd L hm hc (v := coverPlace L 0 Q) (intOrd_baseX_pos L Q) hy₀
  rwa [← geomInertia_eq_placeStab L 0 Q] at hstab

end Rigidity.RET

end
