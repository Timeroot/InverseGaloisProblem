/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.DihedralInertia
import InverseGalois.Rigidity.RET.MoveInfinity

/-!
# The dihedral cover in the inverted coordinate

The dihedral cover `T = u^n + u^{-n}` is branched over `T = ±2`, and the fibre over the point at
infinity consists of the two points `u = 0` and `u = ∞`, each with multiplicity `n`.  Reading the
cover in the coordinate `S = T⁻¹` turns that point into the origin, and the resulting cover of the
line is branched over the three points `S = 0` and `S = ±1/2` and is unramified at infinity.

This file sets up the inverted model and the elements of its integral model that see the local
structure at the origin.  Writing `P = u^{2n}`, the coordinate of the inverted cover is
`S = u^n/(P + 1)`; the function `V = P/(P + 1)` satisfies the quadratic equation
`V² - V + S² = 0`, so it is integral, and it generates the quadratic subfield fixed by the
rotations.  The two functions `z = u/(P + 1)` and `z' = u^{2n}/(u(P + 1))` satisfy

```
zⁿ = S·(1 - V)^{n-1},      z'ⁿ = S·V^{n-1}
```

which exhibit `S` as an `n`-th power up to a unit at each of the two points of the fibre.

## Main definitions

* `Rigidity.RET.dihInfCover` — the dihedral cover read in the inverted coordinate.
* `Rigidity.RET.infV`, `Rigidity.RET.infZ`, `Rigidity.RET.infZ'` — the three functions above.

## Main results

* `Rigidity.RET.infV_quadratic`, `Rigidity.RET.infZ_pow`, `Rigidity.RET.infZ'_pow` — the three
  identities.
* `Rigidity.RET.card_geomInertia_dihInf` — the inertia group at the origin has order `n`.
* `Rigidity.RET.isUnramifiedAtInfinity_dihInfCover` — the inverted cover is unramified at infinity.
* `Rigidity.RET.ncard_branchLocus_dihInfCover` — it is branched over exactly three points.
* `Rigidity.RET.isDeckGroupOver_dihedral` — the dihedral group occurs over three prescribed points
  of the line, and (`Rigidity.RET.not_isDeckGroupOver_dihedral`) over no fewer.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

/-! ### The inverted model -/

/-- **The dihedral cover read in the inverted coordinate** `S = T⁻¹`. -/
abbrev dihInfCover (n : ℕ) [NeZero n] : LineCover :=
  (dihLineCover n).twist invSubst.toRingEquiv

variable {n : ℕ} [NeZero n]

/-- The rational function of the parameter underlying an element of the inverted cover. -/
def infLine (x : (dihInfCover n).M) : RatFunc k :=
  LineSubst.toLine (dihSubst n) (show DihCover n from x)

/-- An element of the inverted cover, from a rational function of the parameter. -/
def ofInf (n : ℕ) [NeZero n] (x : RatFunc k) : (dihInfCover n).M :=
  show DihCover n from LineSubst.ofLine (dihSubst n) x

@[simp] theorem infLine_ofInf (x : RatFunc k) : infLine (ofInf n x) = x := rfl

theorem infLine_injective : Function.Injective (infLine (n := n)) := fun _ _ h => h

@[simp] theorem infLine_mul (x y : (dihInfCover n).M) :
    infLine (x * y) = infLine x * infLine y := rfl

@[simp] theorem infLine_add (x y : (dihInfCover n).M) :
    infLine (x + y) = infLine x + infLine y := rfl

@[simp] theorem infLine_sub (x y : (dihInfCover n).M) :
    infLine (x - y) = infLine x - infLine y := rfl

@[simp] theorem infLine_pow (x : (dihInfCover n).M) (m : ℕ) :
    infLine (x ^ m) = infLine x ^ m := rfl

@[simp] theorem infLine_one : infLine (1 : (dihInfCover n).M) = 1 := rfl

@[simp] theorem infLine_zero : infLine (0 : (dihInfCover n).M) = 0 := rfl

/-- Scalars of the inverted cover act through the inverted substitution. -/
@[simp] theorem infLine_algebraMap (f : RatFunc k) :
    infLine (algebraMap (RatFunc k) (dihInfCover n).M f) = dihSubst n (invSubst f) := rfl

/-- The integral model of the inverted cover acts through the inverted substitution. -/
@[simp] theorem infLine_algebraMapPoly (p : Polynomial k) :
    infLine (algebraMap (Polynomial k) (dihInfCover n).M p)
      = dihSubst n (invSubst (algebraMap (Polynomial k) (RatFunc k) p)) := rfl

/-! ### The coordinate as a function of the parameter -/

/-- The denominator `u^{2n} + 1` is not the zero function. -/
theorem dihDen_ne_zero (n : ℕ) [NeZero n] : ((RatFunc.X : RatFunc k) ^ (2 * n) + 1) ≠ 0 := by
  have hne : (Polynomial.X ^ (2 * n) + 1 : Polynomial k) ≠ 0 := by
    have hC : (1 : Polynomial k) = Polynomial.C 1 := (Polynomial.C_1).symm
    have hm : (Polynomial.X ^ (2 * n) + 1 : Polynomial k).Monic := by
      rw [hC]
      exact Polynomial.monic_X_pow_add_C 1 (by have := dihPos n; omega)
    exact hm.ne_zero
  have hmap : ((RatFunc.X : RatFunc k) ^ (2 * n) + 1)
      = algebraMap (Polynomial k) (RatFunc k) (Polynomial.X ^ (2 * n) + 1) := by
    rw [map_add, map_pow, map_one, RatFunc.algebraMap_X]
  rw [hmap]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mpr hne

/-- The dihedral invariant, written with a single denominator. -/
theorem dihedralInvariant_eq_div (n : ℕ) [NeZero n] :
    dihedralInvariant k n
      = ((RatFunc.X : RatFunc k) ^ (2 * n) + 1) / (RatFunc.X : RatFunc k) ^ n := by
  have hXn : ((RatFunc.X : RatFunc k) ^ n) ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  rw [dihedralInvariant, two_mul, pow_add]
  field_simp

/-- **The coordinate of the inverted cover** is the rational function `u^n/(u^{2n} + 1)` of the
parameter. -/
theorem infLine_baseX (n : ℕ) [NeZero n] :
    infLine (algebraMap (Polynomial k) (dihInfCover n).M Polynomial.X)
      = (RatFunc.X : RatFunc k) ^ n / ((RatFunc.X : RatFunc k) ^ (2 * n) + 1) := by
  rw [infLine_algebraMapPoly, RatFunc.algebraMap_X, invSubst_X, map_inv₀, dihSubst_X,
    dihedralInvariant_eq_div, inv_div]

/-! ### The three functions -/

/-- The coordinate of the inverted cover, as an element of its integral model. -/
def infS (n : ℕ) [NeZero n] : Bring (dihInfCover n).M :=
  algebraMap (Polynomial k) (Bring (dihInfCover n).M) Polynomial.X

@[simp] theorem coe_infS : ((infS n : Bring (dihInfCover n).M) : (dihInfCover n).M)
    = algebraMap (Polynomial k) (dihInfCover n).M Polynomial.X := rfl

/-- The generator `u^{2n}/(u^{2n} + 1)` of the quadratic subfield fixed by the rotations. -/
def infV (n : ℕ) [NeZero n] : (dihInfCover n).M :=
  ofInf n ((RatFunc.X : RatFunc k) ^ (2 * n) / ((RatFunc.X : RatFunc k) ^ (2 * n) + 1))

/-- **The quadratic equation of the rotation invariant.** -/
theorem infV_quadratic (n : ℕ) [NeZero n] :
    (infV n) ^ 2 - infV n
      + (algebraMap (Polynomial k) (dihInfCover n).M Polynomial.X) ^ 2 = 0 := by
  apply infLine_injective
  have hden := dihDen_ne_zero n
  have hX : ((RatFunc.X : RatFunc k)) ≠ 0 := RatFunc.X_ne_zero
  simp only [infLine_add, infLine_sub, infLine_pow, infLine_zero, infLine_baseX, infV,
    infLine_ofInf]
  rw [div_pow, div_pow, two_mul, pow_add]
  field_simp
  ring

/-- The rotation invariant is integral over the coordinate ring of the base. -/
theorem isIntegral_infV (n : ℕ) [NeZero n] : IsIntegral (Polynomial k) (infV n) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (Polynomial.X ^ 2), by monicity!, ?_⟩
  rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, map_pow]
  exact infV_quadratic n

/-- The rotation invariant, as an element of the integral model. -/
def infVB (n : ℕ) [NeZero n] : Bring (dihInfCover n).M := ⟨infV n, isIntegral_infV n⟩

@[simp] theorem coe_infVB : ((infVB n : Bring (dihInfCover n).M) : (dihInfCover n).M)
    = infV n := rfl

/-- **The quadratic equation of the rotation invariant**, in the integral model. -/
theorem infVB_quadratic (n : ℕ) [NeZero n] :
    (infVB n) ^ 2 - infVB n + (infS n) ^ 2 = 0 := by
  apply Subtype.ext
  push_cast [coe_infVB, coe_infS]
  exact infV_quadratic n

/-- The complement `1 - V` of the rotation invariant. -/
theorem infLine_one_sub_infV (n : ℕ) [NeZero n] :
    infLine (1 - infV n) = ((RatFunc.X : RatFunc k) ^ (2 * n) + 1)⁻¹ := by
  have hden := dihDen_ne_zero n
  simp only [infLine_sub, infLine_one, infV, infLine_ofInf]
  field_simp
  ring

/-- The function `u/(u^{2n} + 1)`, an `n`-th root of the coordinate up to a unit at the point
`u = 0` of the fibre over the origin. -/
def infZ (n : ℕ) [NeZero n] : (dihInfCover n).M :=
  ofInf n ((RatFunc.X : RatFunc k) / ((RatFunc.X : RatFunc k) ^ (2 * n) + 1))

/-- The function `u^{2n}/(u(u^{2n} + 1))`, an `n`-th root of the coordinate up to a unit at the
point `u = ∞` of the fibre over the origin. -/
def infZ' (n : ℕ) [NeZero n] : (dihInfCover n).M :=
  ofInf n ((RatFunc.X : RatFunc k) ^ (2 * n)
    / ((RatFunc.X : RatFunc k) * ((RatFunc.X : RatFunc k) ^ (2 * n) + 1)))

/-- **The coordinate is an `n`-th power up to a unit at the first point of the fibre.** -/
theorem infZ_pow (n : ℕ) [NeZero n] :
    (infZ n) ^ n
      = (algebraMap (Polynomial k) (dihInfCover n).M Polynomial.X) * (1 - infV n) ^ (n - 1) := by
  apply infLine_injective
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (dihPos n)).symm⟩
  have hden := dihDen_ne_zero (m + 1)
  have hX : ((RatFunc.X : RatFunc k)) ≠ 0 := RatFunc.X_ne_zero
  simp only [infLine_mul, infLine_pow, infLine_baseX, infZ, infLine_ofInf,
    infLine_one_sub_infV, Nat.add_sub_cancel, div_pow, inv_pow]
  field_simp
  ring

/-- **The coordinate is an `n`-th power up to a unit at the second point of the fibre.** -/
theorem infZ'_pow (n : ℕ) [NeZero n] :
    (infZ' n) ^ n
      = (algebraMap (Polynomial k) (dihInfCover n).M Polynomial.X) * (infV n) ^ (n - 1) := by
  apply infLine_injective
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (dihPos n)).symm⟩
  have hden := dihDen_ne_zero (m + 1)
  have hX : ((RatFunc.X : RatFunc k)) ≠ 0 := RatFunc.X_ne_zero
  simp only [infLine_mul, infLine_pow, infLine_baseX, infZ', infLine_ofInf, infV,
    Nat.add_sub_cancel, div_pow, mul_pow]
  field_simp
  ring

/-! ### The integral model at the origin -/

section Inertia

/-- The complement of the rotation invariant, in the integral model. -/
def infEB (n : ℕ) [NeZero n] : Bring (dihInfCover n).M := 1 - infVB n

@[simp] theorem coe_infEB : ((infEB n : Bring (dihInfCover n).M) : (dihInfCover n).M)
    = 1 - infV n := rfl

theorem infVB_add_infEB (n : ℕ) [NeZero n] : infVB n + infEB n = 1 := by
  rw [infEB]; ring

theorem isIntegral_infZ (n : ℕ) [NeZero n] : IsIntegral (Polynomial k) (infZ n) := by
  refine IsIntegral.of_pow (NeZero.pos n) ?_
  rw [infZ_pow]
  exact isIntegral_algebraMap.mul ((isIntegral_one.sub (isIntegral_infV n)).pow _)

theorem isIntegral_infZ' (n : ℕ) [NeZero n] : IsIntegral (Polynomial k) (infZ' n) := by
  refine IsIntegral.of_pow (NeZero.pos n) ?_
  rw [infZ'_pow]
  exact isIntegral_algebraMap.mul ((isIntegral_infV n).pow _)

/-- The `n`-th root of the coordinate at the first point of the fibre, in the integral model. -/
def infZB (n : ℕ) [NeZero n] : Bring (dihInfCover n).M := ⟨infZ n, isIntegral_infZ n⟩

/-- The `n`-th root of the coordinate at the second point of the fibre, in the integral model. -/
def infZ'B (n : ℕ) [NeZero n] : Bring (dihInfCover n).M := ⟨infZ' n, isIntegral_infZ' n⟩

@[simp] theorem coe_infZB : ((infZB n : Bring (dihInfCover n).M) : (dihInfCover n).M)
    = infZ n := rfl

@[simp] theorem coe_infZ'B : ((infZ'B n : Bring (dihInfCover n).M) : (dihInfCover n).M)
    = infZ' n := rfl

theorem infZB_pow (n : ℕ) [NeZero n] : (infZB n) ^ n = infS n * (infEB n) ^ (n - 1) := by
  apply Subtype.ext
  push_cast [coe_infZB, coe_infS, coe_infEB]
  exact infZ_pow n

theorem infZ'B_pow (n : ℕ) [NeZero n] : (infZ'B n) ^ n = infS n * (infVB n) ^ (n - 1) := by
  apply Subtype.ext
  push_cast [coe_infZ'B, coe_infS, coe_infVB]
  exact infZ'_pow n

/-! ### The inertia group at the origin -/

/-- The generator of a place of the base, read in the integral model of the inverted cover, lies
in every place of the cover above it. -/
theorem gen_mem_of_liesOver (n : ℕ) [NeZero n] (c : k) (Q : Ideal (Bring (dihInfCover n).M))
    [Q.LiesOver (placeP c)] :
    algebraMap (Polynomial k) (Bring (dihInfCover n).M) (X - C c) ∈ Q := by
  have hover : placeP c = Q.comap (algebraMap (Polynomial k) (Bring (dihInfCover n).M)) :=
    Ideal.LiesOver.over
  have hmem : (X - C c) ∈ placeP c := Ideal.mem_span_singleton_self _
  rw [hover, Ideal.mem_comap] at hmem
  exact hmem

/-- **A root of the place generator, up to a factor invertible at a place of the cover, forces that
place to ramify to the order of the root.** -/
theorem dihInf_pow_dvd_gen (n : ℕ) [NeZero n] (c : k) (Q : Ideal (Bring (dihInfCover n).M))
    [hQm : Q.IsMaximal] [Q.LiesOver (placeP c)] {m : ℕ} {y u : Bring (dihInfCover n).M}
    (hy : y ^ m = algebraMap (Polynomial k) (Bring (dihInfCover n).M) (X - C c) * u) (hu : u ∉ Q) :
    Q ^ m ∣ Ideal.map (algebraMap (Polynomial k) (Bring (dihInfCover n).M)) (placeP c) := by
  haveI hQp : Q.IsPrime := hQm.isPrime
  have hprime : Prime Q := Ideal.prime_of_isPrime (Q_ne_bot _ c Q) hQp
  set g := algebraMap (Polynomial k) (Bring (dihInfCover n).M) (X - C c) with hg
  -- the extended place is generated by the image of the generator
  have hmap : Ideal.map (algebraMap (Polynomial k) (Bring (dihInfCover n).M)) (placeP c)
      = Ideal.span {g} := by
    rw [placeP, Ideal.map_span, Set.image_singleton]
  have hgQ : g ∈ Q := gen_mem_of_liesOver n c Q
  -- the root lies in the place, so its `m`-th power lies in the `m`-th power of the place
  have hyQ : y ∈ Q := hQp.mem_of_pow_mem m (by rw [hy]; exact Ideal.mul_mem_right _ _ hgQ)
  have hdvd : Q ^ m ∣ Ideal.span {g} * Ideal.span {u} := by
    have h1 : Q ∣ Ideal.span {y} :=
      Ideal.dvd_iff_le.mpr (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hyQ)
    have h2 : Q ^ m ∣ Ideal.span {y} ^ m := pow_dvd_pow_of_dvd h1 m
    rwa [Ideal.span_singleton_pow, hy, ← Ideal.span_singleton_mul_span_singleton] at h2
  have hnot : ¬ Q ∣ Ideal.span {u} := by
    intro hc
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff] at hc
    exact hu hc
  rw [hmap]
  exact hprime.pow_dvd_of_dvd_mul_right m hnot hdvd

/-- **An `n`-th root of the coordinate, unit away from one point of the fibre, forces the place at
the origin to ramify to order `n`.** -/
theorem dihInf_pow_dvd_of_root (n : ℕ) [NeZero n] (Q : Ideal (Bring (dihInfCover n).M))
    [hQm : Q.IsMaximal] [Q.LiesOver (placeP (0 : k))]
    {y w : Bring (dihInfCover n).M} (hy : y ^ n = infS n * w ^ (n - 1)) (hw : w ∉ Q) :
    Q ^ n ∣ Ideal.map (algebraMap (Polynomial k) (Bring (dihInfCover n).M)) (placeP 0) := by
  haveI hQp : Q.IsPrime := hQm.isPrime
  refine dihInf_pow_dvd_gen n 0 Q (y := y) (u := w ^ (n - 1)) ?_ ?_
  · rw [C_0, sub_zero, hy]
    rfl
  · exact fun hc => hw (hQp.mem_of_pow_mem (n - 1) hc)

/-- **The place at the origin of the inverted dihedral cover ramifies to order at least `n`.** -/
theorem dihInf_pow_dvd (n : ℕ) [NeZero n] (Q : Ideal (Bring (dihInfCover n).M))
    [hQm : Q.IsMaximal] [Q.LiesOver (placeP (0 : k))] :
    Q ^ n ∣ Ideal.map (algebraMap (Polynomial k) (Bring (dihInfCover n).M)) (placeP 0) := by
  haveI hQp : Q.IsPrime := hQm.isPrime
  by_cases hE : infEB n ∈ Q
  · refine dihInf_pow_dvd_of_root n Q (infZ'B_pow n) (fun hV => ?_)
    have h1 : (1 : Bring (dihInfCover n).M) ∈ Q := by
      have := Ideal.add_mem Q hV hE
      rwa [infVB_add_infEB] at this
    exact hQp.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · exact dihInf_pow_dvd_of_root n Q (infZB_pow n) hE

/-! ### The deck group of the inverted cover -/

variable {ζ : k}

/-- **The deck group of the inverted dihedral cover is the dihedral group.** -/
def dihInfDeckEquiv (hζ : IsPrimitiveRoot ζ n) : DihedralGroup n ≃* (dihInfCover n).deck :=
  (dihDeckEquiv hζ).trans (Twist.autEquiv (φ := invSubst.toRingEquiv) (M := DihCover n))

/-- Every element of a dihedral group is a rotation, of order dividing `n`, or a reflection, of
order two. -/
theorem orderOf_dvd_or_eq_two {G : Type*} [Group G] (e : DihedralGroup n ≃* G) (g : G) :
    orderOf g ∣ n ∨ orderOf g = 2 := by
  have hord : orderOf (e.symm g) = orderOf g := e.symm.orderOf_eq g
  cases hx : e.symm g with
  | r i =>
    refine Or.inl ?_
    rw [← hord, hx, DihedralGroup.orderOf_r]
    exact ⟨Nat.gcd n i.val, (Nat.div_mul_cancel (Nat.gcd_dvd_left n i.val)).symm⟩
  | sr j =>
    refine Or.inr ?_
    rw [← hord, hx, DihedralGroup.orderOf_sr]

/-- **A cyclic subgroup of a dihedral group with more than two elements consists of rotations**, so
its order divides `n`. -/
theorem card_dvd_of_isCyclic_subgroup {G : Type*} [Group G] (e : DihedralGroup n ≃* G)
    (H : Subgroup G) [IsCyclic H] (h3 : 3 ≤ Nat.card H) : Nat.card H ∣ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have htop : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' _).mpr hg
  have hcoe : orderOf ((g : G)) = orderOf g :=
    orderOf_injective H.subtype Subtype.val_injective g
  have hc : orderOf ((g : G)) = Nat.card H := by
    rw [hcoe, ← Nat.card_zpowers, htop, Subgroup.card_top]
  rcases orderOf_dvd_or_eq_two e (g : G) with h | h
  · rwa [hc] at h
  · omega

/-- **A dihedral group of order at least six is not cyclic.** -/
theorem not_isCyclic_of_dihedral {G : Type*} [Group G] (e : DihedralGroup n ≃* G) (hn : 3 ≤ n) :
    ¬ IsCyclic G := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hcard : Nat.card G = 2 * n := by
    rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hord : orderOf g = 2 * n := by
    rw [← hcard, ← Nat.card_zpowers, ((Subgroup.eq_top_iff' _).mpr hg : Subgroup.zpowers g = ⊤),
      Subgroup.card_top]
  rcases orderOf_dvd_or_eq_two e g with h | h
  · rw [hord] at h
    have hle := Nat.le_of_dvd (by omega) h
    omega
  · omega

/-- **The inertia group at the origin of the inverted dihedral cover has order exactly `n`**: it is
the group of rotations. -/
theorem card_geomInertia_dihInf (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (Q : Ideal (Bring (dihInfCover n).M)) [Q.IsMaximal] [Q.LiesOver (placeP (0 : k))] :
    Nat.card (geomInertia (dihInfCover n).M Q) = n := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_algebraicClosure n (dihPos n)
  haveI := GeomAKLB.isCyclic_geomInertia (Ω := (dihInfCover n).M) 0 Q
  have hlow := le_card_geomInertia_of_pow_dvd (0 : k) Q (dihInf_pow_dvd n Q)
  have hdvd := card_dvd_of_isCyclic_subgroup (dihInfDeckEquiv hζ)
    (geomInertia (dihInfCover n).M Q) (le_trans hn hlow)
  exact le_antisymm (Nat.le_of_dvd (by omega) hdvd) hlow

/-- **A rotation generates the inertia group at the origin of the inverted dihedral cover.** -/
theorem isInertiaGenAt_zero_dihInfCover (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    ∃ σ : (dihInfCover n).deck, orderOf σ = n ∧ (dihInfCover n).IsInertiaGenAt 0 σ := by
  obtain ⟨Q, hQmax, hQover⟩ := exists_Q_over_placeP (dihInfCover n).M (0 : k)
  haveI := hQmax
  haveI := hQover
  haveI := GeomAKLB.isCyclic_geomInertia (Ω := (dihInfCover n).M) 0 Q
  have hcard := card_geomInertia_dihInf n hn Q
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := geomInertia (dihInfCover n).M Q)
  have htop : Subgroup.zpowers σ₀ = ⊤ := (Subgroup.eq_top_iff' _).mpr hσ₀
  have hord : orderOf ((σ₀ : (dihInfCover n).deck)) = n := by
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers, htop, Subgroup.card_top, hcard]
  refine ⟨(σ₀ : (dihInfCover n).deck), hord, Q, hQmax, hQover, ?_⟩
  refine (Subgroup.eq_of_le_of_card_le' (H := Subgroup.zpowers (σ₀ : (dihInfCover n).deck))
    (Subgroup.zpowers_le.mpr σ₀.2) ?_).symm
  rw [hcard, Nat.card_zpowers, hord]

/-! ### The three branch points -/

/-- The dihedral cover is unramified at the origin. -/
theorem isUnramifiedOutside_compl_zero (n : ℕ) [NeZero n] :
    (dihLineCover n).IsUnramifiedOutside (({0} : Set k)ᶜ) := by
  refine ((dihLineCover n).isUnramifiedOutside_iff_branchLocus_subset _).mpr ?_
  rw [branchLocus_dihLineCover]
  rintro t (rfl | rfl) <;>
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] <;> norm_num

/-- **The inverted dihedral cover is unramified at infinity.** -/
theorem isUnramifiedAtInfinity_dihInfCover (n : ℕ) [NeZero n] :
    (dihInfCover n).IsUnramifiedAtInfinity :=
  LineCover.isUnramifiedAtInfinity_twist_inv (dihLineCover n) (isUnramifiedOutside_compl_zero n)

/-- **The inverted dihedral cover is branched over at most the three points `0`, `1/2` and
`-1/2`.** -/
theorem branchLocus_dihInfCover_subset (n : ℕ) [NeZero n] :
    (dihInfCover n).branchLocus ⊆ ({0, 2⁻¹, -2⁻¹} : Set k) := by
  have h₁ : (dihLineCover n).IsUnramifiedOutside ({2, -2} : Set k) :=
    ((dihLineCover n).isUnramifiedOutside_iff_branchLocus_subset _).mpr
      (le_of_eq (branchLocus_dihLineCover n))
  have h₂ := LineCover.isUnramifiedOutside_twist_inv_ne_zero (dihLineCover n) h₁
  refine subset_trans (((dihInfCover n).isUnramifiedOutside_iff_branchLocus_subset _).mp h₂) ?_
  rintro t ht
  rcases ht with h0 | ⟨-, hti⟩
  · exact Or.inl h0
  · rcases hti with h | h
    · exact Or.inr (Or.inl (inv_eq_iff_eq_inv.mp h))
    · refine Or.inr (Or.inr ?_)
      rw [inv_eq_iff_eq_inv.mp h, inv_neg]
      rfl

/-- **The inverted dihedral cover is branched over exactly three points**, and is unramified at
infinity: a non-abelian cover of the line with three branch points. -/
theorem ncard_branchLocus_dihInfCover (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    (dihInfCover n).branchLocus.ncard = 3 := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_algebraicClosure n (dihPos n)
  have hconv : (dihInfCover n).branchLocus.ncard
      = ((dihInfCover n).finite_branchLocus).toFinset.card :=
    Set.ncard_eq_toFinset_card _ _
  have hfin : ({0, 2⁻¹, -2⁻¹} : Set k).Finite :=
    ((Set.finite_singleton _).insert _).insert _
  have hle : (dihInfCover n).branchLocus.ncard ≤ 3 := by
    refine le_trans (Set.ncard_le_ncard (branchLocus_dihInfCover_subset n) hfin) ?_
    calc ({0, 2⁻¹, -2⁻¹} : Set k).ncard ≤ ({(2 : k)⁻¹, -2⁻¹} : Set k).ncard + 1 :=
          Set.ncard_insert_le _ _
      _ ≤ (({-(2 : k)⁻¹} : Set k).ncard + 1) + 1 :=
          Nat.add_le_add_right (Set.ncard_insert_le _ _) 1
      _ = 3 := by rw [Set.ncard_singleton]
  have hge : 3 ≤ (dihInfCover n).branchLocus.ncard := by
    by_contra hlt
    exact not_isCyclic_of_dihedral (dihInfDeckEquiv hζ) hn
      ((dihInfCover n).isCyclic_deck_of_branchLocus_card_le_two (by omega)
        (isUnramifiedAtInfinity_dihInfCover n))
  omega

/-! ### The dihedral group as a deck group -/

/-- **The dihedral group is the deck group of a cover of the line branched over the three
prescribed points `0`, `1/2` and `-1/2`**, unramified at infinity: the first non-abelian group
exhibited over a prescribed branch locus. -/
theorem isDeckGroupOver_dihedral (n : ℕ) [NeZero n] :
    IsDeckGroupOver ({0, 2⁻¹, -2⁻¹} : Set k) (DihedralGroup n) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_algebraicClosure n (dihPos n)
  exact ⟨dihInfCover n, ⟨(dihInfDeckEquiv hζ).symm⟩,
    ((dihInfCover n).isUnramifiedOutside_iff_branchLocus_subset _).mpr
      (branchLocus_dihInfCover_subset n), isUnramifiedAtInfinity_dihInfCover n⟩

/-- **Two points do not suffice.**  A dihedral group of order at least six is the deck group of no
cover of the line branched over two points and unramified at infinity, so three is the exact number
of points needed. -/
theorem not_isDeckGroupOver_dihedral (n : ℕ) [NeZero n] (hn : 3 ≤ n) {S : Set k} (hS : S.Finite)
    (hcard : hS.toFinset.card ≤ 2) : ¬ IsDeckGroupOver S (DihedralGroup n) := fun h =>
  not_isCyclic_of_dihedral (MulEquiv.refl (DihedralGroup n)) hn
    (isCyclic_of_isDeckGroupOver hS hcard h)

/-- **The dihedral group occurs with two branch points on the affine line**, on the standard model
`T = u^n + u^{-n}`, which pays for the third point by ramifying at infinity. -/
theorem isAffineDeckGroup_two_dihedral (n : ℕ) [NeZero n] :
    IsAffineDeckGroup 2 (DihedralGroup n) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_algebraicClosure n (dihPos n)
  exact ⟨dihLineCover n, ⟨(dihDeckEquiv hζ).symm⟩, le_of_eq (ncard_branchLocus_dihLineCover n)⟩

/-- **One affine branch point does not suffice**, so two is the exact affine count of a dihedral
group of order at least six. -/
theorem not_isAffineDeckGroup_one_dihedral (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    ¬ IsAffineDeckGroup 1 (DihedralGroup n) := by
  rintro ⟨L, ⟨e⟩, hle⟩
  haveI := isCyclic_deck_of_ncard_branchLocus_le_one L hle
  exact not_isCyclic_of_dihedral (MulEquiv.refl (DihedralGroup n)) hn
    (isCyclic_of_surjective (e : L.deck →* DihedralGroup n) e.surjective)

end Inertia

end Rigidity.RET
