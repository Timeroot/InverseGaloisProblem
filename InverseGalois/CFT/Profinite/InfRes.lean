/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Comap

/-!
# Inflation and restriction for the cohomology of a topological group

A smooth cochain is by definition constant on the cosets of an open normal subgroup, and that
alone forces a good deal: a smooth one cocycle is trivial on the subgroup it is smooth for, and the
values of a smooth cocycle, in degree one or two, are fixed by that subgroup.  So a smooth cocycle
is a cocycle of the finite quotient, with coefficients in the invariants, and cohomology of an
infinite Galois group is assembled from the finite levels.

In degree one this gives the exact sequence of inflation and restriction, in the two halves that
are used.  Inflation is injective, because a one cochain of the quotient that becomes a coboundary
upstairs was already the coboundary of the same element; and a class whose restriction to the
kernel is trivial is inflated, because after correcting by that coboundary the cocycle is trivial
on the kernel, hence constant on its cosets, hence composed with the projection.

## Main results

* `InverseGalois.CFT.eq_one_of_isMulCocycle₁_of_smooth`: a smooth one cocycle is trivial on the
  subgroup it is smooth for.
* `InverseGalois.CFT.smul_eq_self_of_isMulCocycle₁_of_smooth`,
  `InverseGalois.CFT.smul_eq_self_of_isMulCocycle₂_of_smooth`: the values of a smooth cocycle are
  fixed by that subgroup.
* `InverseGalois.CFT.comapH1_injective`: **inflation is injective in the first cohomology.**
* `InverseGalois.CFT.exists_comapH1_eq`: **a class of the first cohomology whose restriction to the
  kernel is trivial is inflated from the quotient.**
* `InverseGalois.CFT.exists_comap₂_eq`, `InverseGalois.CFT.exists_comapH2_eq`: **a two cocycle
  constant on the cosets of the kernel is inflated from the quotient**, at the level of cochains
  and at the level of cohomology.

## Tags

profinite group, Galois cohomology, inflation, restriction, smooth cochain
-/

namespace InverseGalois.CFT

open groupCohomology

section Discrete

variable {Q M : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- The trivial subgroup of a discrete group is open and normal. -/
theorem isOpenNormal_bot : IsOpenNormal (⊥ : Subgroup Q) :=
  ⟨inferInstance, isOpen_discrete _⟩

/-- Every one cochain on a discrete group is smooth. -/
theorem isSmooth₁_of_discreteTopology (u : Q → M) : IsSmooth₁ u :=
  ⟨⊥, isOpenNormal_bot, fun x n hn => by rw [Subgroup.mem_bot.mp hn, mul_one]⟩

/-- Every two cochain on a discrete group is smooth. -/
theorem isSmooth₂_of_discreteTopology (a : Q × Q → M) : IsSmooth₂ a :=
  ⟨⊥, isOpenNormal_bot, fun x y n hn m hm => by
    rw [Subgroup.mem_bot.mp hn, Subgroup.mem_bot.mp hm, mul_one, mul_one]⟩

end Discrete

section Values

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] {N : Subgroup G}

/-- **A smooth one cocycle is trivial on the subgroup it is smooth for.** -/
theorem eq_one_of_isMulCocycle₁_of_smooth {u : G → M} (hu : IsMulCocycle₁ u)
    (hs : ∀ x : G, ∀ n ∈ N, u (x * n) = u x) {n : G} (hn : n ∈ N) : u n = 1 := by
  have h := hs 1 n hn
  rw [one_mul] at h
  rw [h, map_one_of_isMulCocycle₁ hu]

/-- **The values of a smooth one cocycle are fixed by the subgroup it is smooth for.** -/
theorem smul_eq_self_of_isMulCocycle₁_of_smooth {u : G → M} (hu : IsMulCocycle₁ u)
    (hnorm : N.Normal) (hs : ∀ x : G, ∀ n ∈ N, u (x * n) = u x) {n : G} (hn : n ∈ N) (g : G) :
    n • u g = u g := by
  have h0 : u n = 1 := eq_one_of_isMulCocycle₁_of_smooth hu hs hn
  have h1 : u (n * g) = n • u g * u n := hu n g
  have h3 : g⁻¹ * n * g ∈ N := by simpa using hnorm.conj_mem n hn g⁻¹
  have h2 : n * g = g * (g⁻¹ * n * g) := by group
  rw [h2, hs g _ h3, h0, mul_one] at h1
  exact h1.symm

/-- A two cocycle takes the same value at every pair whose first entry is trivial. -/
theorem apply_one_of_isMulCocycle₂ {a : G × G → M} (ha : IsMulCocycle₂ a) (y : G) :
    a (1, y) = a (1, 1) := by
  have h := ha 1 1 y
  rw [one_mul, one_mul, one_smul] at h
  exact (mul_left_cancel h).symm

/-- **The values of a smooth two cocycle are fixed by the subgroup it is smooth for.** -/
theorem smul_eq_self_of_isMulCocycle₂_of_smooth {a : G × G → M} (ha : IsMulCocycle₂ a)
    (hnorm : N.Normal) (hs : ∀ x y : G, ∀ n ∈ N, ∀ m ∈ N, a (x * n, y * m) = a (x, y))
    {n : G} (hn : n ∈ N) (x y : G) : n • a (x, y) = a (x, y) := by
  have h := ha n x y
  have e1 : a (n, x) = a (1, 1) := by
    have := hs 1 x n hn 1 N.one_mem
    rw [one_mul, mul_one] at this
    rw [this, apply_one_of_isMulCocycle₂ ha]
  have e2 : a (n, x * y) = a (1, 1) := by
    have := hs 1 (x * y) n hn 1 N.one_mem
    rw [one_mul, mul_one] at this
    rw [this, apply_one_of_isMulCocycle₂ ha]
  have e3 : a (n * x, y) = a (x, y) := by
    have hconj : x⁻¹ * n * x ∈ N := by simpa using hnorm.conj_mem n hn x⁻¹
    have hx : n * x = x * (x⁻¹ * n * x) := by group
    have := hs x y _ hconj 1 N.one_mem
    rw [mul_one] at this
    rw [hx, this]
  rw [e1, e2, e3] at h
  exact (mul_right_cancel h).symm

end Values

section Inflation

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
  [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction Q M]
variable {π : G →* Q} (hπ : ∀ (g : G) (m : M), g • m = π g • m)

include hπ

/-- **Inflation is injective in the first cohomology.** -/
theorem comapH1_injective (hsm : IsSmoothHom π) (hsurj : Function.Surjective π) :
    Function.Injective (comapH1 π hπ hsm) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨u, hu, hus, rfl⟩ := smoothH1Mk_surjective x
  rw [comapH1_smoothH1Mk π hπ hsm hu hus, smoothH1Mk_eq_one_iff] at hx
  obtain ⟨t, ht⟩ := hx
  rw [smoothH1Mk_eq_one_iff]
  refine ⟨t, funext fun q => ?_⟩
  obtain ⟨g, rfl⟩ := hsurj q
  have h := congrFun ht g
  rw [hπ g t] at h
  exact h

omit hπ

omit [TopologicalSpace G] [TopologicalSpace Q] [MulDistribMulAction Q M] in
/-- A one cocycle trivial on the kernel takes the same value at two elements with the same
image. -/
theorem eq_of_map_eq_of_eq_one_on_ker {v : G → M} (hv : IsMulCocycle₁ v)
    (h1 : ∀ n ∈ π.ker, v n = 1) {g g' : G} (hg : π g = π g') : v g = v g' := by
  have hmem : g⁻¹ * g' ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hg, inv_mul_cancel]
  have h := hv g (g⁻¹ * g')
  rw [mul_inv_cancel_left, h1 _ hmem, smul_one, one_mul] at h
  exact h.symm

include hπ

omit [TopologicalSpace G] [TopologicalSpace Q] in
/-- **A smooth one cocycle trivial on the kernel is composed with the projection.** -/
theorem exists_comap₁_eq_of_eq_one_on_ker (hsurj : Function.Surjective π) {v : G → M}
    (hv : IsMulCocycle₁ v) (h1 : ∀ n ∈ π.ker, v n = 1) :
    ∃ u : Q → M, IsMulCocycle₁ u ∧ comap₁ π u = v := by
  refine ⟨fun q => v (Function.surjInv hsurj q), fun q q' => ?_, funext fun g => ?_⟩
  · have hq : π (Function.surjInv hsurj q) = q := Function.surjInv_eq hsurj q
    have hq' : π (Function.surjInv hsurj q') = q' := Function.surjInv_eq hsurj q'
    have hmul : π (Function.surjInv hsurj q * Function.surjInv hsurj q') = q * q' := by
      rw [map_mul, hq, hq']
    have hval : v (Function.surjInv hsurj (q * q'))
        = v (Function.surjInv hsurj q * Function.surjInv hsurj q') :=
      eq_of_map_eq_of_eq_one_on_ker hv h1 (by rw [Function.surjInv_eq hsurj (q * q'), hmul])
    show v (Function.surjInv hsurj (q * q'))
        = q • v (Function.surjInv hsurj q') * v (Function.surjInv hsurj q)
    rw [hval, hv, hπ, hq]
  · exact eq_of_map_eq_of_eq_one_on_ker hv h1 (Function.surjInv_eq hsurj (π g))

variable [DiscreteTopology Q]

/-- **A class of the first cohomology whose restriction to the kernel is trivial is inflated from
the quotient.** -/
theorem exists_comapH1_eq (hsm : IsSmoothHom π) (hsurj : Function.Surjective π) {v : G → M}
    (hv : IsMulCocycle₁ v) (hvs : IsSmooth₁ v) [IsSmoothAction G M] (t : M)
    (ht : ∀ n ∈ π.ker, n • t / t = v n) :
    ∃ x : SmoothH1 Q M, comapH1 π hπ hsm x = smoothH1Mk v hv hvs := by
  set c : G → M := fun g => g • t / t with hc
  have hcc : IsMulCocycle₁ c := (smoothCoboundary₁_le_smoothCocycle₁ ⟨t, rfl⟩).1
  have hcs : IsSmooth₁ c := isSmooth₁_smul_div t
  set w : G → M := v * c⁻¹ with hw
  have hwc : IsMulCocycle₁ w :=
    ((smoothCocycle₁ G M).mul_mem ⟨hv, hvs⟩ ((smoothCocycle₁ G M).inv_mem ⟨hcc, hcs⟩)).1
  have hws : IsSmooth₁ w :=
    ((smoothCocycle₁ G M).mul_mem ⟨hv, hvs⟩ ((smoothCocycle₁ G M).inv_mem ⟨hcc, hcs⟩)).2
  have hwker : ∀ n ∈ π.ker, w n = 1 := by
    intro n hn
    rw [hw]
    simp only [Pi.mul_apply, Pi.inv_apply, hc, ht n hn, mul_inv_cancel]
  obtain ⟨u, hu, hcomap⟩ := exists_comap₁_eq_of_eq_one_on_ker hπ hsurj hwc hwker
  refine ⟨smoothH1Mk u hu (isSmooth₁_of_discreteTopology u), ?_⟩
  rw [comapH1_smoothH1Mk π hπ hsm hu (isSmooth₁_of_discreteTopology u)]
  have hsplit : (⟨v, hv, hvs⟩ : smoothCocycle₁ G M) = ⟨w, hwc, hws⟩ * ⟨c, hcc, hcs⟩ := by
    refine Subtype.ext (funext fun g => ?_)
    simp only [hw, Subgroup.coe_mul, Pi.mul_apply, Pi.inv_apply, inv_mul_cancel_right]
  have hcone : smoothH1Mk c hcc hcs = 1 := (smoothH1Mk_eq_one_iff hcc hcs).2 ⟨t, rfl⟩
  have : smoothH1Mk v hv hvs = smoothH1Mk w hwc hws * smoothH1Mk c hcc hcs := by
    rw [smoothH1Mk, smoothH1Mk, smoothH1Mk, hsplit, QuotientGroup.mk_mul]
  rw [this, hcone, mul_one]
  show QuotientGroup.mk _ = QuotientGroup.mk _
  exact congrArg _ (Subtype.ext hcomap)

end Inflation

section Level

variable {G Q : Type*} [Group G] [Group Q] {π : G →* Q}

/-- Two elements with the same image differ by an element of the kernel. -/
theorem exists_mem_ker_eq_mul {g g' : G} (h : π g = π g') : ∃ n ∈ π.ker, g' = g * n :=
  ⟨g⁻¹ * g', by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel], by group⟩

variable {M : Type*}

/-- A two cochain constant on the cosets of the kernel depends only on the images. -/
theorem eq_of_map_eq_of_smooth₂ {a : G × G → M}
    (hs : ∀ x y : G, ∀ n ∈ π.ker, ∀ m ∈ π.ker, a (x * n, y * m) = a (x, y))
    {x x' y y' : G} (hx : π x = π x') (hy : π y = π y') : a (x, y) = a (x', y') := by
  obtain ⟨n, hn, rfl⟩ := exists_mem_ker_eq_mul hx
  obtain ⟨m, hm, rfl⟩ := exists_mem_ker_eq_mul hy
  exact (hs x y n hn m hm).symm

variable [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction Q M]
  (hπ : ∀ (g : G) (m : M), g • m = π g • m)

include hπ

/-- **A two cocycle constant on the cosets of the kernel is composed with the projection.** -/
theorem exists_comap₂_eq (hsurj : Function.Surjective π) {a : G × G → M} (ha : IsMulCocycle₂ a)
    (hs : ∀ x y : G, ∀ n ∈ π.ker, ∀ m ∈ π.ker, a (x * n, y * m) = a (x, y)) :
    ∃ b : Q × Q → M, IsMulCocycle₂ b ∧ comap₂ π b = a := by
  set s := Function.surjInv hsurj with hsdef
  have hss : ∀ q : Q, π (s q) = q := Function.surjInv_eq hsurj
  refine ⟨fun p => a (s p.1, s p.2), fun q q' q'' => ?_, funext fun p => ?_⟩
  · show a (s (q * q'), s q'') * a (s q, s q') = q • a (s q', s q'') * a (s q, s (q' * q''))
    have h1 : a (s (q * q'), s q'') = a (s q * s q', s q'') :=
      eq_of_map_eq_of_smooth₂ hs (by rw [hss, map_mul, hss, hss]) rfl
    have h2 : a (s q, s (q' * q'')) = a (s q, s q' * s q'') :=
      eq_of_map_eq_of_smooth₂ hs rfl (by rw [hss, map_mul, hss, hss])
    rw [h1, h2, ha (s q) (s q') (s q''), hπ, hss]
  · show a (s (π p.1), s (π p.2)) = a p
    exact eq_of_map_eq_of_smooth₂ hs (hss (π p.1)) (hss (π p.2))

end Level

section LevelTwo

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q] [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction Q M]
variable {π : G →* Q} (hπ : ∀ (g : G) (m : M), g • m = π g • m)

include hπ

/-- **A class of the second cohomology represented by a cocycle constant on the cosets of the
kernel is inflated from the quotient.** -/
theorem exists_comapH2_eq (hsm : IsSmoothHom π) (hsurj : Function.Surjective π) {a : G × G → M}
    (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a)
    (hs : ∀ x y : G, ∀ n ∈ π.ker, ∀ m ∈ π.ker, a (x * n, y * m) = a (x, y)) :
    ∃ x : SmoothH2 Q M, comapH2 π hπ hsm x = smoothH2Mk a ha has := by
  obtain ⟨b, hb, hcomap⟩ := exists_comap₂_eq hπ hsurj ha hs
  refine ⟨smoothH2Mk b hb (isSmooth₂_of_discreteTopology b), ?_⟩
  rw [comapH2_smoothH2Mk π hπ hsm hb (isSmooth₂_of_discreteTopology b)]
  show QuotientGroup.mk _ = QuotientGroup.mk _
  exact congrArg _ (Subtype.ext hcomap)

end LevelTwo

end InverseGalois.CFT
