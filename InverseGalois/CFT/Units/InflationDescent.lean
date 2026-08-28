/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.SubgroupHilbert90

/-!
# Descending an inflated coboundary along a tower

Let `k ⊆ F ⊆ K` be a tower of finite Galois extensions and let `a` be a two-cocycle on the Galois
group of `F` over `k` with values in the units of `k`.  Composing with the restriction of
automorphisms inflates `a` to the Galois group of `K` over `k`, and this file descends the
conclusion of the Albert-Brauer-Hasse-Noether theorem for the inflated cocycle: if the inflation of
`a` is the coboundary of a one-cochain with values in the units of `K`, then `a` itself is the
coboundary of a one-cochain with values in the units of `F`.

The one-cochain trivialising the inflated cocycle is not usually constant on the kernel of the
restriction map, but the cocycle identity says that its restriction to that kernel is a one-cocycle
up to the constant value of the inflated cocycle at the identity, so Hilbert's theorem ninety for
the kernel makes it constant after multiplying by the coboundary of a single unit.  A one-cochain
constant on the kernel is invariant under the kernel on both sides, so it takes its values in the
units of `F` and factors through the restriction map, which is exactly a one-cochain trivialising
`a`.

## Main results

* `InverseGalois.CFT.smul_div_mul_twist`: multiplying a one-cochain by the coboundary of a single
  element does not change its coboundary.
* `InverseGalois.CFT.exists_isMulCoboundary_of_restrictNormalHom`: **a two-cocycle of the Galois
  group of a subextension whose inflation is a coboundary in the units of the larger field is a
  coboundary in the units of the subextension.**

## Tags

Galois descent, inflation, two-cocycle, coboundary, Hilbert ninety, tower
-/

namespace InverseGalois.CFT

/-! ### Twisting a one-cochain -/

section Twist

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- **Multiplying a one-cochain by the coboundary of a single element does not change its
coboundary.** -/
theorem smul_div_mul_twist (b : G → M) (t : M) (g h : G) :
    g • (b h * t / (h • t)) / (b (g * h) * t / ((g * h) • t)) * (b g * t / (g • t))
      = g • b h / b (g * h) * b g := by
  rw [smul_div', smul_mul', ← mul_smul]
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_div]
  abel

end Twist

/-! ### The descent -/

section Descent

variable {k F K : Type*} [Field k] [Field F] [Field K] [Algebra k F] [Algebra F K] [Algebra k K]
  [IsScalarTower k F K] [IsGalois k F] [IsGalois k K] [FiniteDimensional k K]

/-- **A two-cocycle of the Galois group of a subextension whose inflation is a coboundary in the
units of the larger field is a coboundary in the units of the subextension.**  Hilbert's theorem
ninety for the kernel of the restriction map replaces the trivialising one-cochain by one which is
constant on that kernel, and a one-cochain constant on the kernel is fixed by the kernel, hence has
its values in the subextension, and factors through the restriction map. -/
theorem exists_isMulCoboundary_of_restrictNormalHom {a : Gal(F/k) → Gal(F/k) → kˣ}
    (ha : ∀ x y z : Gal(F/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (hb : ∃ b : Gal(K/k) → Kˣ, ∀ g h : Gal(K/k),
      g • b h / b (g * h) * b g = Units.map (algebraMap k K : k →* K)
        (a (AlgEquiv.restrictNormalHom F g) (AlgEquiv.restrictNormalHom F h))) :
    ∃ b : Gal(F/k) → Fˣ, ∀ g h : Gal(F/k),
      g • b h / b (g * h) * b g = Units.map (algebraMap k F : k →* F) (a g h) := by
  classical
  obtain ⟨b, hb⟩ := hb
  haveI : IsGalois F K := IsGalois.tower_top_of_isGalois k F K
  haveI : FiniteDimensional F K := FiniteDimensional.right k F K
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom F : Gal(K/k) →* Gal(F/k)) :=
    AlgEquiv.restrictNormalHom_surjective K
  have hmapinj : Function.Injective (Units.map (algebraMap F K : F →* K)) :=
    Units.map_injective (algebraMap F K).injective
  -- The division-free form of the coboundary identity.
  have hb' : ∀ g h : Gal(K/k), g • b h * b g
      = Units.map (algebraMap k K : k →* K)
          (a (AlgEquiv.restrictNormalHom F g) (AlgEquiv.restrictNormalHom F h)) * b (g * h) := by
    intro g h
    have h1 := hb g h
    rw [div_mul_eq_mul_div, div_eq_iff_eq_mul] at h1
    exact h1
  have hbone : b 1 = Units.map (algebraMap k K : k →* K) (a 1 1) := by
    have h1 := hb' 1 1
    simp only [one_smul, map_one, mul_one] at h1
    exact mul_right_cancel h1
  have ha1 : ∀ x : Gal(F/k), a x 1 = a 1 1 := by
    intro x
    have h1 := ha x 1 1
    simp only [mul_one] at h1
    exact (mul_right_cancel h1).symm
  have ha2 : ∀ z : Gal(F/k), a 1 z = a 1 1 := by
    intro z
    have h1 := ha 1 1 z
    simp only [one_mul] at h1
    exact mul_left_cancel h1
  -- The kernel of the restriction map.
  set N := (AlgEquiv.restrictNormalHom F : Gal(K/k) →* Gal(F/k)).ker with hNdef
  have hmemN : ∀ x : Gal(K/k), x ∈ N ↔ AlgEquiv.restrictNormalHom F x = 1 := by
    intro x
    rw [hNdef]
    exact MonoidHom.mem_ker
  have hb1fix : ∀ g : Gal(K/k), g • b 1 = b 1 := by
    intro g
    rw [hbone]
    exact Units.ext (g.commutes _)
  -- On the kernel the one-cochain is a one-cocycle after dividing by its value at the identity.
  have hcoc : ∀ x ∈ N, ∀ y ∈ N, (fun g : Gal(K/k) => b g / b 1) (x * y)
      = x • (fun g : Gal(K/k) => b g / b 1) y * (fun g : Gal(K/k) => b g / b 1) x := by
    intro x hx y hy
    have h := hb' x y
    rw [(hmemN x).mp hx, (hmemN y).mp hy, ← hbone] at h
    show b (x * y) / b 1 = x • (b y / b 1) * (b x / b 1)
    rw [smul_div', hb1fix, div_mul_div_comm, h, mul_div_mul_left_eq_div]
  obtain ⟨t, ht⟩ :=
    exists_smul_div_eq_of_mem_subgroup (f := fun g : Gal(K/k) => b g / b 1) N hcoc
  obtain ⟨B, hBdef⟩ : ∃ B : Gal(K/k) → Kˣ, ∀ g, B g = b g * t / (g • t) := ⟨_, fun _ => rfl⟩
  have hB : ∀ g h : Gal(K/k), g • B h / B (g * h) * B g
      = Units.map (algebraMap k K : k →* K)
          (a (AlgEquiv.restrictNormalHom F g) (AlgEquiv.restrictNormalHom F h)) := by
    intro g h
    simp only [hBdef]
    rw [smul_div_mul_twist b t g h]
    exact hb g h
  -- The twisted one-cochain is constant on the kernel.
  have hBN : ∀ x ∈ N, B x = b 1 := by
    intro x hx
    have h : x • t / t = b x / b 1 := ht x hx
    have hxt : x • t = b x / b 1 * t := by rw [← h, div_mul_cancel]
    rw [hBdef, hxt, mul_div_mul_right_eq_div, div_div_cancel]
  -- Hence it is invariant under the kernel on the right, ...
  have hBleft : ∀ (g x : Gal(K/k)), x ∈ N → B (g * x) = B g := by
    intro g x hx
    have h := hB g x
    rw [(hmemN x).mp hx, ha1, ← hbone, hBN x hx, hb1fix, div_mul_eq_mul_div,
      div_eq_iff_eq_mul] at h
    exact (mul_left_cancel h).symm
  -- ... and therefore fixed by the kernel.
  have hBfix : ∀ (g x : Gal(K/k)), x ∈ N → x • B g = B g := by
    intro g x hx
    have hxk := (hmemN x).mp hx
    have hconj : g⁻¹ * x * g ∈ N := by
      rw [hmemN, map_mul, map_mul, map_inv, hxk, mul_one, inv_mul_cancel]
    have hxg : B (x * g) = B g := by
      have hrw : x * g = g * (g⁻¹ * x * g) := by group
      rw [hrw, hBleft g _ hconj]
    have h := hB x g
    rw [hxk, ha2, ← hbone, hBN x hx] at h
    have h1 : x • B g / B (x * g) = 1 :=
      mul_right_cancel (h.trans (one_mul (b 1)).symm)
    rw [div_eq_one] at h1
    rw [h1, hxg]
  -- A one-cochain fixed by the kernel takes its values in the units of the subextension.
  have hmemF : ∀ g : Gal(K/k), ∃ y : Fˣ, Units.map (algebraMap F K : F →* K) y = B g := by
    intro g
    have hfixF : ∀ τ : Gal(K/F), τ ((B g : K)) = (B g : K) := by
      intro τ
      have hker : τ.restrictScalars k ∈ N := by
        rw [hmemN]
        refine AlgEquiv.ext fun y => (algebraMap F K).injective ?_
        have hcom : algebraMap F K
              (AlgEquiv.restrictNormalHom F (AlgEquiv.restrictScalars k τ) y)
            = AlgEquiv.restrictScalars k τ (algebraMap F K y) :=
          AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars k τ) F y
        rw [hcom]
        exact τ.commutes y
      exact congrArg Units.val (hBfix g _ hker)
    obtain ⟨y₀, hy₀⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed (F := F) (E := K) (B g : K)).mpr hfixF
    have hy₀ne : y₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy₀
      exact (B g).ne_zero hy₀.symm
    exact ⟨Units.mk0 y₀ hy₀ne, Units.ext hy₀⟩
  -- It also factors through the restriction map.
  have hwd : ∀ g g' : Gal(K/k),
      AlgEquiv.restrictNormalHom F g = AlgEquiv.restrictNormalHom F g' → B g = B g' := by
    intro g g' hgg
    have hmem : g⁻¹ * g' ∈ N := by
      rw [hmemN, map_mul, map_inv, hgg, inv_mul_cancel]
    have hrw : g * (g⁻¹ * g') = g' := by group
    exact ((congrArg B hrw).symm.trans (hBleft g _ hmem)).symm
  set u : Gal(K/k) → Fˣ := fun g => Classical.choose (hmemF g) with hudef
  have hu : ∀ g, Units.map (algebraMap F K : F →* K) (u g) = B g := fun g =>
    Classical.choose_spec (hmemF g)
  set bF : Gal(F/k) → Fˣ := fun γ => u (Function.surjInv hsurj γ) with hbFdef
  have hbF : ∀ g : Gal(K/k), bF (AlgEquiv.restrictNormalHom F g) = u g := by
    intro g
    refine hmapinj ?_
    rw [hbFdef, hu, hu]
    exact hwd _ _ (Function.surjInv_eq hsurj _)
  -- Equivariance of the inclusion of the units.
  have hsmulmap : ∀ (g : Gal(K/k)) (y : Fˣ),
      Units.map (algebraMap F K : F →* K) (AlgEquiv.restrictNormalHom F g • y)
        = g • Units.map (algebraMap F K : F →* K) y := fun g y =>
    Units.ext (AlgEquiv.restrictNormal_commutes g F (y : F))
  refine ⟨bF, fun γ δ => ?_⟩
  obtain ⟨g, rfl⟩ := hsurj γ
  obtain ⟨h, rfl⟩ := hsurj δ
  refine hmapinj ?_
  rw [map_mul, map_div, hsmulmap, hbF, hbF, ← map_mul (AlgEquiv.restrictNormalHom F), hbF,
    hu, hu, hu, hB]
  exact Units.ext (IsScalarTower.algebraMap_apply k F K _)

end Descent

end InverseGalois.CFT
