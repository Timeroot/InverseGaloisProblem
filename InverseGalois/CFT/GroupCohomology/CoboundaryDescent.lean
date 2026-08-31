/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.IndexTwo

/-!
# Descending a two-coboundary along a surjection of groups

Let `π : H → Q` be a surjection of groups, let `A` be a group on which `H` acts and `B` a group on
which `Q` acts, and let `B` sit inside `A` compatibly with `π`, as the elements fixed by the kernel
of `π`.  A two-cocycle of `Q` with values in `B` whose inflation to `H` is the coboundary of a
one-cochain with values in `A` is then already the coboundary of a one-cochain with values in `B`,
provided the first cohomology of the kernel with values in `A` vanishes.

The one-cochain upstairs is corrected by the coboundary of a single element of `A`, chosen so that
the corrected cochain is constant on the kernel.  A cochain constant on the kernel and trivialising
an inflated cocycle is constant on the cosets of the kernel and takes its values in the elements
fixed by the kernel, so it is the inflation of a cochain downstairs, which trivialises the cocycle
one started from.

For the Galois group of an extension of local fields and the multiplicative groups of the fields
this is the injectivity of the inflation map between relative Brauer groups: a class split by a
larger extension is already split by the smaller one.

## Main results

* `InverseGalois.CFT.coboundary₂_smulDiv`: the coboundary of the one-cochain attached to an element
  is trivial.
* `InverseGalois.CFT.exists_coboundary₂_eq_of_comap`: **an inflated two-cocycle which is a
  coboundary upstairs is a coboundary downstairs**, when the first cohomology of the kernel
  vanishes and the invariants of the kernel are the group downstairs.

## Tags

group cohomology, two-cocycle, coboundary, inflation, Hilbert 90, relative Brauer group
-/

open groupCohomology

namespace InverseGalois.CFT

/-! ### The coboundary attached to an element -/

section SmulDiv

variable {H A : Type*} [Group H] [CommGroup A] [MulDistribMulAction H A]

/-- **The one-cochain attached to an element has trivial coboundary.**  It is a one-cocycle, and
the coboundary of a one-cocycle is trivial. -/
theorem coboundary₂_smulDiv (α : A) : coboundary₂ (fun h : H => h • α / α) = 1 := by
  funext p
  obtain ⟨x, y⟩ := p
  simp only [coboundary₂_apply, smul_div', mul_smul, Pi.one_apply]
  refine Additive.ofMul.injective ?_
  simp only [ofMul_mul, ofMul_div, ofMul_one]
  abel

end SmulDiv

/-! ### Descending the trivialising cochain -/

section Descent

variable {H Q A B : Type*} [Group H] [Group Q] [CommGroup A] [CommGroup B]
  [MulDistribMulAction H A] [MulDistribMulAction Q B] {π : H →* Q} {j : B →* A}

/-- **An inflated two-cocycle which is a coboundary upstairs is a coboundary downstairs.**  The
trivialising cochain upstairs is corrected by the coboundary of a single element, supplied by the
vanishing of the first cohomology of the kernel, so as to be constant on the kernel; a cochain
constant on the kernel and trivialising an inflated cocycle is constant on the cosets of the kernel
and takes its values in the elements fixed by the kernel, hence descends. -/
theorem exists_coboundary₂_eq_of_comap
    (hπ : Function.Surjective π) (hj : Function.Injective j)
    (hjmap : ∀ (h : H) (b : B), h • j b = j (π h • b))
    (hjrange : ∀ a : A, (∀ n : ↥π.ker, (n : H) • a = a) → ∃ b : B, j b = a)
    (h90 : ∀ e : ↥π.ker → A, IsMulCocycle₁ e → IsMulCoboundary₁ e)
    {f : Q × Q → B} (hf : IsMulCocycle₂ f) {c : H → A}
    (hc : coboundary₂ c = fun p : H × H => j (f (π p.1, π p.2))) :
    ∃ d : Q → B, coboundary₂ d = f := by
  classical
  -- three elementary rearrangements in a commutative group
  have habs1 : ∀ X Y Z W : A, Y * Z = W * X → Y / W * (Z / W) = X / W := by
    intro X Y Z W h
    rw [div_mul_div_comm, h, mul_div_mul_left_eq_div]
  have habs2 : ∀ V X Y : A, V / X * Y = V → X = Y := by
    intro V X Y h
    rw [div_mul_eq_mul_div, div_eq_iff_eq_mul] at h
    exact (mul_left_cancel h).symm
  have habs3 : ∀ V X Y : A, V / X * Y = Y → V = X := by
    intro V X Y h
    exact div_eq_one.1 (mul_right_cancel (b := Y) (by rw [one_mul]; exact h))
  -- the value of the cocycle at the identity is fixed by the kernel
  have hker1 : ∀ n : ↥π.ker, π (n : H) = 1 := fun n => MonoidHom.mem_ker.1 n.2
  have hfixW : ∀ n : ↥π.ker, (n : H) • j (f (1, 1)) = j (f (1, 1)) := by
    intro n
    rw [hjmap, hker1 n, one_smul]
  -- the trivialising cochain restricted to the kernel is a one-cocycle up to that value
  have hcker : ∀ n m : ↥π.ker,
      (n : H) • c (m : H) * c (n : H) = j (f (1, 1)) * c ((n : H) * (m : H)) := by
    intro n m
    have h := congrFun hc ((n : H), (m : H))
    simp only [coboundary₂_apply, hker1 n, hker1 m] at h
    rw [div_mul_eq_mul_div, div_eq_iff_eq_mul] at h
    exact h
  have hecoc : IsMulCocycle₁ (fun n : ↥π.ker => c (n : H) / j (f (1, 1))) := by
    intro n m
    show c ((n * m : ↥π.ker) : H) / j (f (1, 1))
      = (n : H) • (c (m : H) / j (f (1, 1))) * (c (n : H) / j (f (1, 1)))
    rw [smul_div', hfixW n, Subgroup.coe_mul]
    exact (habs1 _ _ _ _ (hcker n m)).symm
  obtain ⟨α, hα⟩ := h90 _ hecoc
  have hαval : ∀ n : ↥π.ker, (n : H) • α / α = c (n : H) / j (f (1, 1)) := fun n => hα n
  -- the corrected cochain, with the same coboundary
  set c₁ : H → A := fun h => c h * (h • α / α)⁻¹ with hc₁def
  have hcb2 : coboundary₂ c₁ = fun p : H × H => j (f (π p.1, π p.2)) := by
    have hfun : c₁ = c * (fun h : H => h • α / α)⁻¹ := rfl
    rw [hfun, coboundary₂_mul, coboundary₂_inv, coboundary₂_smulDiv, inv_one, mul_one, hc]
  have hcbval : ∀ x y : H, coboundary₂ c₁ (x, y) = j (f (π x, π y)) :=
    fun x y => congrFun hcb2 (x, y)
  -- it is constant on the kernel
  have hc₁ker : ∀ n : ↥π.ker, c₁ (n : H) = j (f (1, 1)) := by
    intro n
    rw [hc₁def]
    show c (n : H) * ((n : H) • α / α)⁻¹ = j (f (1, 1))
    rw [hαval n, inv_div, mul_comm, div_mul_eq_mul_div, div_eq_iff_eq_mul, mul_comm]
  -- hence constant on the cosets of the kernel
  have hstep1 : ∀ (h : H) (n : ↥π.ker), c₁ (h * (n : H)) = c₁ h := by
    intro h n
    have hval := hcbval h (n : H)
    rw [coboundary₂_apply, hc₁ker n, hker1 n, map_one_snd_of_isMulCocycle₂ hf (π h),
      ← hjmap] at hval
    exact habs2 _ _ _ hval
  -- two elements with the same image have the same value
  have hcong : ∀ g h : H, π g = π h → c₁ g = c₁ h := by
    intro g h hgh
    have hmem : h⁻¹ * g ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
    have hs := hstep1 h ⟨h⁻¹ * g, hmem⟩
    have heq : h * (h⁻¹ * g) = g := by group
    rwa [heq] at hs
  -- and the values are fixed by the kernel
  have hstep2 : ∀ (n : ↥π.ker) (h : H), (n : H) • c₁ h = c₁ h := by
    intro n h
    have hval := hcbval (n : H) h
    rw [coboundary₂_apply, hc₁ker n, hker1 n, map_one_fst_of_isMulCocycle₂ hf (π h)] at hval
    have hnh : c₁ ((n : H) * h) = c₁ h := hcong _ _ (by rw [map_mul, hker1 n, one_mul])
    rw [habs3 _ _ _ hval, hnh]
  -- so the cochain descends
  choose d₀ hd₀ using fun h : H => hjrange (c₁ h) (fun n => hstep2 n h)
  have hjd : ∀ h : H, j (d₀ (Function.surjInv hπ (π h))) = c₁ h := by
    intro h
    rw [hd₀]
    exact hcong _ _ (Function.surjInv_eq hπ (π h))
  refine ⟨fun q => d₀ (Function.surjInv hπ q), ?_⟩
  funext p
  obtain ⟨x, y⟩ := p
  obtain ⟨h, rfl⟩ := hπ x
  obtain ⟨g, rfl⟩ := hπ y
  refine hj ?_
  have hgoal := hcbval h g
  rw [coboundary₂_apply] at hgoal
  simp only [coboundary₂_apply, map_mul, map_div]
  rw [← map_mul π, ← hjmap, hjd, hjd, hjd]
  exact hgoal

end Descent

end InverseGalois.CFT
