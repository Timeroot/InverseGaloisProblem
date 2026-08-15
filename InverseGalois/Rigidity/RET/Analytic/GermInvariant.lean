/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Analytic.GermScale

/-!
# Germs invariant under a rotation of the coordinate

A rotation `u ↦ a * u` of the coordinate acts on the meromorphic germs at the origin.  A germ it
fixes has a very restricted order of vanishing: writing the germ as `u ^ n` times an analytic
function nonvanishing at the origin and comparing the two sides at the origin gives `a ^ n = 1`.
So a rotation of order `m` can only fix germs whose order of vanishing is a multiple of `m`.

That is the quantitative content behind the comparison of an analytic branch with the algebra it
comes from.  A branch read in the coordinate `u` is also a branch read in `u ^ 2`, and nothing in
the construction of the branch says which coordinate is the right one; the rotations that fix the
branch measure exactly that ambiguity, and this file converts the measurement into a bound on the
order of vanishing of every element of the place the branch cuts out.

The second half of the file is the bookkeeping that turns such a bound into a bound on the powers
of the place: the elements whose germ vanishes to order at least `n` form an ideal, these ideals
multiply as expected, and the `n`-th power of a place all of whose elements vanish to order at
least `m` consists of elements vanishing to order at least `n * m`.

## Main definitions

* `Rigidity.RET.Analytic.ordIdeal` — the elements whose germ vanishes to a given order.

## Main results

* `Rigidity.RET.Analytic.zpow_eq_one_of_scaleGerm_eq_self` — a rotation fixing a germ of order `n`
  satisfies `a ^ n = 1`.
* `Rigidity.RET.Analytic.le_ord_of_scaleGerm_eq_self` — a rotation of order `m` fixing a germ that
  vanishes forces it to vanish to order at least `m`.
* `Rigidity.RET.Analytic.le_ord_of_mem_germPlace_pow_of_le` — the refined order bound on the powers
  of the germ place.
-/

open Filter Topology Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

open MeroGerm

theorem germ_eq_iff {x : ℂ} {f g : ℂ → ℂ} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    of hf = of hg ↔ ∀ᶠ z in 𝓝[≠] x, f z = g z := by
  refine ⟨fun h => ?_, of_congr hf hg⟩
  have hval : (f : PunctGerm x) = (g : PunctGerm x) := congrArg Subtype.val h
  exact Filter.Germ.coe_eq.1 hval

/-- **A rotation fixing a germ fixes its leading coefficient**: if `u ↦ a * u` leaves a
meromorphic germ of order `n` unchanged, then `a ^ n = 1`. -/
theorem zpow_eq_one_of_scaleGerm_eq_self {a : ℂ} (ha : a ≠ 0) {f : MeroGerm (0 : ℂ)} {n : ℤ}
    (hn : ord f = (n : WithTop ℤ)) (h : scaleGerm ha f = f) : a ^ n = 1 := by
  obtain ⟨F, hF, rfl⟩ := exists_of f
  rw [ord_of] at hn
  obtain ⟨g, hg, hg0, hFg⟩ := (meromorphicOrderAt_eq_int_iff hF).1 hn
  rw [scaleGerm_of] at h
  have hEq : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (F ∘ scaleFun a) u = F u := (germ_eq_iff _ _).1 h
  have hFg2 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z = z ^ n * g z := by
    filter_upwards [hFg] with z hz
    simpa [smul_eq_mul] using hz
  have hFg3 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), F (a * u) = (a * u) ^ n * g (a * u) :=
    (tendsto_scaleFun ha).eventually hFg2
  have key : ∀ᶠ u in 𝓝[≠] (0 : ℂ), a ^ n * g (a * u) = g u := by
    filter_upwards [hEq, hFg2, hFg3, self_mem_nhdsWithin] with u h1 h2 h3 hu
    have hu0 : u ≠ 0 := by simpa using hu
    have h5 : (a * u) ^ n * g (a * u) = u ^ n * g u := by rw [← h3, ← h2]; exact h1
    rw [mul_zpow] at h5
    refine mul_left_cancel₀ (zpow_ne_zero n hu0) ?_
    rw [← h5]; ring
  have hcont : ContinuousAt (fun u : ℂ => a ^ n * g (a * u)) 0 := by
    refine continuousAt_const.mul (ContinuousAt.comp ?_ (by fun_prop))
    simpa using hg.continuousAt
  have hlim1 : Tendsto (fun u : ℂ => a ^ n * g (a * u)) (𝓝[≠] (0 : ℂ)) (𝓝 (a ^ n * g 0)) := by
    have hT : Tendsto (fun u : ℂ => a ^ n * g (a * u)) (𝓝 (0 : ℂ)) (𝓝 (a ^ n * g (a * 0))) :=
      hcont.tendsto
    rw [mul_zero] at hT
    exact hT.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) :=
    hg.continuousAt.continuousWithinAt (s := {(0 : ℂ)}ᶜ)
  have heq := tendsto_nhds_unique (hlim1.congr' key) hlim2
  exact mul_right_cancel₀ hg0 (by rw [heq, one_mul] : a ^ n * g 0 = 1 * g 0)

/-- **A rotation of finite order fixing a germ forces its order of vanishing to be a multiple of
the order of the rotation.** -/
theorem le_ord_of_scaleGerm_eq_self {a : ℂ} (ha : a ≠ 0) {f : MeroGerm (0 : ℂ)}
    (h : scaleGerm ha f = f) (h0 : 0 < ord f) :
    ((orderOf a : ℤ) : WithTop ℤ) ≤ ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [ord_zero]; exact le_top
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (ord_ne_top hf)
  have hnpos : (0 : ℤ) < n := by
    have hlt : ((0 : ℤ) : WithTop ℤ) < ((n : ℤ) : WithTop ℤ) := by
      rw [hn, WithTop.coe_zero]; exact h0
    exact WithTop.coe_lt_coe.1 hlt
  have hone : a ^ n = 1 := zpow_eq_one_of_scaleGerm_eq_self ha hn.symm h
  have hnat : a ^ n.toNat = 1 := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hnpos.le]
    exact hone
  have hdvd : orderOf a ∣ n.toNat := orderOf_dvd_iff_pow_eq_one.2 hnat
  have hle : orderOf a ≤ n.toNat := Nat.le_of_dvd (by omega) hdvd
  rw [← hn, WithTop.coe_le_coe]
  omega

/-! ### The filtration of the integral model by the order of vanishing -/

section Filtration

variable {B : Type*} [CommRing B] {Ψ : B →+* MeroGerm (0 : ℂ)}

/-- The elements of a ring of germs without poles whose germ vanishes to order at least `n`. -/
def ordIdeal (h0 : ∀ b : B, (0 : WithTop ℤ) ≤ ord (Ψ b)) (n : ℤ) : Ideal B where
  carrier := {b : B | (n : WithTop ℤ) ≤ ord (Ψ b)}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add]
    exact le_trans (le_min hx hy) (ord_add _ _)
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
    rw [map_mul, ord_mul]
    have hle : ((0 : ℤ) : WithTop ℤ) + (n : WithTop ℤ) ≤ ord (Ψ c) + ord (Ψ x) :=
      add_le_add (by exact_mod_cast h0 c) hx
    simpa using hle

theorem mem_ordIdeal {h0 : ∀ b : B, (0 : WithTop ℤ) ≤ ord (Ψ b)} {n : ℤ} {b : B} :
    b ∈ ordIdeal h0 n ↔ (n : WithTop ℤ) ≤ ord (Ψ b) := Iff.rfl

theorem ordIdeal_mul_le (h0 : ∀ b : B, (0 : WithTop ℤ) ≤ ord (Ψ b)) (m n : ℤ) :
    ordIdeal h0 m * ordIdeal h0 n ≤ ordIdeal h0 (m + n) := by
  rw [Ideal.mul_le]
  intro r hr t ht
  rw [mem_ordIdeal] at hr ht ⊢
  rw [map_mul, ord_mul]
  have hle : ((m : ℤ) : WithTop ℤ) + ((n : ℤ) : WithTop ℤ) ≤ ord (Ψ r) + ord (Ψ t) :=
    add_le_add hr ht
  simpa using hle

end Filtration

section Place

variable {B : Type*} [CommRing B] [Algebra (Polynomial ℂ) B] {s : ℂ} {d : ℕ}
  {Ψ : B →+* MeroGerm (0 : ℂ)}

/-- **Refined order bound on the powers of the germ place**: if every element of the place has
germ vanishing to order at least `m`, then every element of its `n`-th power vanishes to order at
least `n * m`. -/
theorem le_ord_of_mem_germPlace_pow_of_le
    (hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p)
    (hint : ∀ b : B, IsIntegral (Polynomial ℂ) b) {m : ℤ}
    (hm : ∀ b ∈ germPlace hΨ hint, (m : WithTop ℤ) ≤ ord (Ψ b)) (n : ℕ) {b : B}
    (hb : b ∈ germPlace hΨ hint ^ n) : (((n : ℤ) * m : ℤ) : WithTop ℤ) ≤ ord (Ψ b) := by
  have h0 : ∀ b : B, (0 : WithTop ℤ) ≤ ord (Ψ b) := ord_nonneg_of_kummer hΨ hint
  have key : ∀ k : ℕ, germPlace hΨ hint ^ k ≤ ordIdeal h0 ((k : ℤ) * m) := by
    intro k
    induction k with
    | zero =>
      intro x _
      rw [mem_ordIdeal]
      simpa using h0 x
    | succ k ih =>
      have h1 : germPlace hΨ hint ^ (k + 1) ≤ ordIdeal h0 ((k : ℤ) * m) * ordIdeal h0 m := by
        rw [pow_succ]
        exact Ideal.mul_mono ih hm
      refine h1.trans ((ordIdeal_mul_le h0 _ _).trans ?_)
      have hcast : ((k : ℤ) * m + m) = ((k + 1 : ℕ) : ℤ) * m := by push_cast; ring
      rw [hcast]
  exact key n hb

end Place

end Rigidity.RET.Analytic

end
