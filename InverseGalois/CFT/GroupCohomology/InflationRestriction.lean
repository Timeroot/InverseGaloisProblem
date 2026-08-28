/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.Inflation

/-!
# Exactness of the inflation-restriction sequence in degree two

Let `N` be a normal subgroup of `G` acting on a commutative group `M`.  A two-cocycle of `G` which
is a coboundary when restricted to `N` is, as soon as the first cohomology of `N` vanishes,
cohomologous to a cocycle inflated from the quotient: one whose value at a pair depends only on the
pair of cosets, and whose values are fixed by `N`.  Together with the injectivity of inflation this
is the exactness of

  `0 → H²(G/N, Mᴺ) → H²(G, M) → H²(N, M)`.

The subgroup of index two is treated by hand elsewhere, with the two cosets named; here the naming
is replaced by a choice of representative for every coset and the same three corrections are run.
A one-cochain trivialising the restriction is extended by one to give a cocycle trivial on `N × N`;
a second correction, built from the values of the cocycle at the pairs `(g s(g)⁻¹, s(g))` splitting
an element along its coset, makes it trivial at every pair whose first entry lies in `N`; and a
third, built from a trivialisation on `N` of the one-cocycle `n ↦ a (σ, σ⁻¹ n σ)` attached to each
coset representative `σ`, makes it trivial at every pair whose second entry lies in `N`.  A cocycle
trivial at every pair with an entry in `N` is then inflated, by two applications of the cocycle
identity, and its values are automatically `N`-invariant.

The consequence used in a dévissage is the last theorem: a group whose subgroup and quotient both
have vanishing second cohomology has vanishing second cohomology, provided the first cohomology of
the subgroup vanishes as well.

## Main results

* `InverseGalois.CFT.exists_cosetSection`: a normal subgroup admits a choice of coset
  representatives sending the subgroup itself to the identity.
* `InverseGalois.CFT.exists_twist_eq_one_of_mem_left_of_section`: a two-cocycle trivial on the
  subgroup becomes, after a twist, trivial at every pair whose first entry lies in the subgroup.
* `InverseGalois.CFT.exists_twist_eq_one_of_mem_of_section`: it becomes, after a further twist,
  trivial at every pair with an entry in the subgroup.
* `InverseGalois.CFT.exists_twist_inflated`: **a two-cocycle whose restriction to a normal subgroup
  is a coboundary is cohomologous to an inflated cocycle**, when the first cohomology of the
  subgroup vanishes.
* `InverseGalois.CFT.isMulCoboundary₂_of_forall_subgroup_of_forall_inflated`: **the second
  cohomology of a group vanishes as soon as that of a normal subgroup, that of the quotient, and
  the first cohomology of the subgroup do.**

## Tags

group cohomology, inflation, restriction, two-cocycle, coboundary, normal subgroup, dévissage
-/

namespace InverseGalois.CFT

open groupCohomology

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-! ### A choice of coset representatives -/

/-- **A normal subgroup admits a choice of coset representatives sending the subgroup itself to the
identity.**  The map records, for each element, a representative of its coset, and it is constant
on cosets. -/
theorem exists_cosetSection (N : Subgroup G) [N.Normal] :
    ∃ s : G → G, (∀ g : G, g * (s g)⁻¹ ∈ N) ∧ (∀ g h : G, g * h⁻¹ ∈ N → s g = s h) ∧ s 1 = 1 := by
  classical
  set o : G → G := fun g => Quotient.out (QuotientGroup.mk g : G ⧸ N) with ho
  have hmk : ∀ g : G, g * (o g)⁻¹ ∈ N := by
    intro g
    have h : (o g)⁻¹ * g ∈ N :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : G ⧸ N))
    have hc := ‹N.Normal›.conj_mem _ h (o g)
    rwa [show o g * ((o g)⁻¹ * g) * (o g)⁻¹ = g * (o g)⁻¹ by group] at hc
  obtain ⟨s, hsdef⟩ : ∃ s : G → G, ∀ g : G, s g = if g ∈ N then 1 else o g := ⟨_, fun _ => rfl⟩
  refine ⟨s, fun g => ?_, ?_, by rw [hsdef]; simp⟩
  · rw [hsdef]
    by_cases hg : g ∈ N
    · simp [hg]
    · simpa [hg] using hmk g
  · intro g h hgh
    have hmem : g ∈ N ↔ h ∈ N := by
      refine ⟨fun hg => ?_, fun hh => ?_⟩
      · simpa using mul_mem (inv_mem hgh) hg
      · simpa using mul_mem hgh hh
    have heq : (QuotientGroup.mk g : G ⧸ N) = QuotientGroup.mk h := by
      refine QuotientGroup.eq.mpr ?_
      have hc := ‹N.Normal›.conj_mem _ (inv_mem hgh) g⁻¹
      rwa [show g⁻¹ * (g * h⁻¹)⁻¹ * g⁻¹⁻¹ = g⁻¹ * h by group] at hc
    rw [hsdef, hsdef]
    by_cases hg : g ∈ N
    · rw [if_pos hg, if_pos (hmem.mp hg)]
    · rw [if_neg hg, if_neg fun hh => hg (hmem.mpr hh), ho]
      simp only
      rw [heq]

/-! ### Consequences of the defining properties of a section -/

section SectionLemmas

variable {N : Subgroup G} [N.Normal] {s : G → G}

omit [N.Normal] in
/-- A representative of the coset of an element of the subgroup is the identity. -/
theorem cosetSection_eq_one (hsc : ∀ g h : G, g * h⁻¹ ∈ N → s g = s h) (hs1 : s 1 = 1)
    {n : G} (hn : n ∈ N) : s n = 1 := by
  rw [hsc n 1 (by simpa using hn), hs1]

/-- Multiplying on the right by an element of the subgroup does not change the representative. -/
theorem cosetSection_mul_right (hsc : ∀ g h : G, g * h⁻¹ ∈ N → s g = s h) (g : G)
    {n : G} (hn : n ∈ N) : s (g * n) = s g :=
  hsc _ _ (by simpa using ‹N.Normal›.conj_mem _ hn g)

omit [N.Normal] in
/-- Multiplying on the left by an element of the subgroup does not change the representative. -/
theorem cosetSection_mul_left (hsc : ∀ g h : G, g * h⁻¹ ∈ N → s g = s h) (g : G)
    {n : G} (hn : n ∈ N) : s (n * g) = s g :=
  hsc _ _ (by simpa using hn)

omit [N.Normal] in
/-- The chosen representative of a coset represents its own coset. -/
theorem cosetSection_cosetSection (hs : ∀ g : G, g * (s g)⁻¹ ∈ N)
    (hsc : ∀ g h : G, g * h⁻¹ ∈ N → s g = s h) (g : G) : s (s g) = s g :=
  hsc _ _ (by simpa using inv_mem (hs g))

end SectionLemmas

/-! ### The second normalisation -/

section SecondNormalisation

variable {N : Subgroup G} [N.Normal] {s : G → G}

omit [N.Normal] in
/-- **A two-cocycle trivial on the subgroup becomes, after a twist, trivial at every pair whose
first entry lies in the subgroup.**  The correcting cochain reads the value of the cocycle at the
pair splitting an element along its coset. -/
theorem exists_twist_eq_one_of_mem_left_of_section
    (hs : ∀ g : G, g * (s g)⁻¹ ∈ N) (hsc : ∀ g h : G, g * h⁻¹ ∈ N → s g = s h) (hs1 : s 1 = 1)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (h0 : ∀ x ∈ N, ∀ y ∈ N, a (x, y) = 1) :
    ∃ u : G → M, ∀ n ∈ N, ∀ y : G, twist a u (n, y) = 1 := by
  obtain ⟨u, hu⟩ : ∃ u : G → M, ∀ g : G, u g = (a (g * (s g)⁻¹, s g))⁻¹ := ⟨_, fun _ => rfl⟩
  refine ⟨u, fun n hn y => ?_⟩
  have hun : u n = 1 := by
    rw [hu, cosetSection_eq_one hsc hs1 hn, inv_one, mul_one, h0 n hn 1 N.one_mem, inv_one]
  have hkey : a (n * y * (s y)⁻¹, s y) = n • a (y * (s y)⁻¹, s y) * a (n, y) := by
    have h := ha n (y * (s y)⁻¹) (s y)
    rw [h0 n hn _ (hs y), mul_one, inv_mul_cancel_right,
      show n * (y * (s y)⁻¹) = n * y * (s y)⁻¹ by group] at h
    exact h
  have hsny : s (n * y) = s y := cosetSection_mul_left hsc y hn
  rw [twist_apply, hun, mul_one, hu, hu, hsny, hkey]
  apply Additive.ofMul.injective
  simp only [smul_inv', div_eq_mul_inv, mul_inv, inv_inv, ofMul_mul, ofMul_inv, ofMul_one]
  abel

end SecondNormalisation

/-! ### The third normalisation -/

section ThirdNormalisation

variable {N : Subgroup G} [N.Normal] {s : G → G}

/-- Attached to each element of `G` is a map on the subgroup, the value of the cocycle at the pair
formed by that element and a conjugate.  When the cocycle is trivial at every pair whose first
entry lies in the subgroup this map is a one-cocycle. -/
theorem isMulCocycle₁_conj_of_eq_one {a : G × G → M} (ha : IsMulCocycle₂ a)
    (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1) (σ : G) :
    ∀ x ∈ N, ∀ y ∈ N,
      (fun m : G => a (σ, σ⁻¹ * m * σ)) (x * y)
        = x • (fun m : G => a (σ, σ⁻¹ * m * σ)) y * (fun m : G => a (σ, σ⁻¹ * m * σ)) x := by
  intro x hx y hy
  have hp : σ⁻¹ * x * σ ∈ N := by simpa using ‹N.Normal›.conj_mem _ hx σ⁻¹
  have hmain := ha σ (σ⁻¹ * x * σ) (σ⁻¹ * y * σ)
  rw [h1 _ hp _, smul_one, one_mul] at hmain
  have hxσ : a (σ * (σ⁻¹ * x * σ), σ⁻¹ * y * σ) = x • a (σ, σ⁻¹ * y * σ) := by
    rw [show σ * (σ⁻¹ * x * σ) = x * σ by group]
    exact smul_apply_of_mem_left ha h1 hx σ _
  rw [hxσ] at hmain
  simp only
  rw [show σ⁻¹ * (x * y) * σ = σ⁻¹ * x * σ * (σ⁻¹ * y * σ) by group]
  exact hmain.symm

/-- **A two-cocycle trivial at every pair whose first entry lies in the subgroup becomes, after a
twist, trivial at every pair with an entry in the subgroup.**  This is the step which consumes the
vanishing of the first cohomology of the subgroup. -/
theorem exists_twist_eq_one_of_mem_of_section
    (hs : ∀ g : G, g * (s g)⁻¹ ∈ N) (hsc : ∀ g h : G, g * h⁻¹ ∈ N → s g = s h) (hs1 : s 1 = 1)
    (hH1 : ∀ f : G → M, (∀ x ∈ N, ∀ y ∈ N, f (x * y) = x • f y * f x) →
      ∃ t : M, ∀ x ∈ N, x • t / t = f x)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1) :
    ∃ u : G → M, (∀ n ∈ N, ∀ y : G, twist a u (n, y) = 1) ∧
      (∀ x : G, ∀ n ∈ N, twist a u (x, n) = 1) := by
  classical
  choose T hT using fun σ : G =>
    hH1 (fun m : G => a (σ, σ⁻¹ * m * σ)) (isMulCocycle₁_conj_of_eq_one ha h1 σ)
  obtain ⟨T', hT'one, hT'⟩ : ∃ T' : G → M, T' 1 = 1 ∧
      ∀ σ : G, ∀ x ∈ N, x • T' σ / T' σ = a (σ, σ⁻¹ * x * σ) := by
    obtain ⟨T', hT'def⟩ : ∃ T' : G → M, ∀ σ : G, T' σ = if σ = 1 then 1 else T σ :=
      ⟨_, fun _ => rfl⟩
    refine ⟨T', by rw [hT'def]; simp, fun σ x hx => ?_⟩
    rw [hT'def]
    by_cases hσ : σ = 1
    · subst hσ
      rw [if_pos rfl, smul_one, div_one, h1 1 N.one_mem]
    · rw [if_neg hσ]
      exact hT σ x hx
  obtain ⟨u, hu⟩ : ∃ u : G → M, ∀ g : G, u g = (g * (s g)⁻¹) • (T' (s g))⁻¹ := ⟨_, fun _ => rfl⟩
  have hun : ∀ n ∈ N, u n = 1 := by
    intro n hn
    rw [hu, cosetSection_eq_one hsc hs1 hn, hT'one]
    simp
  have hone : ∀ n ∈ N, ∀ y : G, twist a u (n, y) = 1 := by
    intro n hn y
    have hstep : u (n * y) = n • u y := by
      rw [hu, hu, cosetSection_mul_left hsc y hn, ← mul_smul, mul_assoc]
    rw [twist_apply, h1 n hn y, hun n hn, mul_one, hstep, div_self', div_one]
  have hrep : ∀ σ : G, s σ = σ → ∀ n ∈ N, twist a u (σ, n) = 1 := by
    intro σ hσ n hn
    have hcn : σ * n * σ⁻¹ ∈ N := ‹N.Normal›.conj_mem _ hn σ
    have hval : (σ * n * σ⁻¹) • T' σ / T' σ = a (σ, n) := by
      have h := hT' σ _ hcn
      rwa [show σ⁻¹ * (σ * n * σ⁻¹) * σ = n by group] at h
    have huσ : u σ = (T' σ)⁻¹ := by rw [hu, hσ, mul_inv_cancel, one_smul]
    have huσn : u (σ * n) = (σ * n * σ⁻¹) • (T' σ)⁻¹ := by
      rw [hu, cosetSection_mul_right hsc σ hn, hσ]
    rw [twist_apply, hun n hn, smul_one, huσn, huσ, smul_inv', one_div, inv_inv,
      ← div_eq_mul_inv, hval, div_self']
  refine ⟨u, hone, fun x n hn => ?_⟩
  have hkey := smul_apply_of_mem_left (isMulCocycle₂_twist ha u) hone (hs x) (s x) n
  rw [show x * (s x)⁻¹ * s x = x by group] at hkey
  rw [hkey, hrep (s x) (cosetSection_cosetSection hs hsc x) n hn, smul_one]

end ThirdNormalisation

/-! ### A cocycle trivial along the subgroup is inflated -/

section Inflated

variable {N : Subgroup G}

/-- A two-cocycle trivial at every pair whose second entry lies in the subgroup is unchanged by
multiplying its second entry on the right by an element of the subgroup. -/
theorem apply_mul_right_eq_of_eq_one {a : G × G → M} (ha : IsMulCocycle₂ a)
    (h2 : ∀ x : G, ∀ n ∈ N, a (x, n) = 1) (x y : G) {m : G} (hm : m ∈ N) :
    a (x, y * m) = a (x, y) := by
  have h := ha x y m
  rw [h2 _ m hm, h2 _ m hm, smul_one, one_mul, one_mul] at h
  exact h.symm

/-- A two-cocycle trivial at every pair with an entry in the subgroup is unchanged by multiplying
its first entry on the right by an element of the subgroup. -/
theorem apply_mul_left_eq_of_eq_one [N.Normal] {a : G × G → M} (ha : IsMulCocycle₂ a)
    (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1) (h2 : ∀ x : G, ∀ n ∈ N, a (x, n) = 1)
    (x y : G) {n : G} (hn : n ∈ N) : a (x * n, y) = a (x, y) := by
  have h := ha x n y
  rw [h2 x n hn, h1 n hn y, smul_one, mul_one, one_mul] at h
  have hc : y⁻¹ * n * y ∈ N := by simpa using ‹N.Normal›.conj_mem _ hn y⁻¹
  rw [h, show n * y = y * (y⁻¹ * n * y) by group, apply_mul_right_eq_of_eq_one ha h2 x y hc]

/-- The values of a two-cocycle trivial at every pair with an entry in the subgroup are fixed by
the subgroup. -/
theorem smul_apply_eq_of_eq_one [N.Normal] {a : G × G → M} (ha : IsMulCocycle₂ a)
    (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1) (h2 : ∀ x : G, ∀ n ∈ N, a (x, n) = 1)
    {n : G} (hn : n ∈ N) (x y : G) : n • a (x, y) = a (x, y) := by
  have hc : x⁻¹ * n * x ∈ N := by simpa using ‹N.Normal›.conj_mem _ hn x⁻¹
  rw [← smul_apply_of_mem_left ha h1 hn x y, show n * x = x * (x⁻¹ * n * x) by group,
    apply_mul_left_eq_of_eq_one ha h1 h2 x y hc]

end Inflated

/-! ### Exactness -/

section Exactness

variable {N : Subgroup G} [N.Normal]

/-- **A two-cocycle whose restriction to a normal subgroup is a coboundary is cohomologous to an
inflated cocycle**, as soon as the first cohomology of the subgroup vanishes.  The corrected
cocycle depends only on the pair of cosets and takes values fixed by the subgroup, so it is the
inflation of a two-cocycle of the quotient with values in the invariants.  This is the exactness of
the inflation-restriction sequence in degree two. -/
theorem exists_twist_inflated
    (hH1 : ∀ f : G → M, (∀ x ∈ N, ∀ y ∈ N, f (x * y) = x • f y * f x) →
      ∃ t : M, ∀ x ∈ N, x • t / t = f x)
    {a : G × G → M} (ha : IsMulCocycle₂ a)
    (hres : ∃ b : G → M, ∀ x ∈ N, ∀ y ∈ N, a (x, y) = x • b y / b (x * y) * b x) :
    ∃ u : G → M,
      (∀ (x y n : G), n ∈ N → ∀ m : G, m ∈ N → twist a u (x * n, y * m) = twist a u (x, y)) ∧
      (∀ n : G, n ∈ N → ∀ x y : G, n • twist a u (x, y) = twist a u (x, y)) := by
  obtain ⟨s, hs, hsc, hs1⟩ := exists_cosetSection N
  obtain ⟨u₁, h₁⟩ := exists_twist_eq_one_on_subgroup hres
  obtain ⟨u₂, h₂⟩ :=
    exists_twist_eq_one_of_mem_left_of_section hs hsc hs1 (isMulCocycle₂_twist ha u₁) h₁
  obtain ⟨u₃, h₃, h₄⟩ := exists_twist_eq_one_of_mem_of_section hs hsc hs1 hH1
    (isMulCocycle₂_twist (isMulCocycle₂_twist ha u₁) u₂) h₂
  rw [twist_twist, twist_twist] at h₃ h₄
  refine ⟨u₁ * (u₂ * u₃), fun x y n hn m hm => ?_, fun n hn x y => ?_⟩
  · rw [apply_mul_right_eq_of_eq_one (isMulCocycle₂_twist ha _) h₄ _ _ hm,
      apply_mul_left_eq_of_eq_one (isMulCocycle₂_twist ha _) h₃ h₄ _ _ hn]
  · exact smul_apply_eq_of_eq_one (isMulCocycle₂_twist ha _) h₃ h₄ hn x y

/-- **The second cohomology of a group vanishes as soon as that of a normal subgroup, that of the
quotient, and the first cohomology of the subgroup do.**  This is the dévissage step: a cocycle is
first trivialised along the subgroup, then along the quotient. -/
theorem isMulCoboundary₂_of_forall_subgroup_of_forall_inflated
    (hH1 : ∀ f : G → M, (∀ x ∈ N, ∀ y ∈ N, f (x * y) = x • f y * f x) →
      ∃ t : M, ∀ x ∈ N, x • t / t = f x)
    (hH2N : ∀ b : G × G → M, IsMulCocycle₂ b →
      ∃ c : G → M, ∀ x ∈ N, ∀ y ∈ N, b (x, y) = x • c y / c (x * y) * c x)
    (hH2Q : ∀ b : G × G → M, IsMulCocycle₂ b →
      (∀ (x y n : G), n ∈ N → ∀ m : G, m ∈ N → b (x * n, y * m) = b (x, y)) →
      (∀ n : G, n ∈ N → ∀ x y : G, n • b (x, y) = b (x, y)) → IsMulCoboundary₂ b)
    {a : G × G → M} (ha : IsMulCocycle₂ a) : IsMulCoboundary₂ a := by
  obtain ⟨u, hinfl, hfix⟩ := exists_twist_inflated hH1 ha (hH2N a ha)
  obtain ⟨v, hv⟩ := isMulCoboundary₂_iff.mp (hH2Q _ (isMulCocycle₂_twist ha u) hinfl hfix)
  refine isMulCoboundary₂_iff.mpr ⟨u * v, funext fun p => ?_⟩
  rw [coboundary₂_mul, Pi.mul_apply, hv, mul_comm (coboundary₂ u p) (twist a u p)]
  exact (eq_twist_mul_coboundary₂ a u p).symm

end Exactness

end InverseGalois.CFT
