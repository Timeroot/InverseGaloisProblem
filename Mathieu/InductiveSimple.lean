import Mathlib

/-!
# An inductive simplicity criterion for primitive groups

This file provides a *general, reusable* simplicity criterion that captures the classical
"primitive permutation group with a simple point stabiliser and no regular normal subgroup is
simple" argument.  It is the route used to prove `M₂₃` and `M₂₄` simple, where the
class-equation enumeration used for `M₁₁, M₁₂, M₂₂` is infeasible.

## Mathematical content

Let `G` act faithfully and **primitively** on a finite set `α` (`|α| ≥ 2`), and let `a : α`
have point stabiliser `Gₐ = stabilizer G a`.  Let `N ⊴ G` be a nontrivial normal subgroup.

* The orbits of `N` form a *block system* (`IsBlock.orbit_of_normal`).  By primitivity each
  block is trivial, so `orbit N a` is either `{a}` (then `N ≤ Gₐ`, and being normal in a
  transitive — hence faithful with trivial core — action forces `N = ⊥`) or all of `α`
  (then `N` is **transitive**).
* When `N` is transitive, `N ∩ Gₐ` is a normal subgroup of `Gₐ`.  If `Gₐ` is **simple**, then
  `N ∩ Gₐ` is `⊥` or `Gₐ`.
  - If `N ∩ Gₐ = Gₐ`, then `Gₐ ≤ N`; a transitive subgroup containing a point stabiliser is the
    whole group, so `N = ⊤`.
  - If `N ∩ Gₐ = ⊥`, then `N` acts **regularly** (transitively with trivial stabiliser).  This
    is the *regular normal subgroup* case, excluded by the hypothesis `hreg`.

The regular case is excluded, per group, by the second lemma here:
`stabilizer_injective_mulAut_of_regular`: a faithful action with a regular normal subgroup `N`
gives an **injective** homomorphism `Gₐ ↪ MulAut N` (conjugation), so `|Gₐ|` divides
`|MulAut N|`.  For the Mathieu groups this is numerically absurd (`|M₂₂|` does not divide
`|Aut C₂₃| = 22`, etc.).
-/

namespace Mathieu

open MulAction Subgroup

/-- **Transitive normal subgroup ⇒ stabiliser embeds in `Aut N`.**

If `G` acts faithfully on `α` and `N ⊴ G` is transitive, then conjugation gives an injective
homomorphism from the point stabiliser `Gₐ` into `MulAut N`.  Consequently `|Gₐ|` divides
`|MulAut N|`.  (Applied to a *regular* normal subgroup, this is the classical exclusion of a
regular normal subgroup in a primitive group with a large stabiliser.) -/
theorem stabilizer_injective_mulAut_of_regular
    {G : Type*} [Group G] {α : Type*} [MulAction G α] [FaithfulSMul G α]
    (a : α) (N : Subgroup G) [N.Normal]
    (htrans : MulAction.orbit (↥N) a = Set.univ) :
    ∃ f : ↥(MulAction.stabilizer G a) →* MulAut ↥N, Function.Injective f := by
  refine ⟨?_, ?_⟩
  · exact (MulAut.conjNormal (G := G) (H := N)).comp (MulAction.stabilizer G a).subtype
  intro g h hgh
  -- `conjNormal ↑g = conjNormal ↑h`, so `g` and `h` conjugate every `n ∈ N` the same way.
  have h_comm : ∀ n : ↥N, (g : G) * (n : G) * (g : G)⁻¹ = (h : G) * (n : G) * (h : G)⁻¹ := by
    intro n
    have := congrArg (fun (φ : MulAut ↥N) => (φ n : G)) hgh
    simpa [MulAut.conjNormal_apply] using this
  -- Hence `↑g` and `↑h` act identically on `α` (using transitivity of `N`).
  have h_comm_all : ∀ ω : α, (g : G) • ω = (h : G) • ω := by
    intro ω
    obtain ⟨n, hn⟩ : ∃ n : ↥N, (n : G) • a = ω := Set.eq_univ_iff_forall.mp htrans ω
    have hga : (g : G) • a = a := g.2
    have hha : (h : G) • a = a := h.2
    have key := congrArg (fun x : G => x • a) (h_comm n)
    simp only [mul_smul] at key
    -- key : (↑g) • (↑n) • (↑g)⁻¹ • a = (↑h) • (↑n) • (↑h)⁻¹ • a
    have hg' : ((g : G)⁻¹) • a = a := by
      rw [inv_smul_eq_iff, hga]
    have hh' : ((h : G)⁻¹) • a = a := by
      rw [inv_smul_eq_iff, hha]
    rw [hg', hh'] at key
    rw [← hn]
    -- want (↑g) • (↑n) • a = (↑h) • (↑n) • a, which is `key`
    simpa [mul_smul] using key
  -- Faithfulness gives `↑g = ↑h`, hence `g = h`.
  exact Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul h_comm_all)

/-
**A regular subgroup has the same cardinality as the set it acts on.**

If `N ≤ G` is transitive on the finite set `α` with trivial point stabiliser at `a`, then
`|N| = |α|`.
-/
theorem card_eq_of_regular
    {G : Type*} [Group G] {α : Type*} [MulAction G α] [Finite α]
    (a : α) (N : Subgroup G)
    (htrans : MulAction.orbit (↥N) a = Set.univ)
    (hreg : ∀ n : ↥N, n • a = a → n = 1) :
    Nat.card ↥N = Nat.card α := by
  -- By the orbit-stabilizer theorem, this map is injective.
  have h_inj : Function.Injective (fun n : N => n • a) := by
    intro n m hnm;
    specialize hreg ( m⁻¹ * n ) ; simp_all +decide [ mul_smul ];
    simpa using eq_inv_of_mul_eq_one_right hreg;
  convert Nat.card_congr ( Equiv.ofBijective _ ⟨ h_inj, ?_ ⟩ );
  exact fun x => by rw [ Set.eq_univ_iff_forall ] at htrans; exact htrans x;

/-
**An automorphism of prime order `p` on a group of order `p+1` makes all nonidentity
elements equivalent.**

If `K` is a finite group of order `p+1` (`p` prime) admitting an automorphism `σ` of order
`p`, then `σ` (more precisely the cyclic group `⟨σ⟩`) acts on the `p` nonidentity elements of
`K` with a single orbit; consequently all nonidentity elements of `K` have the same order.

This is the engine behind the exclusion of a regular normal subgroup of order `24` in `M₂₄`:
there `p = 23`, and the conclusion (every nonidentity element has the same order) contradicts
Cauchy's theorem, which produces elements of order `2` and `3`.
-/
theorem orderOf_eq_of_aut_prime_order
    {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (σ : MulAut K) (hσ : orderOf σ = p) (hcard : Nat.card K = p + 1)
    {x y : K} (hx : x ≠ 1) (hy : y ≠ 1) : orderOf x = orderOf y := by
  -- By `IsPGroup.card_modEq_card_fixedPoints`, `Nat.card K ≡ Nat.card (fixedPoints ↥H K) [MOD p]`.
  have hcard_modEq_card_fixedPoints : Nat.card K ≡ Nat.card (MulAction.fixedPoints (↥(Subgroup.zpowers σ)) K) [MOD p] := by
    have hPGroup : IsPGroup p (↥(Subgroup.zpowers σ)) := by
      rw [ IsPGroup.iff_card ];
      rw [ Nat.card_zpowers, hσ ] ; exact ⟨ 1, by simp +decide ⟩;
    convert hPGroup.card_modEq_card_fixedPoints K using 1;
  -- Since `Nat.card K = p + 1 ≡ 1 [MOD p]`, we get `Nat.card (fixedPoints ↥H K) ≡ 1 [MOD p]`.
  have hcard_fixedPoints : Nat.card (MulAction.fixedPoints (↥(Subgroup.zpowers σ)) K) = 1 := by
    have hcard_fixedPoints_le : Nat.card (MulAction.fixedPoints (↥(Subgroup.zpowers σ)) K) ≤ Nat.card K := by
      exact Set.ncard_le_ncard ( Set.subset_univ _ ) |> le_trans <| by simp +decide [ Set.ncard_univ ] ;
    have hcard_fixedPoints_ge : 1 ≤ Nat.card (MulAction.fixedPoints (↥(Subgroup.zpowers σ)) K) := by
      refine' Nat.card_pos_iff.mpr _;
      exact ⟨ ⟨ 1, fun _ => by simp +decide ⟩, Set.Finite.to_subtype <| Set.toFinite _ ⟩
    have hcard_fixedPoints_cases : Nat.card (MulAction.fixedPoints (↥(Subgroup.zpowers σ)) K) = 1 ∨ Nat.card (MulAction.fixedPoints (↥(Subgroup.zpowers σ)) K) = p + 1 := by
      obtain ⟨ k, hk ⟩ := hcard_modEq_card_fixedPoints.symm.dvd;
      rcases lt_trichotomy k 0 with hk' | rfl | hk' <;> first | left; nlinarith | right; nlinarith;
    by_cases h : Nat.card (MulAction.fixedPoints (↥(Subgroup.zpowers σ)) K) = p + 1;
    ·
      have h_all_fixed : ∀ z : K, z ∈ MulAction.fixedPoints (↥(Subgroup.zpowers σ)) K := by
        have h_all_fixed : Set.ncard (MulAction.fixedPoints (↥(Subgroup.zpowers σ)) K) = Set.ncard (Set.univ : Set K) := by
          simp_all +decide [ Set.ncard_univ ];
        exact fun z => by_contra fun hz => absurd h_all_fixed ( ne_of_lt ( Set.ncard_lt_ncard ( show fixedPoints ( ↥ ( zpowers σ ) ) K < Set.univ from lt_of_le_of_ne ( Set.subset_univ _ ) fun h => hz <| h.symm ▸ Set.mem_univ _ ) ) );
      have h_sigma_id : σ = 1 := by
        ext z; specialize h_all_fixed z; simp_all +decide [ MulAction.mem_fixedPoints ] ;
        simpa using h_all_fixed 1;
      exact absurd hσ ( by rw [ h_sigma_id, orderOf_one ] ; exact ne_of_lt ( Nat.Prime.one_lt Fact.out ) )
    ·
      exact hcard_fixedPoints_cases.resolve_right h;
  -- Since `Nat.card (fixedPoints ↥H K) = 1`, we have `fixedPoints ↥H K = {1}`.
  have hfixedPoints : MulAction.fixedPoints (↥(Subgroup.zpowers σ)) K = {1} := by
    rw [ Nat.card_eq_one_iff_unique ] at hcard_fixedPoints;
    exact Set.eq_singleton_iff_unique_mem.mpr ⟨ by simp +decide [ fixedPoints ], fun x hx => Subtype.ext_iff.mp ( hcard_fixedPoints.1.elim ⟨ x, hx ⟩ ⟨ 1, by simp +decide [ fixedPoints ] ⟩ ) ⟩;
  -- Since `x ≠ 1`, `x` is not a fixed point (by Step 2), so its orbit `MulAction.orbit ↥H x` is not a singleton; by `IsPGroup.card_orbit` its cardinality is `p^n`, and being `> 1` forces `n ≥ 1`, so `p ∣ Nat.card (orbit ↥H x)` and `Nat.card (orbit ↥H x) ≥ p`.
  have hcard_orbit : ∀ x : K, x ≠ 1 → Nat.card (MulAction.orbit (↥(Subgroup.zpowers σ)) x) = p := by
    intros x hx_ne_one
    have hcard_orbit : Nat.card (MulAction.orbit (↥(Subgroup.zpowers σ)) x) ∣ p := by
      convert Subgroup.card_quotient_dvd_card ( MulAction.stabilizer ( ↥ ( Subgroup.zpowers σ ) ) x ) using 1;
      · exact Nat.card_congr ( MulAction.orbitEquivQuotientStabilizer ( ↥ ( Subgroup.zpowers σ ) ) x );
      · rw [ Nat.card_zpowers, hσ ];
    rw [ Nat.dvd_prime Fact.out ] at hcard_orbit;
    cases' hcard_orbit with h h;
    · rw [ Nat.card_eq_one_iff_unique ] at h;
      simp_all +decide [ Set.ext_iff, MulAction.mem_orbit_iff ];
    · exact h;
  -- Since `y ≠ 1`, `y ∈ (K \ {1})` `= orbit ↥H x`, so there is `τ : ↥H` with `τ • x = y`, i.e. `(τ : MulAut K) x = y`.
  obtain ⟨τ, hτ⟩ : ∃ τ : ↥(Subgroup.zpowers σ), (τ : MulAut K) x = y := by
    have h_orbit_eq : MulAction.orbit (↥(Subgroup.zpowers σ)) x = (Set.univ \ {1} : Set K) := by
      apply Set.eq_of_subset_of_ncard_le;
      · intro z hz
        obtain ⟨τ, hτ⟩ := hz
        aesop;
      · simp_all +decide;
      · exact Set.toFinite _;
    exact h_orbit_eq.symm.subset ⟨ Set.mem_univ _, hy ⟩;
  rw [ ← hτ, MulEquiv.orderOf_eq ]

/-- **Inductive simplicity criterion.**

A finite group `G` acting faithfully and primitively on a finite set `α` with at least two
points, whose point stabiliser `Gₐ` is simple and which has no regular normal subgroup
(hypothesis `hreg`), is simple. -/
theorem isSimpleGroup_of_isPreprimitive_of_simpleStabilizer
    {G : Type*} [Group G] [Finite G]
    {α : Type*} [MulAction G α] [Finite α] [Nontrivial α]
    [FaithfulSMul G α] [IsPreprimitive G α]
    (a : α)
    (hstab : IsSimpleGroup ↥(MulAction.stabilizer G a))
    (hreg : ∀ N : Subgroup G, N.Normal → MulAction.orbit (↥N) a = Set.univ →
      (∀ n : ↥N, n • a = a → n = 1) → False) :
    IsSimpleGroup G := by
  have h_nontrivial : Nontrivial G := by
    contrapose! hreg
    exact absurd hstab.exists_pair_ne (by simp [eq_iff_true_of_subsingleton])
  refine { eq_bot_or_eq_top_of_normal := ?_ }
  intro N hN_normal
  have h_orbit : (MulAction.orbit (↥N) a).Subsingleton ∨ MulAction.orbit (↥N) a = Set.univ :=
    IsPreprimitive.isTrivialBlock_of_isBlock (IsBlock.orbit_of_normal a)
  cases' h_orbit with h_orbit h_orbit
  · -- `orbit N a` is a singleton: `N ≤ stabilizer`, and normality + faithful transitive ⇒ `N = ⊥`.
    have hN_le_stab : N ≤ MulAction.stabilizer G a := by
      intro n hn
      have := h_orbit (show n • a ∈ orbit (↥N) a from ⟨⟨n, hn⟩, rfl⟩)
        (show a ∈ orbit (↥N) a from ⟨1, by simp⟩)
      aesop
    have hN_trivial : ∀ n ∈ N, ∀ ω : α, n • ω = ω := by
      intro n hn ω
      obtain ⟨g, hg⟩ : ∃ g : G, g • a = ω := MulAction.exists_smul_eq G a ω
      have := hN_le_stab (hN_normal.conj_mem _ hn g⁻¹)
      simp_all [mul_smul, inv_smul_eq_iff]
    have hN_bot : ∀ n ∈ N, n = 1 := fun n hn =>
      ‹FaithfulSMul G α›.eq_of_smul_eq_smul fun ω => by simpa using hN_trivial n hn ω
    exact Or.inl (eq_bot_iff.mpr hN_bot)
  · -- `N` is transitive.  Use simplicity of the stabiliser on `N ∩ Gₐ = N.subgroupOf (stab)`.
    have hK : (N.subgroupOf (stabilizer G a)) = ⊥ ∨ (N.subgroupOf (stabilizer G a)) = ⊤ :=
      hstab.eq_bot_or_eq_top_of_normal _ Subgroup.normal_subgroupOf
    cases' hK with hK hK
    · -- `N ∩ Gₐ = ⊥`: `N` is regular, contradicting `hreg`.
      refine absurd (hreg N hN_normal h_orbit ?_) (fun h => h)
      intro n hn
      have hxstab : (n : G) ∈ stabilizer G a := by
        rw [MulAction.mem_stabilizer_iff]; simpa using hn
      have hmem : (⟨(n : G), hxstab⟩ : ↥(stabilizer G a)) ∈ N.subgroupOf (stabilizer G a) := by
        rw [Subgroup.mem_subgroupOf]; exact n.2
      rw [hK, Subgroup.mem_bot] at hmem
      have hval : (n : G) = 1 := congrArg Subtype.val hmem
      exact Subtype.ext hval
    · -- `Gₐ ≤ N` and `N` transitive ⇒ `N = ⊤`.
      have h_stab_le_N : stabilizer G a ≤ N := by
        intro x hx
        have hmem : (⟨x, hx⟩ : ↥(stabilizer G a)) ∈ N.subgroupOf (stabilizer G a) := by
          rw [hK]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf).mp hmem
      refine Or.inr (eq_top_iff.mpr fun g _ => ?_)
      obtain ⟨n, hn⟩ := Set.mem_univ (g • a) |> fun h => h_orbit.symm.subset h
      have hn' : (n : G) • a = g • a := hn
      have h_conj : (n : G)⁻¹ * g ∈ stabilizer G a := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, ← hn', inv_smul_smul]
      simpa using N.mul_mem n.2 (h_stab_le_N h_conj)

end Mathieu