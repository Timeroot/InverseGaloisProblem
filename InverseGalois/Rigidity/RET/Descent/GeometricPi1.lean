/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Descent.Data

/-!
# The geometric fundamental group — presentation of `N` by the sphere group

This module supplies the **algebraic layer** of the branch-cycle descent's geometric input: the
`GeometricInertiaData` structure (the tame inertia generators of `N = Gal(Ω/k₀(T))`) and the
reduction of the geometric presentation to that data.  The arithmetic geometry — the *existence* of
the data — lives in `Descent.Tower` (`geomInertiaModel_exists`), where the arithmetic model `N ⊴ E`
is available.

## What this file is (and why the existence is NOT here)

The tower needs, for the certificate's rigid generating product-one tuple `base`, a surjection
`pres : SphereGroup r ↠ N` realizing the monodromy `φ` as the sphere hom of `base`, *and* satisfying
Fried's branch-cycle formula.  This file factors the *algebra* of that goal into:

* a **structure** `GeometricInertiaData` — the tame inertia generators `gᵢ ∈ N` (one per branch
  point) with their defining properties: they generate `N`, satisfy the product-one sphere relation,
  realize `φ (gᵢ) = baseᵢ`, and obey the cyclotomic branch-cycle;
* a **reduction** `geomPresentation_of_inertiaData`: from that data the full presentation conclusion
  follows by elementary group theory (the sphere-hom of the generators).

**Crucially, the existence of `GeometricInertiaData` cannot be stated over an abstract tower.**  For
an *arbitrary* surjection `φ : N ↠ G` and rigid tuple `base`, the data need **not** exist:
e.g. `G = ℤ/2`, `r = 2`, `base = (a, a)` (generating, product-one), `N = ℤ/2 × ℤ/2`, `φ` the
projection — any product-one lift forces `g₀ = g₁`, so the lifts generate a cyclic subgroup, never
all of `N`.  The data exists only because `N` is the *geometric fundamental group of the cover
branched over the `r` points with monodromy `base`* — geometric information an abstract `N ⊴ E` does
not carry.  Hence the existence (`geomInertiaModel_exists`, `Descent.Tower`) must *produce the model
`m` together with the data*, existentially choosing `N = Gal(Ω/k₀(T))` for the right cover; it is the
Riemann Existence Theorem at the `N` level, not an abstract group-theory fact.

## Main results

* `GeometricInertiaData` — the tame inertia generators and their defining properties.
* `geomPresentation_of_inertiaData` — the presentation conclusion from the data.

The existence of the data (Riemann existence at the `N` level) is `geomInertiaModel_exists` in
`Descent.Tower`; see its docstring for the two mathematical inputs (tame `π₁` presentation +
cyclotomic action on tame inertia).
-/

open Polynomial

namespace Rigidity.RET

/-- **The tame inertia generators of the geometric Galois group `N`.**

For an arithmetic tower `N ⊴ E` (here abstracted to the raw group data `E`, `N`, `φ : N ↠ G`) and a
rigid generating product-one tuple `base` from the certificate, this bundles the geometric inertia
generators `gᵢ ∈ N` — one per branch point — with the four properties that make `N` the geometric
monodromy group of the branch cover:

* `gen_top` — the `gᵢ` **generate** `N` (the cover is connected);
* `gen_prod` — they satisfy the **product-one sphere relation** `g₀ ⋯ g_{r-1} = 1` (the single
  relation of `π₁(ℙ¹ ∖ {r points})`);
* `φ_gen` — `φ` realizes the certificate's **monodromy**: `φ (gᵢ) = baseᵢ`;
* `branchCycle` — **Fried's tame branch-cycle formula**: for each `e : E` lifting `σ ∈ Γ` there is a
  cyclotomic exponent `k = χ(σ)`, coprime to every base-generator order, with `φ (e · gᵢ · e⁻¹)`
  conjugate to `baseᵢ ^ k` — i.e. `E` acts on tame inertia through the cyclotomic character.

Producing an inhabitant (bundled with its model) is `geomInertiaModel_exists` (`Descent.Tower`),
where the Riemann Existence Theorem enters. -/
structure GeometricInertiaData {G : Type} [Group G] [Finite G] {cert : RigidData G}
    {E : Type} [Group E] (N : Subgroup E) [N.Normal] (φ : N →* G)
    (base : Fin cert.r → G) (hbase : base ∈ rigidTuples cert.C) where
  /-- the tame inertia generators: one element of `N` per branch point. -/
  gen : Fin cert.r → N
  /-- the inertia generators generate `N` (the cover is connected). -/
  gen_top : Subgroup.closure (Set.range gen) = ⊤
  /-- the product-one sphere relation `g₀ ⋯ g_{r-1} = 1`. -/
  gen_prod : (List.ofFn gen).prod = 1
  /-- `φ` realizes the certificate's monodromy: `φ (gᵢ) = baseᵢ`. -/
  φ_gen : ∀ i, φ (gen i) = base i
  /-- **Fried's tame branch-cycle formula**: `E` acts on tame inertia through the cyclotomic
  character.  For each `e : E` there is an exponent `k = χ(σ)`, coprime to every base-generator order,
  with `φ (e · gᵢ · e⁻¹)` conjugate to `baseᵢ ^ k`. -/
  branchCycle : ∀ e : E, ∃ k : ℕ, (∀ i, Nat.Coprime k (orderOf (base i))) ∧
    ∀ i, ConjClasses.mk (φ (Rigidity.RET.conjN N e (gen i))) = ConjClasses.mk (base i ^ k)

/-- **The algebraic reduction (B1+C).**  From the tame inertia generators, the full
geometric-presentation conclusion follows: the sphere hom of the generators is the required
surjection `pres`, it realizes `φ` as the sphere hom of `base`, and its branch-cycle conjunct is the
data's `branchCycle` field (`pres (of i) = gᵢ`).  No arithmetic-geometry input — this is exactly the
elementary group theory the presentation packages.  Consumed by `geomTower_nonempty`. -/
theorem geomPresentation_of_inertiaData {G : Type} [Group G] [Finite G]
    {cert : RigidData G} {E : Type} [Group E] (N : Subgroup E) [N.Normal] (φ : N →* G)
    (base : Fin cert.r → G) (hbase : base ∈ rigidTuples cert.C)
    (d : GeometricInertiaData N φ base hbase) :
    ∃ pres : Rigidity.RET.SphereGroup cert.r →* N, Function.Surjective pres ∧
      (∀ x : Rigidity.RET.SphereGroup cert.r,
        φ (pres x) = Rigidity.RET.sphereHom base hbase.2.1 x) ∧
      ∀ e : E, ∃ k : ℕ, (∀ i, Nat.Coprime k (orderOf (base i))) ∧
        ∀ i, ConjClasses.mk (φ (Rigidity.RET.conjN N e (pres (PresentedGroup.of i)))) =
          ConjClasses.mk (base i ^ k) := by
  refine ⟨Rigidity.RET.sphereHom d.gen d.gen_prod, ?_, ?_, ?_⟩
  · -- surjectivity: the generators generate `N`.
    rw [Rigidity.RET.sphereHom_surjective_iff d.gen d.gen_prod]
    exact d.gen_top
  · -- `φ ∘ pres = sphereHom base`: two homs agreeing on every generator.
    have hhom : φ.comp (Rigidity.RET.sphereHom d.gen d.gen_prod)
        = Rigidity.RET.sphereHom base hbase.2.1 := by
      ext i
      rw [MonoidHom.comp_apply, Rigidity.RET.sphereHom_of, Rigidity.RET.sphereHom_of, d.φ_gen]
    exact fun x => DFunLike.congr_fun hhom x
  · -- branch-cycle: `pres (of i) = gᵢ`, so this is exactly the data's `branchCycle` field.
    intro e
    obtain ⟨k, hcop, heq⟩ := d.branchCycle e
    refine ⟨k, hcop, fun i => ?_⟩
    rw [Rigidity.RET.sphereHom_of]
    exact heq i

/-- **The tame inertia generators with the geometric cyclotomic action.**

This is the *sharper* geometric datum that `GeometricInertiaData` unpacks to.  It carries the same
presentation content (`gen_top`, `gen_prod`, `φ_gen`) but replaces the derived class-level branch
cycle by its geometric source: the **cyclotomic conjugacy on tame inertia itself**.  For each
`e : E` there is one exponent `k = χ(σ)` (`σ ∈ Γ` the image of `e`), coprime to every inertia
generator's order `orderOf gᵢ` (= the ramification index at branch point `i`), with
`e · gᵢ · e⁻¹` **conjugate inside `N`** to `gᵢ ^ k`.

This is exactly how tame inertia transforms under the arithmetic Galois action: tame inertia at a
branch point is canonically `≅ Ẑ(1)` (the Tate twist), and `Γ` acts on it through the cyclotomic
character, so a lift `e` of `σ` conjugates a topological generator to its `χ(σ)`-th power (up to the
choice of generator, i.e. up to `N`-conjugacy).  Separating this from the class-level formula is the
honest cut: the conjugacy lives in `N` and is genuinely geometric, whereas pushing it through `φ`
to conjugacy classes in `G` is elementary. -/
structure TameInertiaData {G : Type} [Group G] [Finite G] {cert : RigidData G}
    {E : Type} [Group E] (N : Subgroup E) [N.Normal] (φ : N →* G)
    (base : Fin cert.r → G) (hbase : base ∈ rigidTuples cert.C) where
  /-- the tame inertia generators: one element of `N` per branch point. -/
  gen : Fin cert.r → N
  /-- the inertia generators generate `N` (the cover is connected). -/
  gen_top : Subgroup.closure (Set.range gen) = ⊤
  /-- the product-one sphere relation `g₀ ⋯ g_{r-1} = 1`. -/
  gen_prod : (List.ofFn gen).prod = 1
  /-- `φ` realizes the certificate's monodromy: `φ (gᵢ) = baseᵢ`. -/
  φ_gen : ∀ i, φ (gen i) = base i
  /-- **The cyclotomic action on tame inertia.**  For each `e : E` there is an exponent `k = χ(σ)`,
  coprime to every inertia generator's order, with `e · gᵢ · e⁻¹` conjugate *inside `N`* to
  `gᵢ ^ k`.  This is Fried's branch cycle at its geometric source, before pushing through `φ`. -/
  cyclo_conj : ∀ e : E, ∃ k : ℕ, (∀ i, Nat.Coprime k (orderOf (gen i))) ∧
    ∀ i, IsConj (Rigidity.RET.conjN N e (gen i)) ((gen i) ^ k)

/-- **Sorry-free reduction: the class-level branch cycle from the cyclotomic conjugacy.**

Given the tame inertia data with its geometric cyclotomic conjugacy (`e · gᵢ · e⁻¹ ~_N gᵢ ^ k`),
the class-level `branchCycle` field of `GeometricInertiaData` follows by elementary group theory:

* **Coprimality** upgrades from `orderOf gᵢ` to `orderOf baseᵢ` because `baseᵢ = φ gᵢ`, so
  `orderOf baseᵢ ∣ orderOf gᵢ` and coprimality is inherited by divisors.
* **The class formula** is the image under `φ` of the `N`-conjugacy: `φ` preserves conjugacy
  (`MonoidHom.map_isConj`), and `φ (gᵢ ^ k) = baseᵢ ^ k`, so `φ (e · gᵢ · e⁻¹)` is `G`-conjugate to
  `baseᵢ ^ k`, i.e. equal in `ConjClasses G`.

This isolates the genuinely geometric input (`cyclo_conj`) from its group-theoretic consequence. -/
def TameInertiaData.toGeometricInertiaData {G : Type} [Group G] [Finite G]
    {cert : RigidData G} {E : Type} [Group E] {N : Subgroup E} [N.Normal] {φ : N →* G}
    {base : Fin cert.r → G} {hbase : base ∈ rigidTuples cert.C}
    (t : TameInertiaData N φ base hbase) : GeometricInertiaData N φ base hbase where
  gen := t.gen
  gen_top := t.gen_top
  gen_prod := t.gen_prod
  φ_gen := t.φ_gen
  branchCycle := by
    intro e
    obtain ⟨k, hcop, hconj⟩ := t.cyclo_conj e
    refine ⟨k, fun i => ?_, fun i => ?_⟩
    · -- coprimality: `orderOf baseᵢ ∣ orderOf gᵢ`, so coprime to `k` is inherited.
      have hdvd : orderOf (base i) ∣ orderOf (t.gen i) := by
        rw [← t.φ_gen i]
        exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])
      exact (hcop i).coprime_dvd_right hdvd
    · -- class formula: push the `N`-conjugacy through `φ`.
      have hmap : IsConj (φ (Rigidity.RET.conjN N e (t.gen i))) (φ ((t.gen i) ^ k)) :=
        φ.map_isConj (hconj i)
      rw [map_pow, t.φ_gen i] at hmap
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr hmap

end Rigidity.RET
