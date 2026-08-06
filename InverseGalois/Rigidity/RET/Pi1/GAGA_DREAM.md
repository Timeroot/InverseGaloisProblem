# The GAGA / Riemann Existence dream: proving `riemann_existence_cover`

This document sketches the full decomposition of the sole transcendental floor of the IGP
rigidity tree — `riemann_existence_cover` (equivalently `inertiaRootData_exists`) — into a chain
of named theorems, and audits each link against Mathlib v4.28.0 (the toolchain this repo pins).
It is the "dream": what we would prove if we weren't afraid, laid out so it can be filled in
piece by piece.

## The statement we must prove

```
riemann_existence_cover {G} [Group G] [Finite G] :
    IsGeometricGaloisCover G ↔ ∃ (r : ℕ) (φ : SphereGroup r →* G), Function.Surjective φ
```

where `IsGeometricGaloisCover G := ∃ finite Galois L/ℚ̄(T) with (L ≃ₐ[ℚ̄(T)] L) ≃* G`, and
`SphereGroup r = ⟨x₀,…,x_{r-1} | ∏ xᵢ = 1⟩`.

The `←` direction (a product-one generating tuple realizes `G` as a geometric Galois group) is the
true content. The heart of it is the **comparison isomorphism**

```
    π₁^ét(ℙ¹_ℚ̄ ∖ S)  ≅  sphereCompletion (|S|-1)          (RET, "the dream")
```

between the algebraic (étale) fundamental group of the projective line minus `|S|` points and the
profinite completion of the topological fundamental group of the `|S|`-punctured sphere. There is
no purely algebraic proof: it *is* the comparison of the algebraic and complex-analytic worlds.
This is the Riemann Existence Theorem (Grauert–Remmert form).

## The standard ℂ-analytic decomposition

Write `S ⊂ ℙ¹_ℚ̄` finite, `r = |S|`, `U = ℙ¹ ∖ S`. The classical proof chain:

| Link | Statement | Nature |
|------|-----------|--------|
| **A** | `Gal(M_S / ℚ̄(T)) ≅ π₁^ét(U)` — max. extension unramified outside `S` ↔ étale π₁ | algebraic (Grothendieck–Galois) |
| **B** | `π₁^ét(U_ℂ) ≅ profiniteCompletion (π₁^top(U^an))` — GAGA comparison | **transcendental floor** |
| **L** | `π₁^ét(U_ℚ̄) ≅ π₁^ét(U_ℂ)` — base change along ℚ̄ ↪ ℂ (Lefschetz principle) | algebraic (spreading out) |
| **C** | `π₁^top(S² ∖ r pts) ≅ SphereGroup r` (finite quotients) — van Kampen | topological |
| **D** | `profiniteCompletion (SphereGroup r) = sphereCompletion r` | definitional / trivial |

Composing A∘L∘B∘C∘D gives the comparison isomorphism, hence `riemann_existence_cover`.

## Status of each link vs the existing repo build

* **A** — DONE in spirit. The repo's `Pi1/Etale/` develops `(FiniteEtaleAlgCat K)ᵒᵖ` as a Galois
  category with `Aut(fibreFunctor) ≅ G_K`, and the categorical FTGT
  (`etaleEquivContActionAut`). What remains for a *geometric* π₁ over ℚ̄(T) is the specialization
  of this abstract machinery to the function field `ℚ̄(T)` and its unramified-outside-`S`
  extensions. Substantial but on rails — no new mathematics, only wiring.
* **D** — DONE. `sphereCompletion r := profiniteCompletion.obj (GrpCat.of (SphereGroup r))`, and
  `sphereIsFundamentalGroup` / `sphereCompletion_mulEquiv_aut` are proven sorry-free
  (`Pi1/SphereCompletion.lean`, `Pi1/FundamentalGroup.lean`).
* **C** — **DONE, for every `r`.** `Pi1/Topological/VanKampen/` proves Seifert–van Kampen from
  scratch (`coprodMulEquivPi1`), and `Pi1/Topological/PuncturedPlane.lean` runs the induction that
  computes `π₁(ℂ ∖ S) ≅ FreeGroup (Fin |S|) ≅ Γ_{|S|+1}` for an arbitrary finite `S ⊂ ℂ`
  (`pi1_compl_mulEquiv_sphereGroup`). Sorry-free and axiom-free.
* **L** — HARD but algebraic. Needs base change of étale fundamental groups; no analysis. A
  medium-term target once A is specialized.
* **B** — THE WALL. This is GAGA proper: analytification of schemes, comparison of coherent
  sheaves / finite étale covers between the algebraic and analytic categories. Essentially absent
  from Mathlib and a multi-year formalization in its own right. Every other link is a genuine
  reduction; this one is irreducible with current tools.

## Mathlib audit (v4.28.0, CORRECTED)

An earlier survey read a stale Mathlib copy and undercounted. The truth:

### Present — the topological toolkit is richer than expected
* `Mathlib/Topology/Homotopy/Lifting.lean` (Junyan Xu, 2025) — the full covering-space lifting
  package:
  * `IsCoveringMap.exists_path_lifts`, `.liftPath`, `.liftPath_trans` — **path lifting**.
  * `IsCoveringMap.liftHomotopy`, `.monodromy_theorem` — **homotopy lifting**.
  * `IsCoveringMap.monodromy` (fiber over `x` → fiber over `y`, homotopy-class dependent),
    `monodromy_refl`, `monodromy_trans_apply`, `monodromy_bijective`, and the packaged
    `monodromyFunctor : FundamentalGroupoid X ⥤ Type` — **the covering→π₁-action dictionary**.
  * `IsCoveringMap.existsUnique_continuousMap_lifts` — the simply-connected lifting criterion.
* `Mathlib/Analysis/Complex/CoveringMap.lean` — `isCoveringMap_exp` (`exp : ℂ → ℂ∖0` is a covering
  map, total space contractible), `isCoveringMap_npow`/`zpow` (`z ↦ zⁿ` on `𝕜∖0`), and the
  quotient-covering forms. These *are* the cyclic covers of `ℙ¹ ∖ {0,∞}`.
* `Mathlib/AlgebraicTopology/FundamentalGroupoid/` — `FundamentalGroup`, the groupoid, and
  `SimplyConnected.lean` with `SimplyConnectedSpace.ofContractible`, the
  `Subsingleton (Path.Homotopic.Quotient x y)` characterization, and `→ PathConnectedSpace`.
* Grothendieck–Galois categories, profinite groups/completion, function-field ramification —
  all present and used by the existing repo build.

### Absent — must be built or remain floors
* **GAGA / analytification / Riemann surfaces** (link **B**). The wall.
* ~~**Seifert–van Kampen**~~ — was absent (Mathlib's `Limits/VanKampen.lean` is the categorical
  notion, not the π₁ computation); now **built from scratch** in `Pi1/Topological/VanKampen/`.
* ~~**π₁(S¹) ≅ ℤ**~~ — was absent; now proven as `Complex.fundamentalGroupUnitsExp`.
* **Base change of étale π₁** (link **L**).

## What this workstream builds (the reachable frontier)

Everything except **B** is, in principle, reachable. The topological toolkit — the reusable engine
for link **C** — rests entirely on the confirmed `Lifting.lean` monodromy machinery and the
`exp`/`zⁿ` covering maps. **Landed and in the green build** (all sorry-free and axiom-free beyond
`propext`/`Choice`/`Quot.sound`):

1. `Pi1/Topological/Monodromy.lean`
   * `IsCoveringMap.monodromyHom : FundamentalGroup X x →* Equiv.Perm (p ⁻¹' {x})` — the monodromy
     as a genuine group homomorphism (packaging `monodromyFunctor` on the automorphism group).
   * `IsCoveringMap.orbitMap x e₀ : FundamentalGroup X x → p ⁻¹' {x}`, `γ ↦ monodromy γ e₀`, with
     `orbitMap_surjective` (path-connected total space) and `orbitMap_injective` (simply connected),
     packaged as `orbitEquiv : FundamentalGroup X x ≃ p ⁻¹' {x}` — the classification of the fibre
     of a universal cover by π₁.
   * `monodromy_comp_deck` — monodromy is equivariant under any continuous fibrewise self-map over
     the identity (a deck transformation); the crux upgrading the set bijection to a group iso.
2. `Pi1/Topological/QuotientPi1.lean`
   * `IsQuotientCoveringMap.fundamentalGroupMulEquiv : FundamentalGroup X (f e₀) ≃* G` — for a free,
     properly discontinuous quotient covering `f : E → X` by a group `G` with `E` simply connected
     and path connected, **π₁(X) is the deck group `G`**.  This is link **C** in its cleanest form
     (universal cover presented as a quotient).  Plus the additive twin
     `IsAddQuotientCoveringMap.fundamentalGroupMulEquiv : ... ≃* Multiplicative A`.
3. `Pi1/Topological/CircleGroup.lean`
   * `Complex.fundamentalGroupUnitsExp : π₁(ℂ ∖ 0) ≃* Multiplicative ℤ` via `isAddQuotientCoveringMap_exp`
     (contractible, hence simply connected, total space `ℂ`; deck group `2πiℤ ≅ ℤ`) — the base case
     of C and the first concrete π₁ computation, realizing `ℤ = π₁` of the once-punctured line.
4. `Pi1/Topological/TameCover.lean`
   * The degree-`n` power cover `z ↦ zⁿ` on `ℂˣ` — the topological model of **tame ramification**.
     `npowCover : IsCoveringMap (z ↦ zⁿ)`; `npow_orbitMap_surjective` (monodromy acts transitively:
     tame inertia is transitive on the fibre); `npow_fibre_card` (each fibre is a `μₙ`-torsor of
     size `n`, so the cyclic tame monodromy has order `n`).
5. `Pi1/Topological/Transport.lean`
   * **Homotopy invariance of `π₁`**: `ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv` — a
     homotopy equivalence `X ≃ₕ Y` induces `FundamentalGroup X x ≃* FundamentalGroup Y (e x)` (the
     `mulEquivEnd` of the fully faithful functor of `equivOfHomotopyEquiv`), with the homeomorphism
     specialization `Homeomorph.fundamentalGroupMulEquiv`.  Lets a `π₁` computation move between
     homotopy-equivalent spaces (e.g. subtype `{z ≠ 0}` ↔ `ℂˣ`, or later plane ↔ wedge of circles).
   * **The product formula** `FundamentalGroup.prodMulEquiv : π₁(X × Y, (x,y)) ≃* π₁(X,x) × π₁(Y,y)`
     (from `FundamentalGroupoidFunctor.prodIso` pushed through `Grpd.forgetToCat` + `Cat.equivOfIso`,
     plus `End.prodMulEquiv` splitting endomorphisms in a product category) — the second functorial
     pillar of the `π₁` toolkit alongside homotopy invariance.  Fills a Mathlib gap (only the
     groupoid-level `prodIso` existed, not the group iso at a basepoint).  The **arbitrary-arity**
     generalization `FundamentalGroup.piMulEquiv : π₁(∀ i, Xᵢ, x) ≃* ∀ i, π₁(Xᵢ, xᵢ)` (from `piIso`
     + `End.piMulEquiv`) computes the `π₁` of any finite power — e.g. the `r`-torus.
6. `Pi1/Topological/TameMonodromy.lean`
   * `Complex.npowMonodromyInt : Multiplicative ℤ →* Perm ((z ↦ zⁿ) ⁻¹' {e₀ⁿ})` — the tame
     monodromy as the action of `π₁(ℂˣ) ≅ ℤ` on the fibre; `npow_tame_monodromy` bundles that this
     `ℤ`-action is **transitive** on the fibre of **`n` points**, i.e. the generator is an `n`-cycle
     — the cyclic reduction `ℤ ↠ ℤ/n ≅ μₙ` of tame inertia.
7. `Pi1/Topological/SphereBaseCase.lean`
   * `freeGroupFin1MulEquivInt : FreeGroup (Fin 1) ≃* Multiplicative ℤ`;
     `sphereGroup_two_mulEquiv_int : SphereGroup 2 ≃* Multiplicative ℤ` (`Γ_2 ≅ ℤ`); and the
     **link-C base case `r = 2`** `pi1_units_mulEquiv_sphereGroup_two : FundamentalGroup ℂˣ _ ≃*
     SphereGroup 2` — the Riemann Existence comparison `π₁^top(S² ∖ r pts) ≅ Γ_r` for two branch
     points, both sides infinite cyclic.
   * The **degenerate rung `r ≤ 1`**: `sphereGroup_one_subsingleton`, `sphereGroup_zero_subsingleton`
     (`Γ_1`, `Γ_0` are trivial), the topological `Complex.fundamentalGroup_subsingleton` (`π₁(ℂ) = 1`,
     the plane being contractible), and the comparison `pi1_plane_mulEquiv_sphereGroup_one :
     FundamentalGroup ℂ _ ≃* SphereGroup 1` — the `r = 1` instance (sphere minus one point = plane),
     both sides trivial.  Together with `r = 2` this closes every branch count `r ≤ 2` unconditionally.
   * The **base-case `←` realization** `sphereGroup_two_monodromy_transitive` — transporting the
     degree-`n` tame monodromy across `Γ_2 ≅ ℤ`, the sphere group `Γ_2` acts transitively on the
     `n`-point fibre of `z ↦ zⁿ`, i.e. the cyclic group `ℤ/n` is realized as the monodromy (deck)
     group of a cover via a surjection `Γ_2 ↠ ℤ/n`.  This is the `r = 2`, cyclic-`G` instance of the
     Riemann Existence `←` direction — the first concrete realization of a finite group as monodromy.

8. `Pi1/Topological/Wedge.lean` — the **algebraic half of the wedge-of-circles model**.
   * `Monoid.CoprodI.congr` — the free product is functorial in its factors (a Mathlib gap);
     `freeGroupMulEquivCoprodInt : FreeGroup ι ≃* ⋆_{ι} ℤ` — a free group **is** the free product of
     copies of `ℤ` (the `π₁` of a wedge of circles / the punctured plane).
   * **`sphereGroup_mulEquiv_coprodInt : Γ_r ≅ ⋆_{r-1} ℤ`** and its display
     `sphereGroup_mulEquiv_coprod_pi1Units : Γ_r ≅ ⋆_{r-1} π₁(ℂˣ)` — the sphere group **is** the free
     product of `r - 1` copies of the local inertia group `ℤ ≅ π₁(ℂˣ)`, the algebraic shadow of
     "`r`-punctured sphere `≃ₕ` wedge of `r - 1` circles".
   * `sphereGroup_abelianization_addEquiv : H₁(Γ_r) ≅ ℤ^{r-1}` — the first homology of the punctured
     sphere (abelianized monodromy), via `abelianizationCongr` + `FreeAbelianGroup.equivFinsupp`.

Alongside these, the toolkit is exercised on the **torus**: `Complex.fundamentalGroupTorus :
FundamentalGroup (ℂˣ × ℂˣ) _ ≃* ℤ × ℤ` (`π₁(T²) = ℤ²`) and its arbitrary-arity form
`Complex.fundamentalGroupPowTorus : π₁((ℂˣ)^r) ≅ ℤ^r` (via the `Π`-product formula + `π₁(ℂˣ) ≅ ℤ`).

9. `Pi1/Topological/VanKampen/` — **Seifert–van Kampen, proven from scratch** (Mathlib has none).
   Subdivision of paths and of homotopy squares against an open cover (`Subdivision.lean`,
   `Subdivision2D.lean`), the induced-map bridge (`Bridge.lean`), generation of `π₁(X)` by the two
   pieces (`Generation.lean`), the compatible-pair lift (`Existence.lean`) and its uniqueness
   (`Uniqueness.lean`), assembled in `Group.lean` as
   `VanKampen.coprodMulEquivPi1 : π₁(U) ⋆ π₁(V) ≃* π₁(X)` for an open cover `U ∪ V = X` with
   `U ∩ V` simply connected and both pieces path connected.

10. `Pi1/Topological/PuncturedPlane.lean` — **link C, for every `r`.**
    `pi1_compl_finset : π₁(ℂ ∖ S) ≃* FreeGroup (Fin |S|)` for any `S : Finset ℂ`, and
    `pi1_compl_mulEquiv_sphereGroup : π₁(ℂ ∖ S) ≃* Γ_{|S|+1}` (the extra puncture being `∞`), by
    induction on `|S|`: rotate so the punctures have distinct real parts (`exists_re_injOn`), split
    off the rightmost one with two overlapping half-planes whose intersection is a convex strip,
    identify each half-plane with `ℂ` (`Complex.leftHalfPlaneHomeo`, `rightHalfPlaneHomeo`), and add
    ranks with van Kampen (`freeProduct_of_cover`, `pi1Free_of_split`).

11. `Pi1/Topological/Comparison.lean` — the payoff. `pi1ComplCompletionIso` (links **C** and **D**
    composed: `completion (π₁(ℂ ∖ S)) ≅ sphereCompletion (|S| + 1)`) and the covers correspondence
    restated with the honest topological object,
    `isGeometricGaloisCover_iff_pi1_compl(_completion)`, resting on the general finite-quotient
    dictionary `exists_surjective_completion_iff` of `Pi1/Completion.lean`.

## Unconditional realizations: the `←` direction for specific groups

Independently of the comparison chain, the conclusion `IsGeometricGaloisCover G` can sometimes be
established by exhibiting the extension of `ℚ̄(T)` outright. Everything in this section is proven,
sorry-free and axiom-free (`[propext, Classical.choice, Quot.sound]`), and none of it consumes the
Riemann Existence input:

* **Every finite abelian group** — `RET/KummerCover.lean` builds the Kummer cover `yⁿ = T`
  (`isGeometricGaloisCover_of_isCyclic`), and `RET/KummerAbelian.lean` assembles the cyclic pieces
  by duality (`isGeometricGaloisCover_of_commGroup`).
* **`Aₙ` and `Sₙ`, every `n`** — `RET/SerreCovers.lean`
  (`isGeometricGaloisCover_alternatingGroup`, `isGeometricGaloisCover_perm` for `n ≥ 3`, and the
  primed forms for every `n`, the small cases being cyclic). The geometric
  monodromy of Serre's explicit family, already computed in the Hilbert `Aₙ` tree, is transported
  to `ℚ̄(T)` along `IsGaloisGroupOver.of_ringEquiv`. These are the first nonabelian covers in the
  tree.
* **Every branch datum with at most two points** — `RET/ExistenceLowRank.lean`. `Γ_0` and `Γ_1` are
  trivial and `Γ_2 ≅ ℤ`, so a surjection `Γ_r ↠ G` with `r ≤ 2` has cyclic image and is realized by
  a Kummer cover (`isGeometricGaloisCover_of_sphereGroup_surjective_of_le_two`). This is the
  `r ≤ 2` case of `riemann_existence_cover_mpr`, proven. From `r = 3` on, `Γ_r` is free of rank
  `r - 1`, its finite quotients are all two-generated finite groups, and no explicit construction
  reaches them.
* **Artin's theorem as an engine** — `RET/ArtinFixedField.lean`. A faithful action of a finite `G`
  on a field `L` realizes `G` over the invariants (`isGaloisGroupOver_fixedPoints`), and
  `isGeometricGaloisCover_of_fixedPoints` reduces "`G` is a geometric cover" to producing a faithful
  `G`-action on some field whose invariant subfield is `ℚ̄(T)`. This is the shape every by-hand
  construction takes: e.g. the dihedral group acting on `ℚ̄(u)` by `u ↦ ζu`, `u ↦ u⁻¹`, whose
  invariants are `ℚ̄(uⁿ + u⁻ⁿ)`.
* **Substitutions of the parameter** — `RET/RatFuncSubst.lean`, the tooling that by-hand actions are
  written in. `ratFuncSubst g hg` is the `K`-algebra map `K(u) → K(u)` with `u ↦ g`, defined for `g`
  transcendental over `K`; `ratFunc_algHom_ext` says such a map is pinned by its value at `u`, so
  `ratFuncSubstEquiv` upgrades a pair of mutually inverse substitutions to an automorphism from two
  equations. The dihedral pair `u ↦ c·u` and `u ↦ u⁻¹` is licensed by
  `transcendental_const_mul_X` and `transcendental_inv_X`. What remains for the dihedral cover is
  the group action itself and the degree bound `[ℚ̄(u) : ℚ̄(uⁿ + u⁻ⁿ)] ≤ 2n` from `X²ⁿ - wXⁿ + 1`.
* **Closure under quotients** — `IsGeometricGaloisCover.of_surjective`
  (`Pi1/AbsoluteGaloisQuotient.lean`): pass to the fixed field of the kernel. Closure under
  *subgroups* is genuinely false for this predicate as stated over the line: the fixed field of a
  subgroup is the function field of a cover of `ℙ¹`, which generally has positive genus.

These are genuine, verified contributions independent of the GAGA wall. Link **C** is now **closed
for all `r`**: `π₁^top(S² ∖ r pts) ≅ Γ_r`, with the local `ℤ`-monodromies around the punctures glued
by the from-scratch Seifert–van Kampen theorem. Links **L** and **B** (GAGA — irreducible) are staged
behind it with honest markers.

## Honesty ledger

Nothing here introduces an axiom. Links not yet proven are carried as `sorry` on their honest
statements, never as axioms. `riemann_existence_cover_mpr` and `inertiaRootData_exists` are the two
honest `sorry`s of the tree; this workstream chips at the reductions beneath them. The GAGA wall
(**B**) is named plainly as the one irreducible-with-current-tools step, not hidden.

The `→` direction of `riemann_existence_cover` is no longer among them: `Γ_r ≅ FreeGroup (Fin (r-1))`
makes every finite group a quotient of some `Γ_r`, so `riemann_existence_cover_mp` is unconditional
(`exists_sphereGroup_surjective`) and the biconditional's whole content is its `←` direction. Of
that `←` direction, the branch counts `r ≤ 2` are proven outright, as are the abelian, `Aₙ` and
`Sₙ` cases for every `r`; what remains open is a general finite group with at least three branch
points.
