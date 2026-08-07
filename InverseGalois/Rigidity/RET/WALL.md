# The wall: what is left unproven, stated as narrowly as it can be

This note is the *measurement* of the transcendental input of the rigidity tree.  It records, as
precisely as the Lean statements allow, what is still assumed, why it cannot be proven with the
material at hand, and exactly which reductions to it are already proven.

Everything here is stated as an honest `sorry`.  There are no axioms in this development and there
never will be: a `sorry` announces "not done"; an axiom would announce "done" while being a lie.

---

## 1. The one open statement

| # | statement | file | shape |
|---|-----------|------|-------|
| **W1** | `Rigidity.RET.geomRET` | `RET/GeomRET.lean` | covers of the line over `ℚ̄` with branch locus in a prescribed set of points *are* the finite quotients of the sphere group, in both directions |

`#print axioms Rigidity.rigidity_realizable` is `[propext, sorryAx, Classical.choice, Quot.sound]`;
`sorryAx` enters through **W1** and nowhere else.  Every other result in the tree — several hundred
lemmas — is `[propext, Classical.choice, Quot.sound]`.

The second wall, **W2** (`classInertiaPlaceData_exists`, the branch cycles of the *descended*
`ℚ(T)`-model, as inertia at places over rational points), was the arithmetic half of the climb.  It
is now a theorem, derived from W1 by the ladder of §3.3; §3 records how.  What remains is purely
transcendental.

---

## 2. W1 — the branch-cycle correspondence over `ℚ̄`

```lean
structure GeomRET {r : ℕ} (t : Fin r → k) : Prop where
  exists_cover : ∀ {H : Type} [Group H] [Finite H] (h : Fin r → H),
      (List.ofFn h).prod = 1 → Subgroup.closure (Set.range h) = ⊤ →
      ∃ (L : LineCover) (e : L.deck ≃* H),
        L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
        ∀ i, L.IsInertiaGenAt (t i) (e.symm (h i))
  exists_cycles : ∀ L : LineCover, L.IsUnramifiedOutside (Set.range t) →
      L.IsUnramifiedAtInfinity → ∃ g : Fin r → L.deck, L.IsBranchCycleGenSystem t g

theorem geomRET {r : ℕ} (t : Fin r → k) (ht : Function.Injective t) : GeomRET t
```

`LineCover` is a finite Galois extension `M / ℚ̄(T)` carried with its integral model `ℚ̄[X] ⊆ M`;
`IsInertiaAt t σ` says `σ` lies in the inertia group of a place of `M` over the place `X - t`, and
`IsInertiaGenAt t σ` — the distinguished form both clauses use — says `σ` *generates* that inertia
group;
`IsUnramifiedOutside S` says no point outside `S` carries non-trivial inertia; and
`IsUnramifiedAtInfinity` says the same at the point at infinity, expressed by twisting the cover
along the coordinate change `T ↦ T⁻¹` (`RET/Twist.lean`) and looking at the point `0`.

**Why this shape.**  A surjection `Γ_r ↠ H` from the sphere group *is* a generating product-one
tuple (`prod_apply_sphereGroup_of`, `closure_range_apply_sphereGroup_of`), and `Γ_r` is `π₁` of the
`r`-punctured sphere.  So W1 says: *finite covers of the sphere minus `r` points are the finite
quotients of its `π₁`, algebraically — the topological cover of a monodromy representation is
algebraic with matching inertia (`exists_cover`), and every algebraic cover with that branch locus
comes from a monodromy representation (`exists_cycles`).*  The two hypotheses on the tuple are not
decoration: they are exactly the relations satisfied by the loops, and a tuple violating either is
not the branch-cycle system of any cover.

**Why both clauses.**  `exists_cover` is what realizes a group as a Galois group over `ℚ̄(T)`;
`exists_cycles` is what the *descent* needs, because the `ℚ(T)`-Galois closure of a cover built by
`exists_cover` is a strictly bigger cover whose branch cycles nobody has yet named (§3.2).  Neither
clause implies the other — they are the two directions of one equivalence of categories, and
splitting them would only hide that they are one theorem.  The unramifiedness clauses in
`exists_cover` are what makes `exists_cycles` applicable to the covers `exists_cover` produces, and
they are exactly what is true: a cover with monodromy `Γ_r ↠ H` is branched only over the `r`
punctures.  Without the clause at infinity `exists_cycles` would be *false* — the Kummer cover
`uⁿ = T` is unramified outside `{0}` on the affine line, and has no branch-cycle system over the
single point `0`, because it is ramified at infinity.

**Why it is irreducible here.**  The passage "topological cover ⇝ algebraic cover" is
Grauert–Remmert / GAGA (link **B** of `Pi1/GAGA_DREAM.md`); the passage `ℂ ⇝ ℚ̄` is the Lefschetz
principle (link **L**).  Neither analytification nor coherent-sheaf GAGA exists in Mathlib, and both
are far out of reach of a from-scratch build.

**What *is* proven, above and around W1:**

* the topological half — `π₁(ℂ ∖ S) ≅ FreeGroup (Fin |S|) ≅ Γ_{|S|+1}` — is proven from scratch
  (`RET/Pi1/Topological/`, Seifert–van Kampen included), sorry-free, for *all* `r`;
* `lineCover_exists_of_branchCycles`, `exists_branchCycleSystem`,
  `exists_lineCover_isBranchCycleSystem` (the packaged forms, generation and product-one included)
  and `riemann_existence_cover_mpr` are all *derived* from W1;
* whole families of covers are built **without** W1 at all — every finite abelian group
  (`RET/KummerAbelian.lean`), `Aₙ` and `Sₙ` for every `n` (`RET/SerreCovers.lean`), every dihedral
  group `Dₙ` (`RET/DihedralCover.lean`, by Artin's fixed-field theorem applied to the substitutions
  `u ↦ ζⁱ·u` and `u ↦ ζⁱ·u⁻¹`), every group with a branch datum of rank `r ≤ 2`
  (`RET/ExistenceLowRank.lean`), and anything obtained from these by
  quotients.  These are the classical explicit-polynomial cases; W1 is what covers the rest.

**Reachable sharpenings (partly done).**  The `r ≤ 2` case of `exists_cover` *with* the inertia
clause should follow from the two-point Kummer cover `wⁿ = (T - t₀)(T - t₁)^{n-1}`, and its local
theory is now in place, unconditionally and sorry-free, in `RET/KummerInertia.lean`:

* `irreducible_kummerA` — the Kummer equation is irreducible over `ℚ̄(T)` (Eisenstein at `X - t₀`
  plus Gauss), so the cover is connected of degree `n` with cyclic deck group;
* `isUnramifiedOutside_kummerCover` — unramified away from `{t₀, t₁}`: an inertia element scales
  the Kummer root by a *constant* root of unity, and a nontrivial constant is a unit, hence outside
  every place;
* `geomInertia_eq_top_kummerCover` and `geomInertia_eq_top_kummerCover'` — **total** ramification at
  `t₀` and at `t₁`: the ideal identity `(w)ⁿ = (X - t₀)(X - t₁)^{n-1}` bounds the ramification index
  below by `n` at `t₀`, and the mirrored root `w₁ = (X - t₀)(X - t₁)/w`, which satisfies
  `w₁ⁿ = (X - t₁)(X - t₀)^{n-1}`, does the same at `t₁`; `Ideal.card_inertia_eq_ramificationIdxIn`
  then makes the inertia group the whole deck group;
* `isInertiaGenAt_kummerCover`, `isInertiaGenAt_kummerCover'` — hence any generator of the deck
  group is a *distinguished* inertia element at either point, and
  `exists_zpowers_eq_top_kummerCover` produces one.

The pieces for the point at infinity are half-built in the same file.  The datum has degree `n`,
so in the coordinate `S = T⁻¹` the element `u = w·S` satisfies `uⁿ = (1 - t₀S)(1 - t₁S)^{n-1}`,
which is a unit at `S = 0`; `revKummerA` is that polynomial, `revKummerA_eval_zero` says it is `1`
at the origin, and `invSubst_revKummerA` is the identity
`revKummerA(T⁻¹) · Tⁿ = kummerA(T)` in `ℚ̄(T)`; `twistRoot` is the element `u = w·T⁻¹` of
`Twist invSubst Ω` and `twistRoot_pow` is its equation `uⁿ = revKummerA`.  What remains is to run
the constant-scaling argument inside the inversion twist: show that `u` generates
`Twist invSubst Ω` over `ℚ̄(S)` (whose degree is `n` by `twist_finrank`), conclude
`IsSplittingField (RatFunc k) (Twist invSubst Ω) (Xⁿ - C revKummerA)` by
`isSplittingField_of_root_of_adjoin_eq_top`, and apply `kummer_inertia_eq_one` at a place over
`S = 0`.  After that, the `r ≤ 2` clause needs only the assembly of a `LineCover` carrying the
splitting-field instance together with `deck ≃* H` for a two-element product-one generating tuple
(such an `H` is cyclic, generated by `h₀`, with `h₁ = h₀⁻¹`, and both generators are distinguished
inertia elements by the two theorems above).  Nothing similar is in reach for `exists_cycles`.

---

## 3. W2 — branch cycles of the descended model (**closed**)

```lean
theorem classInertiaPlaceData_exists {G : Type} [Group G] [Finite G]
    (cert : RigidityCertificate G) :
    ∃ m : ArithmeticModel G, Nonempty (ClassInertiaPlaceData cert m)
```

This is now **derived from W1**, by the ladder recorded in §3.3 below; it costs no assumption of its
own.  The route is `geomCompositum_branchCycles_exists` (`RET/Descent/BranchCycles.lean`) followed by
`classInertiaPlaceData_of_branchCycles` (`RET/Descent/Tower.lean`), the latter being sorry-free:
`#print axioms classInertiaPlaceData_of_branchCycles` is `[propext, Classical.choice, Quot.sound]`.

`ClassInertiaPlaceData` asks for inertia generators `gᵢ` of the **geometric** group
`N = Gal(Ω / k₀(T))` of a finite Galois `ℚ(T)`-model `Ω`, at places of `ℚ[X] ⊆ Aring Ω` lying over
the *rational* places `X - branchᵢ`, generating `N`, with product one, and with `φ (gᵢ)` in the
`i`-th prescribed class `Cᵢ`.

The certificate's chosen tuple `base` does **not** occur in the statement: the on-the-nose form
`inertiaPlaceData_exists`, with `φ (gᵢ) = baseᵢ`, is *derived* from it (rung 6a below).  That is the
right cut, because which of the `|G|` conjugate tuples a cover realizes is not something geometry
controls — it is what rigidity is for.

### 3.1 What is proven above it

* `arithmeticModel_exists` — the model `Ω` itself, from any geometric cover, is **proven**
  (`Descent/ModelDescent.lean`: primitive element, `ℚ(T)`-minimal polynomial, splitting field, and
  the regularity comparison `Kfr ⊓ Lfr = k₀(T)` via `regularity_inf_of_embedding`).
* `InertiaPlaceData.place_max`, `place_ne_bot`, `place_trans` — maximality, non-vanishing and
  `N`-transitivity on the places over a branch point are **derived**, not assumed.
* `InertiaPlaceData.toInertiaRootData` — Fried's branch-cycle formula (the cyclotomic conjugation
  `e gᵢ e⁻¹ ∼_N gᵢ^{χ(e)}`) is **derived** from tame ramification in residue characteristic zero.
* Everything from `InertiaRootData` up to `rigidity_realizable` is proven.

### 3.2 The genuine extra content, and why it is not just `exists_cover`

The descent produces `N` as the geometric group of the **arithmetic Galois closure**
`Ω̄ = Ω·ℚ̄(T)`, which strictly contains the cover `L` that `exists_cover` built.  `φ : N ↠ G` is the
restriction `Gal(Ω̄/ℚ̄(T)) ↠ Gal(L/ℚ̄(T)) ≃ G`.  So the generators demanded by `InertiaPlaceData`
live in `N`, not in `G`, and must *lift* the branch cycles of `L`.  That is what `exists_cycles`
(§2) is for: applied to `Ω̄`, it produces branch cycles of `N` over the same rational points.

### 3.3 The ladder from W1 to W2

Each rung below is ordinary algebra — no analysis.  This was the climb; it is finished.  Status as
of 2026-08-06: **all rungs done**.

1. ✅ **Sub-cover packaging** (`RET/SubCover.lean`).  A normal `IntermediateField (ℚ̄(T)) M` is again
   a `LineCover` (`LineCover.sub`), the restriction map is `LineCover.subHom`, and inertia and whole
   branch-cycle systems restrict along it (`IsInertiaAt.restrict`, `IsBranchCycleSystem.restrict`).
2. ✅ **Transport** (`RET/SubCover.lean`).  `IsInertiaAt`, `IsBranchCycleSystem` and
   `IsUnramifiedOutside` are preserved by an isomorphism of covers — needed to move W1's abstract
   `L` onto the concrete `Limg ⊆ Ω̄` produced by the descent.
3. **Unramifiedness of the closure.**  `Ω̄` is generated over `ℚ̄(T)` by the `ℚ(T)`-conjugates of a
   primitive element of `L`; each conjugate field is `a(L)` for `a` fixing `ℚ(T)`, and `a` fixes
   every *rational* point `X - branchᵢ`.  Hence `Ω̄` is unramified outside the same rational points
   — the reason the branch points must be taken rational.
   * ✅ 3a, the compositum half (`RET/Unramified.lean`): a cover generated by normal subcovers each
     unramified outside `S` is unramified outside `S` (`IsUnramifiedOutside.of_iSup`).
   * ✅ 3b, the semilinear half (`RET/Semilinear.lean`).  A `ℚ(T)`-automorphism of `Ω̄` is not
     `ℚ̄(T)`-linear — it moves the constants — so it is an isomorphism of covers only *semilinearly*,
     over a coordinate change `φ` of the base.  `LineCover.SemiIso L L' φ` is that notion.  As soon
     as `φ` preserves the integral model (`PolyPreserving φ ψ`) it carries the model along
     (`SemiIso.bring`), places to places over the moved point (`SemiIso.liesOver_map`), maximal to
     maximal (`SemiIso.isMaximal_map`), deck group to deck group (`SemiIso.deckEquiv`) and inertia
     to inertia (`IsInertiaAt.semiIso`); unramifiedness follows for any set of points stable under
     the move (`IsUnramifiedOutside.semiIso`), and at infinity for a coordinate change commuting
     with the inversion (`SemiIso.twist`, `IsUnramifiedAtInfinity.semiIso`).  For the coordinate
     change induced by an automorphism `c` of the constants (`constSubst c`) the moved point is
     `c t`, so every **rational** point is fixed: `IsUnramifiedOutside.semiIso_const` and
     `IsUnramifiedAtInfinity.semiIso_const`.  This is exactly why the branch points must be
     rational.
   * ✅ 3c, the coordinate change is a constant substitution (`RET/Semilinear.lean`,
     `eq_constSubst`).  There is no other possibility: an automorphism of `ℚ̄(T)` fixing `T`
     moves the constants among themselves — every constant is algebraic over `ℚ`, every ring map
     fixes `ℚ`, and an element of `ℚ̄(T)` algebraic over `ℚ̄` is a constant — and is determined by
     what it does to them (`constEquiv`, `ratFunc_ringHom_ext`).  So the semilinearity of *any*
     `ℚ(T)`-automorphism of `Ω̄` is of the harmless kind 3b handles.
   * ✅ 3d, the conjugates of a subcover (`RET/SemilinearSub.lean`).  The conjugate field itself:
     a semilinear isomorphism carries an intermediate field to an intermediate field
     (`SemiIso.mapField`, `SemiIso.mem_mapField`), a normal one to a normal one
     (`SemiIso.normal_mapField`), and restricts to a semilinear isomorphism of the two subcovers
     (`SemiIso.fieldEquiv`, `SemiIso.restrict`).  Combined with 3b: a conjugate `a(L)` of a
     subcover unramified outside a set of rational points, and at infinity, is unramified there
     too (`IsUnramifiedOutside.semiIso_mapField`, `IsUnramifiedAtInfinity.semiIso_mapField`).
     With 3a and 4b — the compositum of the conjugates is `Ω̄` — this bounds the branch locus of
     the arithmetic Galois closure: `IsUnramifiedOutside.of_conjugates`,
     `IsUnramifiedAtInfinity.of_conjugates`, the whole of rung 3 in one statement.
   * ✅ 3e, where the conjugating maps come from (`RET/SemilinearSub.lean`,
     `SemiIso.ofBasePreserving`).  An automorphism of `Ω̄` over `ℚ(T)` does not fix `ℚ̄(T)`
     pointwise, but it does carry it onto itself; that alone produces the coordinate change
     (`SemiIso.baseHom`, `SemiIso.baseEquiv`) and hence the semilinear isomorphism 3b–3d consume.
     By 3c the coordinate change is a constant substitution, so 3b–3d apply.  Semilinear
     isomorphisms compose (`SemiIso.refl`, `SemiIso.trans`, `constSubst_refl`,
     `constSubst_trans`), and taking images is a Galois connection between the two lattices of
     intermediate fields, compatible with generation (`SemiIso.mapField_le_iff`,
     `SemiIso.mapField_adjoin`) — so a conjugate of `K(x)` is `K(σ x)`, as it should be.
4. **Infinity.**
   * ✅ 4a (`RET/Twist.lean`): the coordinate change.  `Twist φ M` is `M` with `ℚ̄(T)` acting through
     an automorphism `φ` of the base; it is again a finite Galois extension with the *same* deck
     group (`Twist.autEquiv`), so a cover twists to a cover (`LineCover.twist`).  With the inversion
     `invSubst : T ↦ T⁻¹` this defines `IsUnramifiedAtInfinity`.
   * ✅ 4b (`RET/Infinity.lean`): the twist of a subcover is a subcover of the twist.  Twisting does
     not move the lattice of intermediate fields (`Twist.subFieldOrderIso`), so the compositum lemma
     3a carries over verbatim to infinity (`IsUnramifiedAtInfinity.of_iSup`), as does transport
     along an isomorphism (`IsUnramifiedAtInfinity.transport`).
5. ✅ **Geometric ↦ arithmetic inertia** (`RET/Descent/GeomArithBridge.lean`).  An element of inertia
   at a place `Q` of `ℚ̄[X] ⊆ Ω̄` restricts to an element of inertia at `Q ∩ Aring Ω`, a place of
   `ℚ[X] ⊆ Ω` over the same rational point.
6. **Assembly.**
   * ✅ 6a, the match against the certificate's tuple (`RET/Descent/Matching.lean`, and
     `inertiaPlaceData_exists` in `RET/Descent/Tower.lean`).  A tuple of branch cycles whose images
     lie in the prescribed classes, generates and has product one *is* a rigid tuple
     (`Rigidity.comp_mem_rigidTuples`); rigidity — a single conjugation orbit, by
     `rigid_card_iff_single_orbit` — then carries it onto `base`
     (`Rigidity.exists_conj_comp_eq`), and the conjugation is absorbed into the monodromy
     (`ArithmeticModel.conj`), which changes nothing else in the tower.  This is why W2 can be, and
     now is, stated without `base`.  A companion lemma
     (`IsRationalClass.mk_eq_of_zpowers_eq`) removes the other ambiguity of a branch cycle: a
     rational class does not see which generator of the cyclic inertia group was chosen.
   * ✅ 6b, the geometric assembly, in two halves.
     * **Geometry** (`RET/Descent/BranchCycles.lean`, `geomCompositum_branchCycles_exists`).  Take
       the branch points to be the rational integers `0, 1, …, r-1`; `exists_cover` builds a cover
       `L` with the certificate's monodromy, `geomCompositum_exists_of_cover_unramified` (rungs 3, 4)
       builds the arithmetic compositum `Ω̄ = Ω · ℚ̄(T)` with the same branch locus, and
       `exists_cycles` reads branch cycles `g` off `Ω̄`.  Their classes are identified with the
       certificate's by restriction to the subcover `L` (rung 1) plus inertia conjugacy
       (`IsInertiaGenAt.exists_conj`), rationality (`IsRationalClass.mk_eq_of_zpowers_eq`, rung 6a)
       absorbing the choice of generator of the cyclic inertia group.
     * **Arithmetic packaging** (`RET/Descent/Tower.lean`,
       `classInertiaPlaceData_of_branchCycles`).  The `ℚ(T)`-model is the *enlarged* one,
       `Ω(ζ_N)` with `N = |Gal(Ω̄/ℚ̄(T))|` (`RET/Descent/ModelEnlarge.lean`): adjoining the `N`-th
       roots of unity keeps `Ω(ζ_N)/ℚ(T)` Galois and keeps `Ω̄` its compositum with `ℚ̄(T)`, while
       supplying the primitive root of unity through which the tame inertia is read — and `N` is
       divisible by every ramification index because each branch cycle lies in `Gal(Ω̄/ℚ̄(T))`.  The
       comparison `compareOfEmbedding` identifies the geometric group of the model with
       `Gal(Ω̄/ℚ̄(T))`, transporting the branch cycles; rung 5 pushes the places down.  Then
       `place_trans`, `place_max` and `toInertiaRootData`, already proven, finish.

---

## 4. Summary

The transcendental content of the whole development is one sentence: *finite covers of the sphere
minus `r` points are the finite quotients of its fundamental group, algebraically, with tame inertia
at the punctures matching the loops.*  W1 is that sentence, stated in exactly those terms and in
both directions.  It is the only thing the rigidity tree still assumes.

Everything else is a theorem.  The arithmetic half — the branch-cycle rationality descent from
`ℚ̄(T)` to `ℚ(T)`, the whole of §3 — is proven from W1, rung by rung: the branch locus of the
arithmetic Galois closure is bounded (rungs 3, 4), its branch cycles are read off by `exists_cycles`
(rung 1), pushed down to arithmetic inertia (rung 5), given a model carrying the right roots of
unity (rung 6b), and matched against the certificate by rigidity (rung 6a).  From there Fried's
branch-cycle formula, the centerless extension lemma and Hilbert irreducibility — all already
proven — give `rigidity_realizable`.

So the statement of the whole development is now: *the Riemann Existence Theorem over `ℚ̄` implies
the rigidity criterion for the Inverse Galois Problem*, formalized, with the implication itself
carrying no assumption.  Closing W1 needs analytification and coherent-sheaf GAGA (§2); that is the
remaining work, and it is of a different kind from everything above.
