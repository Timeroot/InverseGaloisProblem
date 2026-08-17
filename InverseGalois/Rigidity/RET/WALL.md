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
| **W1** | `Rigidity.RET.geomRETExistence_of_injective` | `RET/GeomRET.lean` | a generating product-one tuple in a finite group is the tuple of branch cycles of a cover of the line over `ℚ̄`, branched over prescribed points |

`#print axioms Rigidity.rigidity_realizable` is `[propext, sorryAx, Classical.choice, Quot.sound]`;
`sorryAx` enters through **W1** and nowhere else.  Every other result in the tree — several hundred
lemmas — is `[propext, Classical.choice, Quot.sound]`.

**W1 is now one direction, not two.**  The correspondence has an existence half (build a cover out
of a tuple) and a completeness half (read branch cycles off a cover).  The completeness half is a
theorem — `geomRETCompleteness_of_injective`, `RET/Local/ProdOneGeneration.lean`, unconditional,
for every finite group and every number of branch points — proven by the analytic tower of
`RET/Analytic/` and the spider of `RET/Pi1/Topological/`; §2.4 records how.  What is open is only
the existence half, which is the half that genuinely needs Grauert–Remmert.  Over `ℂ` even that
half has been reduced to a single named property of coverings of the punctured plane —
`HasEnoughFunctions`, that each nontrivial deck transformation moves one holomorphic function of
moderate growth — everything else about it being proven; the subsection "The algebraization of a
covering, and the wall named once" records the reduction and what still separates it from W1.

The second wall, **W2** (`classInertiaPlaceData_exists`, the branch cycles of the *descended*
`ℚ(T)`-model, as inertia at places over rational points), was the arithmetic half of the climb.  It
is now a theorem, derived from the correspondence by the ladder of §3.3; §3 records how.  What
remains is purely transcendental.

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

-- open (this is W1):
theorem geomRETExistence_of_injective {r : ℕ} (t : Fin r → k) (ht : Function.Injective t) :
    GeomRETExistence t

-- a theorem (RET/Local/ProdOneGeneration.lean):
theorem geomRETCompleteness_of_injective {r : ℕ} {t : Fin r → k} (ht : Function.Injective t) :
    GeomRETCompleteness t

-- the two of them (RET/Completeness.lean):
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
clause implies the other — they are the two directions of one equivalence of categories.  They are
now of different status: `exists_cycles` is proven outright, `exists_cover` is W1.  The
unramifiedness clauses in
`exists_cover` are what makes `exists_cycles` applicable to the covers `exists_cover` produces, and
they are exactly what is true: a cover with monodromy `Γ_r ↠ H` is branched only over the `r`
punctures.  Without the clause at infinity `exists_cycles` would be *false* — the Kummer cover
`uⁿ = T` is unramified outside `{0}` on the affine line, and has no branch-cycle system over the
single point `0`, because it is ramified at infinity.

**Why it is irreducible here.**  The passage "topological cover ⇝ algebraic cover" is
Grauert–Remmert / GAGA (link **B** of `Pi1/GAGA_DREAM.md`).  It is needed in the existence
direction only: there one is *handed* a topological object and must produce a field.  In the
completeness direction the field is given, and the analytic tower of `RET/Analytic/` builds its
covering space out of the equation itself, which is why that direction could be closed from scratch
(§2.4).  Neither analytification nor coherent-sheaf GAGA exists in Mathlib, and both are far out of
reach of a from-scratch build.

**What *is* proven, above and around W1:**

* the topological half — `π₁(ℂ ∖ S) ≅ FreeGroup (Fin |S|) ≅ Γ_{|S|+1}` — is proven from scratch
  (`RET/Pi1/Topological/`, Seifert–van Kampen included), sorry-free, for *all* `r`;
* the whole completeness direction, `exists_cycles`, for every finite group and every number of
  branch points (`geomRETCompleteness_of_injective`, and its packaged forms
  `exists_branchCycleSystem`, `exists_branchCycleGenSystem` in `RET/Completeness.lean`) — see §2.4;
* `lineCover_exists_of_branchCycles`, `exists_lineCover_isBranchCycleSystem` (the packaged forms of
  the existence direction, generation and product-one included) and `riemann_existence_cover_mpr`
  are *derived* from W1;
* whole families of covers are built **without** W1 at all — every finite abelian group
  (`RET/KummerAbelian.lean`), `Aₙ` and `Sₙ` for every `n` (`RET/SerreCovers.lean`), every dihedral
  group `Dₙ` (`RET/DihedralCover.lean`, by Artin's fixed-field theorem applied to the substitutions
  `u ↦ ζⁱ·u` and `u ↦ ζⁱ·u⁻¹`), every group with a branch datum of rank `r ≤ 2`
  (`RET/ExistenceLowRank.lean`), every *abelian* group with a branch datum of *any* rank
  (`RET/FreeAbelianCover.lean`, `RET/ExistenceAbelian.lean`) — the last two including the full
  `exists_cover` clause of `GeomRET`, branch points and distinguished inertia and all, see below —
  and anything obtained from these by quotients.  These are the classical explicit-polynomial cases; W1 is what covers
  the rest;
* and W1 itself is a theorem in two regimes: over at most two branch points, for every finite group
  (`geomRET_of_le_two`), and over any number of branch points, for abelian deck groups
  (`geomRETComm`).  So what W1 still assumes is the *construction* of a cover with a prescribed
  non-abelian monodromy over three or more points, which is exactly the regime the rigidity method
  uses.

**The abelian case of `exists_cover` is a theorem, in every rank (done).**  Unconditionally and
sorry-free, in `RET/FreeAbelianCover.lean` (the free cover and its local theory) and
`RET/ExistenceAbelian.lean` (the descent and assembly):

```lean
theorem exists_cover_of_commGroup {r : ℕ} (t : Fin r → k) (ht : Function.Injective t)
    {H : Type} [CommGroup H] [Finite H] (h : Fin r → H)
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (L : LineCover) (e : L.deck ≃* H),
      L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
      ∀ i, L.IsInertiaGenAt (t i) (e.symm (h i))
```

— verbatim the `exists_cover` clause of `GeomRET t`, restricted to abelian `H`, with no bound on
the number of branch points.  The proof is *free cover, then quotient*:

* over `r = s + 1` points `t₀, …, t_s` and for `n = |H|`, `RET/FreeAbelianCover.lean` builds the
  **free** cover of exponent `n` — the splitting field of `∏_{l<s} (Xⁿ - bₗ)` where
  `bₗ = (T - tₗ) · (∏_{i<s}(T - tᵢ))^{n-1}` is the one-point Kummer datum of `MultiKummer`
  normalized to total degree `n` (`freeExp`, `freeB`, `freePoly`).  Adjoining the `s` radicals
  `yₗ = bₗ^{1/n}` independently gives deck group exactly `μₙ^s ≅ (ℤ/n)^s`
  (`freeTheta_injective`, `freeTheta_surjective`: injectivity because the radicals generate,
  surjectivity because no product `∏ yₗ^{cₗ}` other than the trivial one is a scalar — the
  exponent vectors are independent since each `bₗ` has a pole/zero pattern at `tₗ` that the others
  do not);
* the two inertia computations reuse the cyclic machinery of `MultiKummerInertia`, applied to each
  monomial `∏ yₗ^{cₗ}` at once: `inertia_fix_monomial` says an inertia element at `tᵢ` fixes every
  monomial whose exponent `freeExp n c i` is divisible by `n`, and this pins the inertia group at
  `t_{j}` (`j < s`) to the `j`-th coordinate `zpowers` (`geomInertia_free_castSucc`), and the
  inertia at the last point `t_s` to the anti-diagonal `(ζ, …, ζ)⁻¹`
  (`geomInertia_free_last`) — the algebraic shadow of the product-one relation again;
* unramifiedness outside the `tᵢ` and at infinity are the multi-point Kummer arguments, applied
  coordinatewise (`free_inertia_eq_one_outside`, `free_isUnramifiedAtInfinity`);
* finally, a product-one generating tuple `h : Fin (s+2) → H` is exactly a surjection
  `π : (ℤ/n)^{s+1} ↠ H` sending the coordinate vectors to `h₀, …, h_s` and the anti-diagonal to
  `h_{s+1}`, and the corresponding **subcover** — the fixed field of `ker(π ∘ e)` — has deck group
  `H` by the Galois correspondence (`descentEquiv`, built from
  `IsGalois.normalAutEquivQuotient`), with the distinguished inertia generators restricting
  correctly (`LineCover.IsInertiaGenAt.restrict`) and unramifiedness inherited
  (`IsUnramifiedOutside.sub`, `IsUnramifiedAtInfinity.sub`).  Ranks `r ≤ 1` force `H` trivial and
  are handed to the cyclic case.

**The cyclic case of `exists_cover` is a theorem, in every rank (done).**  Unconditionally and
sorry-free, in `RET/MultiKummer.lean` and `RET/MultiKummerInertia.lean` (local theory) and
`RET/ExistenceCyclic.lean` (assembly):

```lean
theorem exists_cover_of_isCyclic {r : ℕ} (t : Fin r → k) (ht : Function.Injective t)
    {H : Type} [Group H] [Finite H] [IsCyclic H] (h : Fin r → H)
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (L : LineCover) (e : L.deck ≃* H),
      L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
      ∀ i, L.IsInertiaGenAt (t i) (e.symm (h i))
```

— verbatim the `exists_cover` clause of `GeomRET t`, restricted to cyclic `H`, with no bound on the
number of branch points.  The cover is the multi-point Kummer cover `wⁿ = ∏ᵢ (T - tᵢ)^{aᵢ}`, where
`n = |H|` and `aᵢ` is the exponent of `hᵢ` read through an isomorphism `H ≅ ℤ/n`.  The three
hypotheses of the correspondence become the three hypotheses of the construction, exactly:

* *the `hᵢ` generate* ⟹ no proper divisor of `n` kills all the `aᵢ`, which by Kummer duality
  (`irreducible_X_pow_sub_C_of_forall_isPow`, `irreducible_multiA`) makes `Xⁿ - ∏ᵢ (T - tᵢ)^{aᵢ}`
  irreducible over `ℚ̄(T)` — Eisenstein is unavailable here, and Mathlib's criteria for `Xⁿ - a`
  need odd `n`, so irreducibility is proven by bounding the degree above by the single generator
  `w` and below by the surjectivity of the Kummer monodromy onto `μₙ`;
* *`∏ᵢ hᵢ = 1`* ⟹ `n ∣ ∑ᵢ aᵢ`, so with `∑ᵢ aᵢ = ns` the element `u = w·T⁻ˢ` satisfies
  `uⁿ = ∏ᵢ (1 - tᵢS)^{aᵢ}` in the coordinate `S = T⁻¹` (`revMultiA`, `twistRootS`,
  `invSubst_revMultiA`), whose right-hand side is `1` at `S = 0`; hence
  `isUnramifiedAtInfinity_multiCover`.  This is the algebraic shadow of the product-one relation:
  the branch cycles of a cover of the line multiply to the inverse of the branch cycle at infinity;
* *the `tᵢ` are distinct* ⟹ `geomInertia_eq_zpowers_multi`: the inertia group at any place over
  `tⱼ` is generated by the deck transformation `w ↦ ζ^{aⱼ}w`, i.e. by the image of `hⱼ`.

The inertia computation is the substance, and it is an equality of two bounds with `d = gcd(n, aⱼ)`,
`m = n/d`, `A = aⱼ/d`:

* *above* — the element `Y = w^m/(T - tⱼ)^A` satisfies `Y^d = ∏_{i≠j} (T - tᵢ)^{aᵢ}`, so `Y` is
  integral and a unit at `tⱼ`; an inertia element scales it by a *constant* root of unity, which
  must therefore be `1` (`const_eq_one_of_mem_inertia`), and that forces `d ∣ c` for the exponent
  `c` by which the element scales `w` (`gcd_dvd_of_mem_inertia_multi`);
* *below* — Bézout `A·x = m·p + 1` makes `z = w^x/(T - tⱼ)^p` integral with
  `z^m = Y^x·(T - tⱼ)`; since `Q ∤ (Y)` this gives `Q^m ∣ (T - tⱼ)` as ideals
  (`multi_pow_dvd_map_placeP`), so `e(Q) ≥ m` and `|I(Q)| ≥ m`
  (`le_card_geomInertia_of_pow_dvd`).

Both bounds are `m = n/gcd(n,aⱼ)`, which is the order of `hⱼ`, so the containment
`I(Q) ≤ ⟨hⱼ⟩` of the first is an equality by cardinality.  Note that the cover is *not* totally
ramified at `tⱼ` in general — the `r ≤ 2` argument below, which only ever needs
`I(Q) = ⊤`, does not generalize; the exact inertia group has to be computed.

**The `r ≤ 2` case of `exists_cover` is a theorem (done).**  Unconditionally and sorry-free, in
`RET/KummerInertia.lean` (local theory) and `RET/ExistenceLowRank.lean` (assembly):

```lean
theorem exists_cover_of_le_two {r : ℕ} (hr : r ≤ 2) (t : Fin r → k) (ht : Function.Injective t)
    {H : Type} [Group H] [Finite H] (h : Fin r → H)
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (L : LineCover) (e : L.deck ≃* H),
      L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
      ∀ i, L.IsInertiaGenAt (t i) (e.symm (h i))
```

— that is, verbatim the `exists_cover` clause of `GeomRET t`, restricted to `r ≤ 2`.  For `r ≤ 1`
the tuple forces `H` trivial and the cover is the line itself (`trivialCover`); for `r = 2` the
tuple is `(h₀, h₀⁻¹)` with `H = ⟨h₀⟩` cyclic of some order `n`, and the cover is the two-point
Kummer cover `wⁿ = (T - t₀)(T - t₁)^{n-1}`.  Its local theory:

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
  group is a *distinguished* inertia element at either point, and both `h₀` and `h₀⁻¹` are
  generators;
* `isUnramifiedAtInfinity_kummerCover` — the datum has degree `n`, so in the coordinate `S = T⁻¹`
  the element `u = w·S` satisfies `uⁿ = (1 - t₀S)(1 - t₁S)^{n-1}` (`revKummerA`, `twistRoot`,
  `invSubst_revKummerA`, `twistRoot_pow`), whose right-hand side is `1` at `S = 0`.  An
  automorphism of a cover over the base multiplies an `n`-th root of a scalar by an `n`-th root of
  unity, which over `ℚ̄` is a *constant* (`exists_const_smul_of_pow_mem`); at a place over `S = 0`
  the root `u` is a unit, so an inertia element scales it by `1`
  (`kummer_fix_of_mem_inertia_zero`), hence fixes `w`, hence is the identity.  This route needs no
  splitting-field structure on the twist at all.

**The cyclic case of `exists_cycles` is a theorem too, in every rank (done).**  Unconditionally and
sorry-free, in `RET/KummerNormalForm.lean`, `RET/CyclicKummerModel.lean`,
`RET/CyclicBranchLocus.lean`, `RET/LocalKummer.lean`, `RET/CyclicAtInfinity.lean` (theory) and
`RET/CyclicCycles.lean` (assembly):

```lean
theorem exists_branchCycleGenSystem_of_isCyclic (L : LineCover) [IsCyclic L.deck] {r : ℕ}
    (t : Fin r → k) (ht : Function.Injective t) (hS : L.IsUnramifiedOutside (Set.range t))
    (hinf : L.IsUnramifiedAtInfinity) :
    ∃ g : Fin r → L.deck, L.IsBranchCycleGenSystem t g
```

— verbatim the `exists_cycles` clause of `GeomRET t`, restricted to covers with cyclic deck group.
The route runs the cyclic `exists_cover` argument backwards, and each of the three clauses of
`IsBranchCycleGenSystem` comes out of one of the three inputs:

* *the cover is a multi-point Kummer cover.*  Kummer theory gives a radical generator
  `M = ℚ̄(T)(w)`, `wⁿ = a`, and `a` matters only modulo `n`-th powers; over an algebraically closed
  constant field every rational function is, modulo `n`-th powers, a product `∏ᵢ (T - tᵢ)^{eᵢ}` of
  linear polynomials with `0 ≤ eᵢ < n` (`isLinPow_of_ne_zero`, `exists_count_lt`,
  `exists_multiA_mul_pow`).  Since `w` generates, `Xⁿ - a` is its minimal polynomial, hence
  irreducible, and `M` is its splitting field (`exists_multiKummer_model`);
* *`IsUnramifiedOutside (range t)` ⟹ the exponents live on `t`.*  A point `p` carrying a nonzero
  exponent is a branch point: `isInertiaGenAt_multiCover` produces an inertia element there whose
  parameter is `eₚ mod n ≠ 0`, so unramifiedness forces `n ∣ eₚ`, hence `eₚ = 0`.  The exponents
  can then be re-indexed onto the prescribed tuple `t` (`exists_reindex_multiA`,
  `exists_multiKummer_model_on`);
* *connectedness ⟹ the branch cycles generate.*  If a prime `p ∣ n` divided every `eᵢ` then
  `∏ᵢ (T - tᵢ)^{eᵢ}` would be a `p`-th power, contradicting irreducibility of `Xⁿ - a`
  (`pow_ne_of_irreducible_X_pow_sub_C`, `multiA_pow_of_dvd`); so the residues `eᵢ` generate `ℤ/n`
  (`closure_range_ofAdd_eq_top`), and so do the corresponding deck transformations;
* *`IsUnramifiedAtInfinity` ⟹ the branch cycles multiply to one.*  This is the converse of
  `isUnramifiedAtInfinity_multiCover`.  Choose `s` with `∑ᵢ eᵢ + c = n·s` and `0 ≤ c < n`; then in
  the coordinate `S = T⁻¹` the element `u = w·T⁻ˢ` satisfies `uⁿ = ∏ᵢ (1 - tᵢS)^{eᵢ}·S^c`
  (`twistRootS_pow_gen`).  If `c > 0` the origin of the twist occurs in the radicand to the
  multiplicity `c`, and the local ramification bound gives inertia of order at least
  `n/gcd(n, c) ≥ 2` there — ramification at infinity.  So `c = 0`, i.e. `n ∣ ∑ᵢ eᵢ`
  (`dvd_sum_of_isUnramifiedAtInfinity`), which is exactly `∏ᵢ gᵢ = 1`.

The local ramification bound used at infinity is the `exists_cover` bound with the shape of the
radicand away from the point forgotten: for `A = (T - p)^c · U` with `U(p) ≠ 0`, the place above
`p` occurs to the power `n/gcd(n, c)` in the extended place (`local_pow_dvd_map_placeP`,
`RET/LocalKummer.lean`).  `multi_pow_dvd_map_placeP` is now a one-line corollary of it.

Two corollaries fall out of the degenerate ranks (`RET/CyclicCycles.lean`): a cyclic cover of the
line unramified everywhere is trivial (`subsingleton_deck_of_unramified`, rank `0`: no branch point
means no generator), and so is one branched over a single point
(`subsingleton_deck_of_unramified_outside_singleton`, rank `1`: a lone branch cycle equals the
inverse of the empty product).  These are the algebraic shadow of `π₁(ℙ¹) = π₁(𝔸¹) = 1`.

### The generation clause of `exists_cycles` holds for every abelian deck group

`RET/AbelianGeneration.lean` bootstraps the rank-`0` corollary from cyclic to abelian deck groups:

```lean
theorem closure_isInertiaAt_eq_top_of_comm (L : LineCover) (hab : ∀ a b : L.deck, a * b = b * a)
    (hinf : L.IsUnramifiedAtInfinity) :
    Subgroup.closure {σ : L.deck | ∃ t : k, L.IsInertiaAt t σ} = ⊤
```

— the inertia elements of an abelian cover generate its deck group; equivalently, an abelian cover
of the line unramified everywhere and at infinity is trivial
(`subsingleton_deck_of_comm_of_unramified`).  The argument is a descent to the cyclic case: if the
subgroup `B` generated by all inertia elements were proper, it would lie inside a maximal subgroup
`B'` of the (finite) deck group, which in an abelian group is normal with cyclic quotient — for any
`x ∉ B'`, maximality gives `⟨x⟩ ⊔ B' = ⊤`, so the quotient is generated by the image of `x`.  The
Galois subcover cut out by `B'` (`descentEquiv`) then has cyclic deck group, is unramified at
infinity (`IsUnramifiedAtInfinity.sub`) and unramified *everywhere*, because every inertia element
of the big cover restricts trivially to it (`isUnramifiedOutside_sub`, the variant of
`IsUnramifiedOutside.sub` that replaces "inertia upstairs is trivial" by "inertia upstairs dies
downstairs").  The rank-`0` corollary then makes that subcover trivial, contradicting `x ∉ B'`.

### An abelian cover branched over at most two points is cyclic

Both halves of that descent are stated over an arbitrary allowed branch set — a subcover in which
the inertia away from `S` dies is unramified outside `S` (`isUnramifiedOutside_sub`), so a cyclic
quotient of the deck group killing all inertia away from a *single* point `t₀` is trivial
(`eq_one_of_cyclic_quotient_singleton`, by the rank-`1` corollary instead of the rank-`0` one).
That upgrade plus one extra observation,

```lean
theorem isInertiaAt_iff_mem_of_comm (L : LineCover) (hab : ∀ a b : L.deck, a * b = b * a) (t : k)
    (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP t)] {σ : L.deck} :
    L.IsInertiaAt t σ ↔ σ ∈ geomInertia L.M Q
```

— for an abelian deck group *all* the inertia groups above a point coincide, since the deck group
permutes the places above `t` transitively (`exists_smul_eq_of_liesOver`) and moves inertia groups
by conjugation (`geomInertia_smul`) — gives

```lean
theorem isCyclic_deck_of_comm_of_unramified_outside_pair (L : LineCover)
    (hab : ∀ a b : L.deck, a * b = b * a) (t₀ t₁ : k) (hS : L.IsUnramifiedOutside {t₀, t₁})
    (hinf : L.IsUnramifiedAtInfinity) : IsCyclic L.deck
```

If the inertia group `I₀` above `t₀` were proper it would sit inside a maximal `B'`, and the cyclic
quotient by `B'` would kill every inertia element except those above `t₁` — trivial by the
singleton lemma, contradicting `IsCoatom B'`.  So `I₀ = ⊤`, and a geometric inertia group is cyclic
(`GeomAKLB.isCyclic_geomInertia`).  This is the algebraic shadow of `π₁(𝔾_m)^ab = Ẑ`: it pins down
the *isomorphism type* of the deck group, not merely a generating set, in the first rank where the
group is allowed to be nontrivial.  Feeding it back into the cyclic converse closes the whole
`exists_cycles` clause — branch cycles, generation *and* product-one — for abelian deck groups in
rank two (`exists_branchCycleGenSystem_of_comm_of_two`).  In every rank the coincidence of the
inertia groups above a point also sharpens generation to its localized form: one place `Qᵢ` above
each branch point `tᵢ` already gives `⨆ᵢ geomInertia L.M Qᵢ = ⊤`
(`exists_places_iSup_geomInertia_eq_top_of_comm`), so what the product-one clause has to supply is
exactly a coherent *generator* of each `geomInertia L.M Qᵢ`.  Picking those generators arbitrarily
already gives everything else:

```lean
theorem exists_inertiaGens_of_comm (L : LineCover) (hab : ∀ a b : L.deck, a * b = b * a) {r : ℕ}
    (t : Fin r → k) (hS : L.IsUnramifiedOutside (Set.range t))
    (hinf : L.IsUnramifiedAtInfinity) :
    ∃ g : Fin r → L.deck,
      (∀ i, L.IsInertiaGenAt (t i) (g i)) ∧ Subgroup.closure (Set.range g) = ⊤
```

— the abelian analogue of the cyclic `exists_inertiaGens_of_isCyclic`, in every rank and with no
injectivity hypothesis on `t`: it is `IsBranchCycleGenSystem` minus the field `prod`.

Applied to the subcover cut out by the commutator subgroup, whose deck group is the abelianization
and whose branch locus is no larger, the low-rank theorems shed the commutativity hypothesis
altogether: the abelianized deck group of a cover branched over at most two points is cyclic
(`isCyclic_abelianization_of_unramified_outside_pair`), and a cover branched over at most one point
has *perfect* deck group (`subsingleton_abelianization_of_unramified_outside_singleton`).  That is
as much of `π₁(𝔸¹) = 1` as is available without the correspondence: these methods see only abelian
quotients, and a perfect group has none.  In arbitrary rank the same subcover gives the generator
bound `exists_gens_abelianization_of_unramifiedOutside`: the abelianized deck group of a cover
unramified outside `r` points and infinity is generated by `r` elements (the sharp bound `r - 1`
is again the product-one clause).

For a *solvable* deck group the perfectness statement is already the whole theorem, since a
solvable group with trivial abelianization is trivial:

```lean
theorem subsingleton_deck_of_isSolvable_of_unramified_outside_singleton (L : LineCover)
    [IsSolvable L.deck] (t₀ : k) (hS : L.IsUnramifiedOutside {t₀})
    (hinf : L.IsUnramifiedAtInfinity) : Subsingleton L.deck
```

— i.e. `π₁(𝔸¹) = 1` holds unconditionally for the prosolvable (in particular pronilpotent, and
`p`-group) quotient.  The two-point statement does *not* similarly upgrade from abelian to
solvable: every quotient of `S₃` has cyclic abelianization, so the abelian shadow alone cannot
force a solvable cover branched over two points to be cyclic; that needs product-one.  It does
upgrade to *nilpotent*, where cyclicity of the abelianization propagates to the group
(`isCyclic_of_isNilpotent_of_isCyclic_abelianization`: a generator of the abelianization would
otherwise sit inside a maximal subgroup, normal by the normalizer condition, whose quotient is
cyclic and hence swallows the commutator subgroup too):

```lean
theorem isCyclic_deck_of_isNilpotent_of_unramified_outside_pair (L : LineCover)
    [Group.IsNilpotent L.deck] (t₀ t₁ : k) (hS : L.IsUnramifiedOutside {t₀, t₁})
    (hinf : L.IsUnramifiedAtInfinity) : IsCyclic L.deck
```

so `exists_cycles` holds in full over two points for nilpotent deck groups
(`exists_branchCycleGenSystem_of_isNilpotent_of_two`), in particular for `p`-groups
(`isCyclic_deck_of_isPGroup_of_unramified_outside_pair`).

Generation by inertia likewise survives dropping commutativity, in the two forms the abelian
shadow can see:

```lean
theorem normalClosure_isInertiaAt_sup_commutator_eq_top (L : LineCover)
    (hinf : L.IsUnramifiedAtInfinity) :
    Subgroup.normalClosure {σ : L.deck | ∃ t : k, L.IsInertiaAt t σ} ⊔ commutator L.deck = ⊤

theorem normalClosure_isInertiaAt_eq_top_of_isSolvable (L : LineCover) [IsSolvable L.deck]
    (hinf : L.IsUnramifiedAtInfinity) :
    Subgroup.normalClosure {σ : L.deck | ∃ t : k, L.IsInertiaAt t σ} = ⊤
```

and in localized form, one chosen place above each branch point already suffices
(`exists_places_normalClosure_iSup_geomInertia_sup_commutator_eq_top`), since the places above a
point are a single deck orbit.

Both go through the quotient of the deck group by the normal closure of the inertia (joined with
the commutator subgroup in the first case): it is the deck group of a cover of the line unramified
everywhere, abelian in the first case and solvable in the second, hence trivial.  For a general
deck group the quotient is only known to be perfect.

### `π₁(𝔸¹) = 1` unconditionally, and the whole correspondence in rank ≤ 2 (done)

The perfectness ceiling above is not the end: for *one* branch point the correspondence itself is a
theorem, with no hypothesis on the deck group at all (`RET/TranslateInfinity.lean`):

```lean
theorem subsingleton_deck_of_unramifiedOutside_singleton (L : LineCover) (t₀ : k)
    (h₁ : L.IsUnramifiedOutside {t₀}) (h₂ : L.IsUnramifiedAtInfinity) : Subsingleton L.deck
```

— the once-punctured sphere is simply connected, algebraically.  Inverting the coordinate turns a
cover branched only over `t₀` and infinity into one branched nowhere on the affine line
(`isUnramifiedOutside_empty_twist_inv`), and a cover unramified over the whole affine line *and* on
the chart at infinity is trivial by `NoUnbranchedCover.subsingleton_deck_of_unramified`; a
translation moves an arbitrary `t₀` to the origin.  The one-term branch-cycle system follows
(`exists_branchCycleGenSystem_singleton`), and with the two-point case
(`RET/TwoPointCyclic.lean`, `exists_branchCycleGenSystem_pair`, from
`isCyclic_deck_of_unramifiedOutside_pair` — an arbitrary cover branched over two points is cyclic:
move the points to `0` and `∞`, enlarge the cover by the Kummer line `uᵐ = T` with `m` the order of
the deck group, which changes neither the branch locus nor the exponent, and the enlargement is
cyclic by the cyclic case, hence so is its quotient) the whole of W1 is a theorem in low rank
(`RET/LowRankRET.lean`):

```lean
theorem geomRET_of_le_two {r : ℕ} (hr : r ≤ 2) (t : Fin r → k) (ht : Function.Injective t) :
    GeomRET t
```

— both clauses, every finite group, no hypotheses beyond `r ≤ 2`.  `r = 3` is where the wall
actually begins, and that is exactly where the rigidity method lives.

### The abelian case of `exists_cycles`, hence of all of W1, is a theorem (done)

The product-one clause missing above — the inertia generators `gᵢ` of the cyclic groups `Iᵢ` have
to be chosen coherently before their ordered product can be trivial — is now proven for every
abelian deck group and every rank (`RET/AbelianEmbed.lean`, `RET/AbelianCycles.lean`):

```lean
theorem exists_branchCycleGenSystem_of_comm (L : LineCover) (hab : ∀ a b : L.deck, a * b = b * a)
    {r : ℕ} (t : Fin r → k) (ht : Function.Injective t)
    (hS : L.IsUnramifiedOutside (Set.range t)) (hinf : L.IsUnramifiedAtInfinity) :
    ∃ g : Fin r → L.deck, L.IsBranchCycleGenSystem t g
```

The coherent choice is not made by hand: the cover is *embedded* into the free abelian cover of
`RET/FreeAbelianCover.lean` over the same points (`exists_algHom_of_comm` — an abelian cover of
exponent dividing `n` branched inside `{t₀,…,t_{r-1}}` is a subcover of the free one, because the
free cover is the compositum of all of them), and the branch cycles are the *restrictions* of the
free cover's, whose product-one relation is the one computed in the construction.  Together with
the abelian `exists_cover` this closes the correspondence for abelian deck groups in every rank
(`RET/AbelianRET.lean`):

```lean
structure GeomRETComm {r : ℕ} (t : Fin r → k) : Prop     -- `GeomRET` with `Finite` → `CommGroup`
theorem geomRETComm {r : ℕ} (t : Fin r → k) (ht : Function.Injective t) : GeomRETComm t
```

**RET is proven, unconditionally, for abelian deck groups.**  Beyond abelian, `exists_cycles` needs
the correspondence itself: reading branch cycles off an arbitrary cover is the direction that sees
the topology.  What survives the drop of commutativity is the abelianized shadow
(`RET/AbelianizedCycles.lean`, `RET/InertiaLift.lean`): for *any* deck group there are
distinguished inertia generators over the prescribed points whose images generate the
abelianization and multiply to one there (`exists_branchCycles_mod_commutator`,
`exists_generating_abelianization`), and for a *nilpotent* deck group the generation clause is
honest, not merely abelianized (`RET/NilpotentCycles.lean`,
`exists_branchCycles_generating_of_isNilpotent`, by the nilpotent Frattini argument
`eq_top_of_sup_commutator_eq_top`).  Product-one for a non-abelian group is the wall.

### The counting theorems, with no prescribed branch locus and no hypothesis at infinity

Two hypotheses that look structural turn out to be free.

*The branch locus need not be prescribed* (`RET/BranchSet.lean`, `RET/BranchLocus.lean`).  A deck
transformation `σ ≠ 1` moves some polynomial, and only the finitely many places dividing the
relevant numerators can ramify, so `LineCover.branchLocus` — the set of points of the affine line
carrying nontrivial inertia — is finite (`LineCover.finite_branchLocus`,
`exists_unramifiedOutside_range`).  Every branch-cycle
theorem above therefore has a primed form taking no tuple of points at all
(`exists_branchCycleGenSystem_of_isCyclic'`, `…_of_comm'`, `exists_branchCycles_of_isNilpotent'`,
`exists_branchCycles_mod_commutator'`).

*Unramifiedness at infinity need not be assumed* (`RET/MoveInfinity.lean`).  A coordinate change
`T ↦ (T - a)⁻¹` with `a` outside the branch locus moves infinity to an unramified point, at the
cost of at most one new affine branch point
(`exists_twist_isUnramifiedAtInfinity_ncard`).  So every counting statement holds for a *bare*
cover, and the natural classes to state them for are

```lean
def IsDeckGroupOver (S : Set k) (G : Type) [Group G] [Finite G] : Prop   -- RET/DeckGroups.lean
def IsAffineDeckGroup (n : ℕ) (G : Type) [Group G] [Finite G] : Prop     -- RET/MoveInfinity.lean
```

— groups occurring over a prescribed locus, resp. with at most `n` affine branch points.  Both are
closed under quotients (`IsDeckGroupOver.quotient`, `IsAffineDeckGroup.quotient`), the first feeds
the second (`IsDeckGroupOver.isAffineDeckGroup`), and the resulting count is *sharp* for abelian
groups: an abelian group needs exactly one more branch point than it needs generators
(`exists_cover_card_branchLocus_of_commGroup` against `two_add_le_card_branchLocus_of_comm`), a
cover with at most one affine branch point has cyclic deck group and conversely
(`isCyclic_iff_exists_cover_ncard_branchLocus_le_one`), and read backwards the abelianized count is
an obstruction valid for every group (`not_isAffineDeckGroup_of_abelianization`,
`le_ncard_branchLocus_of_abelianization`).

### Where the branch points are does not matter: Möbius transport of W1

Three distinct points of the projective line carry no invariant, so W1 over three points should not
depend on *which* three.  It does not, and that is now a theorem, proven by moving covers along
coordinate changes rather than by re-running any construction.

The moves are the generators of `PGL₂`.  Twisting a cover along a ring automorphism of `ℚ̄(T)`
(`RET/Twist.lean`) carries `LineCover`s to `LineCover`s; what has to be checked is that the branch
data comes along.  `RET/AffineTransport.lean` does the affine substitutions `T ↦ cT` and
`T ↦ T + a`, `RET/Inversion.lean` the one remaining generator `T ↦ T⁻¹`:

```lean
theorem IsMonodromyOver.affine (hc : c ≠ 0) (a : k) (H : IsMonodromyOver h t) :
    IsMonodromyOver h fun i => c * t i + a
theorem IsMonodromyOver.twist_inv (ht : ∀ i, t i ≠ 0) (H : IsMonodromyOver h t) :
    IsMonodromyOver h fun i => (t i)⁻¹
```

`IsMonodromyOver h t` (`RET/GeomRET.lean`) is the `exists_cover` clause of `GeomRET t` for *one*
tuple `h` — the cover, the isomorphism of its deck group with the group carrying `h`, the two
unramifiedness clauses, and the distinguished inertia generators.  Stating the transports at that
granularity is what makes them usable: `GeomRETExistence` quantifies over every finite group at
once, so a cover built for a single group could not be moved through it.  Each transport therefore
comes in four forms — for a tuple, for `GeomRETExistence`, for `GeomRETCompleteness`, and for
`GeomRET`.

The inversion is the substantive one, because `T ↦ T⁻¹` does not preserve the polynomial ring and so
does not act on places by pulling back maximal ideals of `ℚ̄[X]`.  `RET/Inversion.lean` replaces the
ideal-theoretic notion of a place by a valuation-theoretic one — `IsInertiaGenAtPlace`, "σ generates
the inertia group of a valuation subring of `M` lying over the `(T - t)`-adic valuation" — proves it
agrees with `IsInertiaGenAt` (`isInertiaGenAtPlace_iff`, via `exists_place_of_valuation`), and then
transports *that*, where the substitution is visibly an isomorphism of valued fields
(`valuation_inv_sub_inv_lt_one`: `|s⁻¹ - t⁻¹| < 1` when `|s - t| < 1` and `t ≠ 0`).

With all three generators in hand, `RET/ProjectiveTransport.lean` closes the group up.  A predicate
on triples that survives translation, scaling and inversion survives every coordinate change:

```lean
structure IsTripleInvariant (P : (Fin 3 → k) → Prop) : Prop where
  translate : ∀ {t} (a), P t → P fun i => t i + a
  scale     : ∀ {t} {c} (hc : c ≠ 0), P t → P fun i => c * t i
  inv       : ∀ {t} (ht : ∀ i, t i ≠ 0), P t → P fun i => (t i)⁻¹

theorem IsTripleInvariant.transport (hP : IsTripleInvariant P)
    (ht : Function.Injective t) (hs : Function.Injective s) : P t → P s
```

The proof normalizes both triples to `(0, 1, λ)` by an affine map and then moves `λ` to `μ`: reading
in the coordinate `T ↦ (T - c)⁻¹` with `c = λ(1 - μ)/(λ - μ)` and renormalizing does it in one step
(`IsTripleInvariant.inv_step`, `IsTripleInvariant.normalized`).  Applied to the four predicates:

```lean
theorem isMonodromyOver_transport (ht : Function.Injective t) (hs : Function.Injective s)
    (H : IsMonodromyOver h t) : IsMonodromyOver h s
theorem geomRET_transport (ht : Function.Injective t) (hs : Function.Injective s)
    (H : GeomRET t) : GeomRET s
```

**So W1 over three branch points is a single statement**, not a family of them: proving `GeomRET t`
for one injective triple `t` proves it for all of them.  That is the regime the rigidity method
lives in, and it is now one theorem instead of a moduli of theorems.

### The first non-abelian three-point covers, over every triple

`RET/DihedralCover.lean` and `RET/DihedralInertia.lean` build the dihedral covers explicitly and
compute their inertia — the first branch-cycle computation in this development for a non-abelian
group — and `RET/DihedralExistence.lean` assembles them into the full `exists_cover` clause for
`Dₙ`, over the harmonic triple `{0, 1/2, -1/2}` where the Kummer pullback is cleanest
(`exists_cover_dihedral`).  Möbius transport then removes the harmonic triple from the statement
(`RET/DihedralTriple.lean`):

```lean
theorem exists_cover_dihedral_triple (n : ℕ) [NeZero n] (hn : 3 ≤ n) {t : Fin 3 → k}
    (ht : Function.Injective t) {h : Fin 3 → DihedralGroup n}
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (L : LineCover) (e : L.deck ≃* DihedralGroup n),
      L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
      ∀ i, L.IsInertiaGenAt (t i) (e.symm (h i))
```

— verbatim the `exists_cover` clause of `GeomRET t` at `r = 3`, for a non-abelian group, over an
arbitrary ordered triple of distinct points, with the ordering of the branch cycles prescribed too.

### A branch point carrying the trivial branch cycle is not a branch point

`RET/TrivialCycle.lean` settles the degenerate entries of a branch datum.  The inertia groups above
a point are conjugate, so one of them being trivial makes all of them trivial, and every point of
the line carries a place; hence

```lean
theorem LineCover.isInertiaGenAt_one_iff (L : LineCover) {t : k} :
    L.IsInertiaGenAt t 1 ↔ ∀ σ : L.deck, L.IsInertiaAt t σ → σ = 1
```

— the trivial deck transformation is a distinguished inertia generator at `t` exactly when the cover
is unramified at `t`.  Consequently a realization may be padded with trivial branch cycles and
stripped of them again (`IsMonodromyOver.snoc`, `IsMonodromyOver.of_snoc`), and the branch points and
branch cycles may be permuted together (`IsMonodromyOver.reindex`).  A branch datum is therefore an
*unordered family of nontrivial cycles attached to points*, and nothing else.  (This buys no new
groups at `r = 3`: a generating product-one triple with a trivial entry is a generating pair
`(h, h⁻¹)`, so the group is cyclic and already covered by `geomRETComm`.  What it buys is that the
counting statements are about the honest branch locus.)

### Coordinate changes as a relation on tuples, in every rank

Transport is stated above one predicate at a time and one triple at a time.  `RET/MobiusRelated.lean`
turns it into a relation between tuples of *any* length: `MobiusStep` is one translation, one scaling
or the inversion `T ↦ T⁻¹` (the last only at a tuple avoiding the origin), `MobiusRelated` is its
reflexive-transitive closure, and each elementary step can be undone
(`MobiusStep.related_symm`), so `MobiusRelated` is an equivalence relation (`MobiusRelated.symm`).
Along it every clause of the correspondence is invariant:

```lean
theorem IsMonodromyOver.mobius (hrel : MobiusRelated t s) (H : IsMonodromyOver h t) :
    IsMonodromyOver h s
theorem GeomRET.mobius (hrel : MobiusRelated t s) (H : GeomRET t) : GeomRET s
```

with `r` arbitrary, so the branch locus of W1 matters only through its `MobiusRelated`-class.  At
`r = 3` that class is everything, and the reason is the transport theorem itself applied to the
relation: `MobiusRelated t ·` is triple-invariant by construction
(`isTripleInvariant_mobiusRelated`), hence

```lean
theorem mobiusRelated_of_injective (ht : Function.Injective t) (hs : Function.Injective s) :
    MobiusRelated t s
```

— sharp three-transitivity, from which `isMonodromyOver_transport` and `geomRET_transport` are the
one-line corollaries they ought to be.  At `r ≥ 4` the class is a proper subset and the quotient is
the moduli of `r` points, so this is exactly where the point-independence of W1 stops.

### Branch-cycle data of coprime order multiply, over one and the same branch locus

`RET/Product.lean` composes two covers when their branch loci are *disjoint*: the intersection of
the two function fields is then unramified everywhere, hence trivial.  That hypothesis is fatal for
W1, where the whole point is to keep the branch locus fixed — the tuple `t` is prescribed, and two
covers branched over the same `t` are never disjointly branched.  `RET/CoprimeProduct.lean` replaces
disjointness of the loci by coprimality of the degrees, which leaves the branch locus free:

```lean
theorem LineCover.inf_eq_bot_of_coprime (L : LineCover) (A B : IntermediateField (RatFunc k) L.M)
    (hcop : Nat.Coprime (Module.finrank (RatFunc k) A) (Module.finrank (RatFunc k) B)) :
    A ⊓ B = ⊥
```

— a subcover of both has degree dividing two coprime numbers.  With that, restriction to the two
subcovers is not merely injective (`SubcoverProduct.lean`) but bijective, and the deck group of the
compositum *is* the product, `LineCover.deckProdEquiv : L.deck ≃* (L.sub A).deck × (L.sub B).deck`.

The branch cycles survive too, and this is the part that is special to coprimality.  Inertia above a
point is cyclic, so the inertia group of the compositum is generated by a single pair; its two
coordinates generate the inertia groups downstairs, but only up to conjugacy, and only after
independent conjugation in each factor — which is available precisely because the deck group is a
product.  What coprimality then buys is that the prescribed pair is itself a generator: in
`G₁ × G₂` with `Nat.Coprime (orderOf a) (orderOf b)`, raising `(a, b)` to `orderOf b` kills the
second coordinate without moving the cyclic group generated by the first, so

```lean
theorem zpowers_mk_eq_of_zpowers_eq (hcop : Nat.Coprime (orderOf a) (orderOf b))
    (hx : Subgroup.zpowers x = Subgroup.zpowers a)
    (hy : Subgroup.zpowers y = Subgroup.zpowers b) :
    Subgroup.zpowers ((x, y) : G₁ × G₂) = Subgroup.zpowers ((a, b) : G₁ × G₂)
```

and a pair of distinguished inertia generators is a distinguished inertia generator
(`LineCover.isInertiaGenAt_deckProdEquiv_symm`).  Assembling over the compositum:

```lean
theorem IsMonodromyOver.prod_coprime (hcop : Nat.Coprime (Nat.card G₁) (Nat.card G₂))
    (H₁ : IsMonodromyOver h₁ t) (H₂ : IsMonodromyOver h₂ t) :
    IsMonodromyOver (fun i => (h₁ i, h₂ i)) t

theorem IsThreePointMonodromy.prod_coprime (hcop : Nat.Coprime (Nat.card G₁) (Nat.card G₂))
    (H₁ : IsThreePointMonodromy h₁) (H₂ : IsThreePointMonodromy h₂) :
    IsThreePointMonodromy fun i => (h₁ i, h₂ i)
```

Note what is *not* assumed: nothing about the product-one relation, nothing about generation, and no
relation between the two branch loci beyond their being the same tuple.  The realizable branch data
over a fixed tuple is therefore closed under coprime direct products, so the three-point data
already proven (cyclic, and the dihedral triples) generate all their coprime products — for instance
every `Dih(n) × A` with `A` abelian two-generated of order coprime to `2n`.  Coprimality is not
removable by this argument: for two covers of equal degree the intersection can be anything, and
without it the inertia pair is only known up to the Goursat correspondence between the two factors,
which is exactly the ambiguity the coprime power trick removes.

### The groups realized over a fixed locus, as a class closed under coprime products

Splitting the group quantifier off `GeomRETExistence` turns the existence half into a property of
one group at a time (`RET/MonodromyGroup.lean`):

```lean
def IsMonodromyGroupOver (G : Type) [Group G] [Finite G] {r : ℕ} (t : Fin r → k) : Prop :=
  ∀ h : Fin r → G, (List.ofFn h).prod = 1 → Subgroup.closure (Set.range h) = ⊤ →
    IsMonodromyOver h t

theorem geomRETExistence_iff_forall_isMonodromyGroupOver (t : Fin r → k) :
    GeomRETExistence t ↔ ∀ (G : Type) [Group G] [Finite G], IsMonodromyGroupOver G t
```

The class is invariant under isomorphism and under coordinate changes
(`IsMonodromyGroupOver.congr`, `IsMonodromyGroupOver.mobius`), and — this is what the preceding
subsection buys — closed under direct products of coprime order:

```lean
theorem IsMonodromyGroupOver.prod_coprime (hcop : Nat.Coprime (Nat.card G₁) (Nat.card G₂))
    (H₁ : IsMonodromyGroupOver G₁ t) (H₂ : IsMonodromyGroupOver G₂ t) :
    IsMonodromyGroupOver (G₁ × G₂) t
```

The hypotheses on a tuple are what makes this work: a product-one generating tuple in `G₁ × G₂`
projects to a product-one generating tuple in each factor (generation because a surjection carries
generators to generators, product-one because it is a homomorphism), so the two factors deliver
covers over the same locus that the coprime compositum reassembles.  No closure property in the
other direction is available — a generating product-one tuple in a quotient need not lift to one
upstairs, which is precisely why the existence half is not a formal consequence of itself.

Two families are in the class unconditionally: every finite abelian group over every tuple of
distinct points, and every dihedral group over every triple.  Their coprime products are therefore
in it too, and

```lean
theorem isThreePointMonodromy_dihedral_prod (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (hcop : Nat.Coprime (2 * n) (Nat.card A)) (hprod : (List.ofFn h).prod = 1)
    (htop : Subgroup.closure (Set.range h) = ⊤) : IsThreePointMonodromy h
```

gives three-point branch data in groups that are neither abelian nor dihedral, e.g. `Dih(n) × A`
for any abelian `A` of order prime to `2n`.

### Moving the branch points apart: products with no hypothesis on the groups

Coprimality is the price of keeping the branch locus fixed.  If the two loci may be moved apart it
is not needed at all, and any two groups multiply (`RET/DisjointProduct.lean`).  The mechanism is
the localized form of the inertia theorem above: what it really needs is that the two *orders* be
coprime, and above a point of the first locus the second cover is unramified, so its distinguished
inertia element is `1` (`LineCover.isInertiaGenAt_one_of_unramified`) and the hypothesis holds for
free.  The branch cycles of the compositum are then the two given systems, each padded by the
identity of the other factor:

```lean
def padAppend (h₁ : Fin r → G₁) (h₂ : Fin s → G₂) : Fin (r + s) → G₁ × G₂ :=
  Fin.append (fun i => (h₁ i, 1)) (fun j => (1, h₂ j))

theorem IsMonodromyOver.prod_disjoint (hdisj : Disjoint (Set.range t) (Set.range u))
    (H₁ : IsMonodromyOver h₁ t) (H₂ : IsMonodromyOver h₂ u) :
    IsMonodromyOver (padAppend h₁ h₂) (Fin.append t u)
```

The padded tuple is again product-one and again generating (`prod_ofFn_padAppend`,
`closure_range_padAppend_eq_top` — the second because the two padded blocks generate the two factors
separately and `(a, b) = (a, 1)(1, b)`), so this is a genuine branch-cycle system:

```lean
theorem exists_isMonodromyOver_prod (hdisj : Disjoint (Set.range t) (Set.range u)) … :
    ∃ h : Fin (r + s) → G₁ × G₂, (List.ofFn h).prod = 1 ∧
      Subgroup.closure (Set.range h) = ⊤ ∧ IsMonodromyOver h (Fin.append t u)
```

`RET/Product.lean` already had the deck group of such a compositum; what is new is that the branch
cycles come along.  The cost is the branch-point count: `r + s` points rather than
`max r s`, which is why this does not enlarge the *three-point* class and coprimality remains the
only way to multiply groups without paying for it.

### The Hurwitz action moves inside the realized class

`RET/BraidMonodromy.lean`.  A cover sees its branch cycle at a point only up to conjugacy — the
inertia groups at the places over a fixed point are permuted transitively by the deck group — so a
branch datum depends on its tuple of cycles only through the tuple of *conjugacy classes*, and only
up to permuting cycles and points together:

```lean
theorem IsMonodromyOver.of_isConj (H₀ : IsMonodromyOver h t) (hc : ∀ i, IsConj (h i) (h' i)) :
    IsMonodromyOver h' t

theorem IsMonodromyOver.of_conjClasses (H₀ : IsMonodromyOver h t) (σ : Equiv.Perm (Fin r))
    (hcl : ∀ i, ConjClasses.mk (h' i) = ConjClasses.mk (h (σ i))) : IsMonodromyOver h' (t ∘ σ)
```

The Hurwitz move `braidTuple n` of `Rigidity/Braid.lean` transposes the `n`-th and `(n+1)`-st
conjugacy classes and leaves the rest alone (`mk_braidTuple_apply`), so it is exactly absorbed by
transposing the two branch points it moves:

```lean
theorem IsMonodromyOver.braidTuple (hn : n + 1 < r) (H₀ : IsMonodromyOver h t) :
    IsMonodromyOver (braidTuple n h) (t ∘ Equiv.swap ⟨n, _⟩ ⟨n + 1, hn⟩)
```

When the branch points are *not* prescribed — the situation at three points, where any triple of
distinct points is as good as any other — that transposition costs nothing.  Writing
`IsGenericMonodromy h` for realizability over an arbitrary prescribed tuple of distinct points
(at `r = 3` this is `IsThreePointMonodromy`, definitionally), the whole braid-and-conjugation class
of a realized tuple is realized:

```lean
theorem IsGenericMonodromy.braidConj (H₀ : IsGenericMonodromy h) (hb : BraidConj h h') :
    IsGenericMonodromy h'

theorem isMonodromyGroupOver_of_braidConj_reps (ht : Function.Injective t)
    (hrep : ∀ g : Fin r → G, (List.ofFn g).prod = 1 → Subgroup.closure (Set.range g) = ⊤ →
      ∃ g₀, BraidConj g₀ g ∧ IsGenericMonodromy g₀) : IsMonodromyGroupOver G t
```

This is the algebraic shadow of the topological fact that dragging the branch points around one
another carries a cover to a cover; here it is a theorem about inertia and conjugacy alone, with no
topology.  Its use is as a *reduction*: the existence half over a tuple of points need only be
checked on one representative of each braid-and-conjugation class.

Specialized to a rigid class tuple the reduction is total.  Rigidity of `C` says exactly that the
generating product-one tuples in the classes `C` form a single orbit under simultaneous conjugation
(`Rigidity.rigid_card_iff_single_orbit`), and simultaneous conjugation is one of the moves, so a
single realized tuple realizes the whole class:

```lean
theorem isGenericMonodromy_of_rigid (hZ : Subgroup.center G = ⊥)
    (hrigid : Nat.card (rigidTuples C) = Nat.card G) (hg₀ : g₀ ∈ rigidTuples C)
    (H : IsGenericMonodromy g₀) (hg : g ∈ rigidTuples C) : IsGenericMonodromy g
```

with `isGenericMonodromy_of_certificate` the same statement read off a `RigidityCertificate`.  This
is the point where the rigidity-certificate half of the repository and the branch-cycle half meet:
what a certificate buys, over and above the group theory, is that the analytic input is needed for
*one* tuple rather than for all of them.

### Explicit non-abelian branch cycles: Morse and totally ramified fibres

Two families of *computed* branch cycles now exist, both non-abelian, and both obtained by reading
the local ramification off a fibre rather than by any topology.

At a **simple critical value** — a point of the base above which exactly one point of the cover is
a double root and the rest are simple — the inertia group is generated by a transposition of the
roots (`RET/MorseInertia.lean`, `isInertiaGen_and_orderOf`, `isSwap_of_mem_geomInertia`).  Applied
to the equation covers this gives `Sₙ` covers with all branch cycles of order two
(`RET/MorseSymmetric.lean`, `RET/SymmetricBranch.lean`), and the bound `n − 1` on the number of
branch points of a simply-branched `Sₙ` cover (`RET/MorseBranchCycles.lean`).  The general local
statement behind it is a bound on the inertia exponent by the root multiplicities in the fibre
(`RET/RamificationBound.lean`).

At the other extreme, a **totally ramified** fibre — one point of the cover above the point of the
base — carries an inertia group equal to the whole deck group, acting as an `n`-cycle on the roots
(`RET/TrinomialTotal.lean`, `RET/TrinomialCycle.lean` for the trinomial models).  The counting
identity behind both extremes is the geometric fundamental identity

```lean
theorem ncard_primesOver_mul_card_geomInertia (L : LineCover) (t : k) (Q : Ideal (Bring L.M)) :
    ((placeP t).primesOver (Bring L.M)).ncard * Nat.card (geomInertia L.M Q) = Nat.card L.deck
```

(`RET/GeomFundamental.lean`: the residue degree is one over an algebraically closed constant field,
so `efg = n` collapses to `#places × e = n`).  Read as a statement about subgroups it says the fibre
is the coset space of an inertia group (`RET/TotallyRamified.lean`,
`ncard_primesOver_eq_index`), with the two extremes `geomInertia = ⊤ ↔ #places = 1` and
`geomInertia = ⊥ ↔ #places = deg` — the latter being exactly unbranchedness
(`ncard_primesOver_eq_card_deck_iff_isUnramifiedAt`).  A cover with a single point over some point
of the base therefore has a *cyclic* deck group, so a non-cyclic cover has at least two points over
every point of the base.

Passing to a Galois subcover, a branch point survives exactly when its branch cycle does
(`RET/SubBranchPoint.lean`):

```lean
theorem isUnramifiedAt_sub_iff (h : L.IsInertiaGenAt t σ) :
    (∀ τ : (L.sub E).deck, (L.sub E).IsInertiaAt t τ → τ = 1) ↔ L.subHom E σ = 1
```

so the branch locus of a quotient cover is the set of points whose branch cycle has nontrivial
image.

### The analytic side: the root variety of a complex family is a covering space

`RET/Analytic/RootCover.lean`.  The half of W1 that is *not* GAGA is `exists_cycles`, and that is
why it could be closed: to read branch cycles off a cover one only has to analytify it — pass from
the algebraic cover to the topological covering space of the punctured plane — and then feed the
monodromy representation to the already proven computation of `π₁(ℂ ∖ S)` as a free group.  (GAGA
proper, the construction of an algebraic cover from a topological one, is what `exists_cover` needs,
and is the wall that remains.)

The first brick of that analytification, for an arbitrary monic two-variable complex polynomial
rather than the integer families the Hilbert tree used:

```lean
def rootVariety (P : Polynomial (Polynomial ℂ)) : Set (ℂ × ℂ) := {p | biEval P p = 0}
def rootProj (P : Polynomial (Polynomial ℂ)) : rootVariety P → ℂ := fun q ↦ (q : ℂ × ℂ).1

theorem isCoveringMapOn_rootProj (hP : P.Monic) (hsep : ∀ z ∈ U, (spec P z).Separable) :
    IsCoveringMapOn (rootProj P) U
```

Three ingredients, each of independent use:

* `isClosedMap_rootProj` — over a compact set of the base, Cauchy's root bound applied to the monic
  specializations keeps the roots in a fixed disc, so the projection is proper, hence closed.
* `finite_fiber` — a fibre injects into the root set of a nonzero polynomial.
* `exists_graphChart` / `isLocalHomeomorphOn_rootProj` — at a simple root the `Y`-derivative of the
  family is nonzero, so the derivative of `(z, w) ↦ (z, P(z, w))` is invertible and the inverse
  function theorem straightens the variety onto a horizontal slice; the projection is the resulting
  chart of the variety.

Closed, with finite fibres, and a local homeomorphism is exactly Mathlib's criterion for a covering
map.  The separability hypothesis is the analytic form of unbranchedness: `U` is the complement of
the branch locus.

### The analytic tower, and the branch cycles of an abstract extension of `ℂ(T)`

That first brick has grown into a tower of about two dozen modules under `RET/Analytic/`, and the
comparison it was missing — an identification of the algebraic deck action with the topological
monodromy — is now proven.  The tower, by role:

* the covering space: `RootCover`, `RootFiber`, `RootMonodromy`, `Clopen`, `Connected`,
  `PathConnected`, `Regular`;
* holomorphic root branches and the recognition of a factor from them: `RootSection`, `Growth`,
  `RootBound`, `Extension`, `Coeff`, `Factor`, `Sheet`, `LocalBranches`;
* the deck action written as formulas in the roots: `DeckMonodromy`, `DeckPoly`, `DeckPolyMul`,
  `RationalDeck`, `DeckCycles`;
* presenting an abstract extension by a polynomial family: `ScaledComp`, `IntegralDeck`,
  `ClearDenom`, `DeckClear`, `GaloisCycles`;
* discarding the parameters that were an artefact of that presentation: `Shrink`.

The capstone is a statement about an arbitrary finite Galois extension of `ℂ(T)`, with no polynomial
family in sight:

```lean
theorem exists_branchCycles_of_isGalois (M : Type) [Field M] [Algebra (RatFunc ℂ) M]
    [FiniteDimensional (RatFunc ℂ) M] [IsGalois (RatFunc ℂ) M] :
    ∃ (S : Finset ℂ) (g : Fin (S.card + 1) → (M ≃ₐ[RatFunc ℂ] M)),
      (List.ofFn g).prod = 1 ∧ Subgroup.closure (Set.range g) = ⊤
```

The exceptional set is not an artefact either.  `Shrink.lean` proves that the monodromy group is
unchanged when parameters at which nothing happens are put back into the plane — the induced map
`π₁(ℂ ∖ S) ↠ π₁(ℂ ∖ S')` is surjective for `S' ⊆ S` (`PuncturedSurjective`) and monodromy is
natural in maps of coverings (`Pi1/Topological/MonodromyNat`), so the two monodromy groups agree up
to relabelling the fibre.  Consequently the set can be shrunk to the degeneration locus

```lean
def degenLocus (P : Polynomial (Polynomial ℂ)) : Set ℂ := {z : ℂ | ¬ (spec P z).Separable}
```

and `exists_branchCycles_eq_degenLocus_of_isGalois` delivers the tuple over exactly that set: the
count of branch cycles is an invariant of the family, not of how it was written down.

### The existence direction, topologically: covers of the punctured plane are built

The *topological* half of `exists_cover` is now a theorem, for every finite group, every number of
branch points, and every prescribed enumeration of them.  What is left of `exists_cover` after it
is the algebraization alone.

```lean
theorem exists_cover_of_prodOne_ordered (S : Finset ℂ) {z₀ : ℂ} (hz₀ : z₀ ∈ ((S : Set ℂ))ᶜ)
    (pt : Fin S.card → ℂ) (hrange : Set.range pt = (S : Set ℂ))
    {H : Type} [Group H] [Finite H] (h : Fin S.card → H)
    (hprod : (List.ofFn h).prod = 1) (hgen : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (δ : Fin S.card → FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩) (loopInf : …) (D : MonodromyData …),
      (∀ i, IsPunctureLoop ((S : Set ℂ))ᶜ (pt i) hz₀ (δ i)) ∧
        IsSupportedAtInfinity ((S : Set ℂ))ᶜ hz₀ loopInf ∧
        IsCoveringMap D.proj ∧ PathConnectedSpace D.Total ∧ Function.Injective D.deckHom ∧
        (∀ y z, D.proj y = D.proj z → ∃ a : H, D.deck a y = z) ∧
        (∀ i s, monodromy along (δ i) = translation by (h i)) ∧
        (∀ s, monodromy along loopInf = id)
```

Everything in the conclusion is an honest covering space: a covering map with path-connected total
space on which `H` acts freely and transitively over each point of the region, with monodromy `h i`
around the `i`-th prescribed puncture and trivial monodromy at infinity.

Three ingredients, in the order they were built.

* **Prescribing a homomorphism on the puncture loops** (`Pi1/FreeQuotient.lean`,
  `Pi1/Topological/PunctureHom.lean`).  `π₁(ℂ ∖ S)` is free of rank `|S|` and the puncture loops
  generate it, so they are as many generators as the rank — but a generating family of that size
  need not be a *basis*, and the Hopf property of free groups, which would supply that, is not in
  Mathlib.  It is not needed: the target `H` is finite, so `(G →* H)` and `(FreeGroup (Fin r) →* H)`
  both have `|H| ^ r` elements, and precomposition with the surjection `FreeGroup.lift γ` is
  injective, hence surjective (`exists_monoidHom_apply_eq`).  Every prescription of the values on
  the loops is therefore realized.  Product-one makes the remaining generator — the loop at
  infinity — go to the identity, and generation makes the homomorphism surjective, which is what
  makes the cover connected.
* **The cover from a homomorphism** (`Pi1/Topological/CoverExistence.lean`).  `MonodromyData.ofHom`
  builds the cover of a region attached to a surjection of its fundamental group; the ingredients
  proved earlier — covering map, path-connectedness of the total space, freeness and transitivity
  of the deck action, and the identification of the monodromy with the homomorphism — assemble into
  `exists_cover_of_prodOne`.
* **Naming the punctures in advance** (`Pi1/Topological/PunctureConj.lean`, `PunctureOrder.lean`,
  `CoverOrdered.lean`).  A system of loops carries its own enumeration of the punctures, the order
  in which their product is read, and the ordered product is not order-blind in a non-abelian
  group.  The prescribed tuple is therefore first moved, inside its braid class, into the order the
  loops provide (`Rigidity.exists_braidConj_perm`, already proven for the Hurwitz action); the
  values on the loops are then conjugates of the prescribed ones, and conjugating a loop — which
  leaves it a loop around the same puncture, since transport along a loop is conjugation by it
  (`IsPunctureLoop.conj`) — makes them equal.

The inertia clause comes for free: `π₁` of a punctured disc is infinite cyclic and the puncture loop
generates it, so the image of the local fundamental group under the monodromy is exactly
`Subgroup.zpowers (h i)` (`Pi1/Topological/PunctureInertia.lean`, `range_localHom`,
`exists_hom_punctureLoops_ordered_inertia`) — the topological form of `IsInertiaGenAt`, the
distinguished inertia clause that `GeomRETExistence` asks for.

So the wall is now exactly one step wide: the passage from this covering space to a finite extension
of `ℚ̄(T)` — a complex structure on the total space, the local normal form `w ↦ wᵉ` filling the
punctures in, and the existence of enough meromorphic functions on the compactification to separate
the sheets (Grauert–Remmert), followed by the descent of the resulting cover from `ℂ` to `ℚ̄`.

### The algebraization of a covering, and the wall named once

The rest of that step — everything except the meromorphic functions themselves — is proven.  For an
arbitrary covering `f : Y → ℂ` with range the complement of a finite set `S`, connected total space,
and a finite group `H` acting on `Y` over the base (`IsOverBase`) and transitively on each fibre,
the modules `Analytic/CoverHolo.lean`, `Moderate.lean`, `Identity.lean`, `CoverRing.lean`,
`FixedSubring.lean`, `CoverAlgebraic.lean`, `PunctureEquation.lean`, `BaseAlgebra.lean`,
`BaseField.lean` and `Separating.lean` build:

* `coverRing hf S`, the holomorphic functions of moderate growth on `Y`, a subring of the functions
  on the total space; it is a domain when `Y` is connected (`coverRing_isDomain`, by the identity
  theorem), and `H` acts on it by ring automorphisms (`coverRingAction`);
* the invariants: a function of moderate growth fixed by `H` descends to the punctured plane, is
  holomorphic there, and its growth conditions at the punctures and at infinity make it meromorphic
  on the sphere, hence rational — so the fixed field is exactly `ℂ(T)`;
* the correspondence: as soon as every nontrivial deck transformation moves some function of the
  ring (`faithfulSMul_coverRing`), the fraction field of `coverRing hf S` is a Galois extension of
  `ℂ(T)` with `H` as Galois group and degree `|H|` (`isGalois_ratFunc_coverRing`,
  `mulEquivAlgEquiv_ratFunc_coverRing`, `finrank_ratFunc_coverRing`, assembled in
  `exists_isGalois_ratFunc_of_forall_ne`).

That leaves one requirement, and `Analytic/Wall.lean` names it once and for all coverings:

```lean
def HasEnoughFunctions : Prop :=
  ∀ (S : Finset ℂ) (Y : Type) [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y]
    (q : Y → ↥((S : Set ℂ)ᶜ)), IsCoveringMap q →
      ∀ hf : IsLocalHomeomorph fun y => ((q y : ℂ)),
        Set.range (fun y => ((q y : ℂ))) = (↑S : Set ℂ)ᶜ →
      ∀ (H : Type) [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y] [FaithfulSMul H Y]
        [IsOverBase H fun y => ((q y : ℂ))],
        (∀ y y' : Y, (q y : ℂ) = (q y' : ℂ) → ∃ b : H, y' = b • y) →
        ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y
```

Two of those hypotheses were absent when the requirement was first written down, and without either
of them it is not merely unproven but **false** — which would have made the theorems below vacuous.
The action must be faithful: any group at all acts on the plane by doing nothing, transitively on
the fibres of the identity covering, and its nontrivial elements move no function whatever
(`Analytic/WallSharp.lean`, `not_hasEnoughFunctionsUnfaithful`, which needs `isCoveringMap_id` —
absent from Mathlib — as a lemma).  And the projection must be a covering, not merely a local
homeomorphism onto the punctured plane: take the plane punctured at `S`, double one further point
`z₁` (the non-Hausdorff quotient of `↥X × Bool` that glues `(z, false)` to `(z, true)` for `z ≠ z₁`)
and let `ℤ/2` swap the two copies (`Analytic/DoublePoint.lean`, `not_hasEnoughFunctionsNonCovering`).
That is a connected local homeomorphism onto `Sᶜ` with a faithful transitive `ℤ/2`-action, and every
function of the ring — indeed every continuous function — takes equal values at the two copies of
`z₁`, since the two sheets agree on the complement of a point, which is dense.  Both hypotheses come
for free at the use site: `exists_cover_of_prodOne_ordered` delivers the covering itself and the
injectivity of `deckHom`.

The stronger-looking form `HasSeparatingFunctions` — one function of moderate growth taking distinct
values at *all* the points of one fibre — is the same statement
(`hasSeparatingFunctions_iff_hasEnoughFunctions`, `Analytic/Combine.lean`).  Choosing for each
nontrivial `c` a function `F_c` that it moves, the differences `F_c − c⁻¹ · F_c` are nonzero
elements of a domain, so are all of their translates, so is their product, and any point where the
product does not vanish sees every `F_c` moved by its own `c` along the whole fibre through it
(`exists_forall_smul_ne`).  A linear combination `∑_c t^{e(c)} F_c` then separates that fibre for
all but finitely many `t`: the failures are the roots of a nonzero polynomial, whose coefficient at
`X^{e(ab⁻¹)}` records that `F_{ab⁻¹}` distinguishes `a` from `b`
(`hasSeparatingFunction_of_forall_ne`).

The statement is not vacuous: the power covering `w ↦ wⁿ` of the plane punctured at the origin
carries it, with the coordinate of the total space — a continuous, hence holomorphic, branch of the
`n`-th root (`analyticAt_of_pow_eq`, `isHolo_kummer_val`, `isModerate_kummer_val`,
`hasSeparatingFunction_kummer`) — as the separating function, and the correspondence then produces
the Kummer extension out of the topology alone (`exists_isGalois_ratFunc_rootsOfUnity`).

Granting it, the existence direction over `ℂ(T)` follows in full: a generating product-one tuple in
a finite group is the monodromy of a covering (`exists_cover_of_prodOne_ordered`), the covering has
a function field Galois over `ℂ(T)` with that group (`exists_isGalois_ratFunc_of_prodOne`), and
every finite group carries such a tuple (`exists_prodOne_generating`), so

```lean
theorem exists_isGalois_ratFunc (hwall : HasEnoughFunctions) (H : Type) [Group H] [Finite H] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℂ) L),
      IsGalois (RatFunc ℂ) L ∧ Nonempty (H ≃* (L ≃ₐ[RatFunc ℂ] L)) ∧
        Module.finrank (RatFunc ℂ) L = Nat.card H
```

— every finite group is a Galois group over `ℂ(T)`, of degree its order, branched over prescribed
points.  What separates this from the repository's remaining `sorry` is not the analysis but the
arithmetic: `geomRETExistence_of_injective` asks for the cover over `ℚ̄`, packaged as a `LineCover`
and carrying the prescribed inertia generators, so Lefschetz descent from `ℂ` to `ℚ̄` and the
inertia clause still stand between the two.

### What the requirement asks is that coverings are cut out by equations

The requirement is stated as a property of *functions*, but it is a property of the covering, and
the equivalence is a theorem in both directions.

**A covering that comes from an equation satisfies it, for the cheapest of reasons.**  On the root
variety `RootTotal P S` of a monic `P ∈ ℂ[T][X]`, the second coordinate `rootCoord` is holomorphic
(`isHolo_rootCoord`) and of moderate growth by the Cauchy bound on the roots of a monic polynomial
(`isModerate_rootCoord`), and it separates the fibres *tautologically*: a point of the root variety
**is** its parameter together with its coordinate, so a deck transformation moving no function of
moderate growth fixes every point (`Analytic/RootRing.lean`, `exists_ne_rootCoord`).  Functions of
moderate growth transport along a homeomorphism over the plane
(`Analytic/Transport.lean`, `mem_coverRing_comp_homeo`), so the same holds of any covering merely
homeomorphic over the plane to an algebraic one (`exists_ne_of_homeo_rootTotal`).

**Conversely the requirement produces the equation.**  Three steps, all unconditional:

1. Functions moving the deck transformations one at a time combine into a single function `G`
   separating one fibre (`hasSeparatingFunction_of_forall_ne`, above).
2. `G` then separates *every* fibre over the complement of a finite set
   (`Analytic/GenericSeparation.lean`, `exists_finset_separating`).  The product of the differences
   of its values along a fibre, `sepProd H G y = ∏_{a ≠ b} (G(a·y) − G(b·y))`, is invariant under
   the deck group and of moderate growth (`sepProd_smul`, `sepProd_mem_coverRing`), hence a
   rational function of the base coordinate, and it is not identically zero because the ring of
   functions of a connected covering is a domain (`exists_sepProd_ne_zero`); so it vanishes over
   only the roots of a numerator.
3. Multiplying `G` by the leading coefficient `d` of the equation it satisfies over `ℂ[T]` makes it
   integral; the product `W = d(f y)·G(y)` still separates, away from the roots of `d`, and its
   values along a fibre are then exactly as many roots of a monic polynomial `P` of that degree as
   the polynomial can have — so all of them (`roots_spec_eq_of_separating`), the specialization is
   separable (`separable_spec_of_separating`), and `(f, W)` is a continuous bijection onto the root
   variety, hence a homeomorphism over the plane (`Analytic/AlgebraicModel.lean`,
   `exists_algebraic_model`; capstone `Analytic/Algebraize.lean`,
   `exists_algebraic_model_of_hasEnoughFunctions`).

**The two directions do meet.**  What stood between them was that the algebraization discards
`d.roots`, finitely many further points of the base at which the equation found may degenerate
although the covering does not, whereas the transport of functions needs a model over the whole
punctured plane.  `Analytic/CoverExtend.lean` closes the gap without re-choosing the equation.
Damp the coordinate of the model by `dampPoly S S' = ∏_{s ∈ S' \ S} (X − s)`, a polynomial in the
base coordinate vanishing exactly at the discarded parameters, and extend the product by zero over
the fibres the model does not see (`dampedCoord`).  Three things then hold, and together they say
the damped coordinate is a function of moderate growth on the *whole* covering:

* over a parameter the model keeps it is a product of two holomorphic functions
  (`isHoloAt_dampedCoord_of_mem`);
* over a discarded parameter it is holomorphic by **Riemann's theorem on removable
  singularities** (`isHoloAt_dampedCoord_of_notMem`): in the chart the projection supplies it is
  bounded on a punctured disc, by the Cauchy bound for the roots of a monic family
  (`norm_dampedCoord_le`), so it extends analytically, and the extension takes the value `0`
  prescribed there because the damping factor tends to `0` — the prescribed value is the right one,
  which is why no choice enters the definition;
* the growth conditions are conditions in the base coordinate, and the extension only adds points
  over finitely many parameters (`IsModerate.of_subtype_of_zero`, `isModerate_dampedCoord`).

The damping does not spoil what the function was for: at a parameter outside `S'` the damping
factor is nonzero, so the damped coordinate still distinguishes the points of that fibre, and a
deck transformation of a *connected* covering which is not the identity moves **every** point
(`smul_ne_self_of_ne_one`, from `IsSeparatedMap.eq_of_comp_eq`), in particular one over such a
parameter.  Hence `exists_ne_of_homeo_rootTotal_of_subset`, and with it the equivalence
(`Analytic/Algebraicity.lean`):

```lean
theorem forall_ne_iff_exists_algebraic_model (hf : IsLocalHomeomorph f)
    (hsepmap : IsSeparatedMap f) (htrans : ∀ y y', f y = f y' → ∃ c : H, y' = c • y)
    (hrange : Set.range f = ((S : Set ℂ))ᶜ) :
    (∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) ↔
      ∃ (P : Polynomial ℂ[X]) (S' : Finset ℂ), S ⊆ S' ∧ P.Monic ∧ P.natDegree = Nat.card H ∧
        (∀ z ∉ (S' : Set ℂ), (spec P z).Separable) ∧
        ∃ Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S', ∀ y, rootBase P S' (Φ y) = f (y : Y)

theorem hasEnoughFunctions_iff_allCoveringsAlgebraic :
    HasEnoughFunctions ↔ AllCoveringsAlgebraic
```

Two hypotheses appear in the converse that the forward direction does not need — the projection is
separated, and the total space is connected — and both are properties of a covering of a punctured
plane, so neither costs anything at the level of `HasEnoughFunctions`.  Separatedness is not
decoration: the plane with one point doubled (`Analytic/DoublePoint.lean`) is a local homeomorphism
with a faithful transitive deck group and no separating function whatever, and separatedness is
exactly what it fails.  So the wall is not a statement about functions at all.  It is the single
statement that **every topological covering of a punctured plane is algebraic**, which is GAGA.

**The equation is the minimal polynomial.**  `Analytic/PrimitiveElement.lean` upgrades the model to
a presentation of the function field.  Write `α` for the image of `W` in
`FractionRing (coverRing hf S)` and `Q` for `P` read over `ℂ(T)`.  Then `minpoly ℂ(T) α ∣ Q`, so
its degree is at most `n = |H|`; and the `n` translates `a · α` are *distinct* elements of the
function field (`smul_algebraMap_coverRing` plus injectivity of `algebraMap` into the fraction
field) and all of them roots of that minimal polynomial, so its degree is at least `n`.  The bounds
meet: `minpoly ℂ(T) α = Q`, which is therefore irreducible, and `ℂ(T)⟮α⟯ = ⊤` because the degree of
the function field over `ℂ(T)` is also `|H|` (`finrank_ratFunc_coverRing`).  So

```lean
theorem exists_algebraic_model_primitive … :
    ∃ (P : Polynomial ℂ[X]) (S' : Finset ℂ), S ⊆ S' ∧ P.Monic ∧ P.natDegree = Nat.card H ∧
      (∀ z ∉ (S' : Set ℂ), (spec P z).Separable) ∧
      (∃ Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S', ∀ y, rootBase P S' (Φ y) = f (y : Y)) ∧
      Irreducible (P.map (algebraMap ℂ[X] (RatFunc ℂ))) ∧ …
```

— one and the same `P` gives the homeomorphism and presents the Galois extension.  Granting the
requirement for every covering at once, `Analytic/PrimitiveGroup.lean` sharpens
`exists_isGalois_ratFunc` from an abstract field to an explicit polynomial:

```lean
theorem exists_polynomial_isGalois_ratFunc (hwall : HasEnoughFunctions) (H : Type) [Group H]
    [Finite H] :
    ∃ P : Polynomial ℂ[X], P.Monic ∧ P.natDegree = Nat.card H ∧
      Irreducible (P.map (algebraMap ℂ[X] (RatFunc ℂ))) ∧
      ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℂ) L), IsGalois (RatFunc ℂ) L ∧
        Nonempty (H ≃* (L ≃ₐ[RatFunc ℂ] L)) ∧
        ∃ α : L, aeval α (P.map (algebraMap ℂ[X] (RatFunc ℂ))) = 0 ∧
          IntermediateField.adjoin (RatFunc ℂ) {α} = ⊤
```

What is still missing between this and `geomRETExistence_of_injective` is unchanged: the
coefficients are complex numbers and the statement says nothing about the branch cycles, so the
Lefschetz descent from `ℂ` to `ℚ̄` and the inertia clause both remain.

### 2.4 How `exists_cycles` was closed

`GeomRETCompleteness t` asks for more than a product-one generating tuple.  For a prescribed tuple
of points `t : Fin r → ℚ̄` it asks for `g : Fin r → L.deck` with `IsInertiaGenAt (t i) (g i)`,
generating, and with product one **in the prescribed order**.  Four things were missing, and all
four are now theorems:

1. **`ℚ̄` versus `ℂ`.**  The tower lives over `ℂ`; a `LineCover` lives over `ℚ̄`.  **Closed**, and
   without any Lefschetz statement: the comparison is only ever needed in the *easy* direction.  An
   embedding `ℚ̄ ↪ ℂ` exists by `IsAlgClosed.lift` and is all that is used — the equation of the
   cover is complexified (`complexEquation`, `RET/Analytic/DeckData.lean`), the analytic tower is
   run on the complexified equation, and the resulting automorphisms are pulled back along the
   deck-group isomorphism `RationalDeck`.  No cover has to be descended from `ℂ` to `ℚ̄`; that is
   the operation the *existence* direction needs, and the reason it is still open.
2. **Matching the index sets.**  The tuple produced by the free-group presentation is indexed by
   nothing in particular.  **Closed** — the spider, below.
3. **Localizing the group elements.**  Nothing says that the element attached to a point is an
   inertia generator *at that point*: that is a local comparison between the analytic monodromy of
   a small loop and the algebraic inertia group of a place.  **Closed** — Puiseux, below.
4. **The order of the product.**  Product-one holds for the tuple that the free-group presentation
   happens to produce, not for a prescribed ordering of the points.  **Closed** — the rectangle
   spider, plus item 3 applied at infinity, below.

The assembly is `RET/Local/ProdOneGeneration.lean`:
`LineCover.exists_isInertiaGenAt_prodOne` produces, over any finite set of points containing the
prescribed ones, a list of distinguished inertia elements — one above each point, plus a last entry
for the loop at infinity — generating the deck group, with ordered product the identity and with
that last entry trivial; `exists_isBranchCycleGenSystem_of_last_eq_one` then reorders and cuts the
list down to the prescribed points by the Hurwitz moves of `RET/BranchCycleReduce.lean`.

#### Item 2: the spider

`Pi1/Topological/Spider.lean` rebuilds the van Kampen induction so that it **does** track which
puncture each generator surrounds:

```lean
theorem exists_punctureLoops_compl {S : Set ℂ} (hS : S.Finite) {z₀ : ℂ} (hz₀ : z₀ ∈ Sᶜ) :
    ∃ γ : ℂ → FundamentalGroup ↥(Sᶜ) ⟨z₀, hz₀⟩,
      (∀ s ∈ S, IsPunctureLoop Sᶜ s hz₀ (γ s)) ∧ Subgroup.closure (γ '' S) = ⊤
```

One loop per puncture, each winding once around its own puncture, and together they generate.
`eq_top_of_isPunctureLoop_mem` is the form used in practice: a subgroup containing every puncture
loop is everything.

Feeding that into the analytic tower gives the *localized* branch-cycle theorem, which is the
tuple of §2 with each entry attached to the puncture it belongs to
(`Analytic/GaloisLocalCycles.lean`):

```lean
theorem exists_localizedBranchCycles_of_isGalois (M : Type) [Field M] [Algebra (RatFunc ℂ) M]
    [FiniteDimensional (RatFunc ℂ) M] [IsGalois (RatFunc ℂ) M] :
    ∃ (P : Polynomial (Polynomial ℂ)) (S : Finset ℂ) (z₀ : ℂ) (hz₀ : z₀ ∉ (S : Set ℂ)),
      P.Monic ∧ (∀ z ∉ (S : Set ℂ), (spec P z).Separable) ∧
        ∃ (Φ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩ →* (M ≃ₐ[RatFunc ℂ] M))
          (γ : ℂ → FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩),
          Function.Surjective Φ ∧
            (∀ s ∈ degenLocus P, IsPunctureLoop ((S : Set ℂ)ᶜ) s hz₀ (γ s)) ∧
              Subgroup.closure ((fun s => Φ (γ s)) '' degenLocus P) = ⊤
```

The whole Galois group of an arbitrary finite Galois extension of `ℂ(T)` is a quotient of the
fundamental group of a punctured plane, generated by the images of loops around the *individual*
punctures.  `Analytic/Presentation.lean` isolates the input (every such extension is presented by a
monic family over `ℂ[T]`), so the statement mentions no polynomial.

What the local model alone cannot give is recorded here because it looks tempting:
`eq_zero_of_prod_zpow_eq_one` (`PunctureLocal.lean`) says loops around distinct punctures are
independent in the abelianization, i.e. they are a basis of `H₁`.  That is strictly weaker than
being a *free basis*: in `F₂` the pair `a, b[a,b]` is a basis of the abelianization and still
generates a proper subgroup.  Generation is genuinely geometric, and is what the spider induction
supplies.

#### Item 4: the rectangle spider, and the loop at infinity

The prescribed-order product-one relation is the *sphere* relation, and `ℂ ∖ S` is the sphere minus
`S ∪ {∞}`.  Writing `γ₁, …, γ_r` for the spider loops and `c` for a large loop, the two halves are

* **(4a, topological)** `γ₁ ⋯ γ_r = c` in `π₁(ℂ ∖ S)` for a suitable ordering of the spider.  This
  is `RET/Pi1/Topological/RectInduction.lean`: the van Kampen induction is run on *rectangles*, and
  each stage carries its boundary loop, so the boundary of a rectangle containing every puncture is
  exhibited as the ordered product of one loop per puncture (`exists_rectSpider_compl`).  Appending
  the inverse of the boundary loop as a last generator turns the product into the identity without
  disturbing generation (`exists_punctureLoops_prodOne_compl`, `PlaneSpider.lean`).  No Hopf
  property and no free-basis statement is needed.
* **(4b, analytic)** `Φ c = 1`, because the cover is unramified at infinity.  The rectangle is
  chosen with all four of its sides outside a disc containing every puncture, so its boundary loop
  is *supported at the point at infinity* (`IsSupportedAtInfinity`, `ExteriorLoop.lean`): it is
  transported from a loop of an exterior region `‖z‖ > R`.  On such a region the loop at infinity
  generates, and item 3 applied to the twisted cover at `0` names it as the identity
  (`deckCycle_eq_one_of_isSupportedAtInfinity`, `RET/Local/InfinityElement.lean`).

So the analytic content of items 3 and 4 is a *single* statement, applied at the finite branch
points and at infinity — exactly as it was predicted to be, and now proven at both.

#### Item 3: how the local comparison was made

Let `M/ℂ(T)` be finite Galois with group `G`, let `s ∈ ℂ`, and let `σ = Φ (γ s)` be the monodromy of
a small loop around `s`.  Wanted: a place `Q` of the integral model over `T = s` with
`geomInertia M Q = Subgroup.zpowers σ`.

The route that fails is counting.  The deck group acts transitively on the places over `s` with
stabilizer the inertia group (residue fields algebraically closed, so decomposition = inertia —
`InertiaGen.lean`), so `#places = |G| / e_Q`; the fibre of the analytic cover is a `G`-torsor, so
the `⟨σ⟩`-orbits on it are the cosets of `⟨σ⟩` and `#orbits = |G| / orderOf σ`.  An equivariant map
{orbits} → {places} is cheap, but the counting argument for its injectivity is circular: it assumes
the equality of the two counts it is meant to produce.  Injectivity says that two distinct analytic
branches at `s` are separated by the integral closure — the analytic normalization agrees with the
algebraic one — and no amount of counting supplies it.

The route that works produces the place *from the branch*, so that no injectivity is ever needed.
A holomorphic branch of the roots on a punctured disc in the Kummer coordinate `T = s + wᵉ` is
bounded (`Analytic/RootBound.lean`), hence extends smoothly across the puncture
(`Local/KummerGerm.lean`), and its Taylor series is a formal root of the family in the Kummer
coordinate.  `Local/PuiseuxAssembly.lean` recognises that datum for what it is: a **Puiseux
parametrisation** of the cover, i.e. an embedding of `M` into a field of Puiseux series over `s`,
which *is* a place of the integral model — `exists_puiseuxEmbedding_of_branch`.  Rotating the
Kummer coordinate `w ↦ ζw` is realized by an automorphism of the extension, of exactly the order of
the rotation (`Analytic/GermInertia.lean`), and that automorphism is an inertia element at `s`
(`LineCover.exists_isInertiaAt_of_branch`, `Local/BranchInertia.lean`).  Matching its order against
the order of the monodromy of the circle (`Local/BranchGeneration.lean`) upgrades it from *an*
inertia element to a *generator*, and `Local/BranchElement.lean` assembles the statement wanted:

```lean
theorem LineCover.isInertiaGenAt_deckCycle …
    (hloop : IsPunctureLoop ((S : Set ℂ)ᶜ) (algebraMap k ℂ s) hz₀ γ) :
    L.IsInertiaGenAt s (RD.deckCycle … e₀ γ)
```

— the name of a loop encircling a single parameter generates the inertia group above that
parameter.  This is the local analytic-algebraic dictionary, and it was built rather than assumed.

#### Also built along the way

* `Pi1/Topological/GroupLoop.lean` — in a topological monoid the pointwise product of two loops at
  the unit is homotopic to their concatenation (`homotopic_loopMul`, by the explicit
  reparametrisation `H(s,t) = α(min((1+s)t, 1)) · β(max((1+s)t − s, 0))`), hence the pointwise
  `n`-th power of a loop is the `n`-th power of its class (`fromPath_loopPow`) and the `n`-th power
  map of the monoid acts as the `n`-th power map on `π₁` at the unit (`mapOfEq_npowMap`).
* `Pi1/Topological/UnitsDegree.lean` — the instance at `ℂˣ`: `π₁(ℂˣ, 1) ≅ ℤ`
  (`fundamentalGroupUnitsOne`) and `z ↦ zⁿ` multiplies the winding number by `n`
  (`windingNumber_npowMap`).  This is the local degree computation every Kummer comparison needs.
* `Analytic/Pullback.lean` — the Kummer substitution `T = s + wᵉ` as a morphism of root covers.
  `pullFam P s e := P.map (eval₂RingHom C (C s + X ^ e))` has `spec (pullFam P s e) w = spec P
  (s + wᵉ)`, its degeneration locus is the preimage of that of `P`, and the substitution lifts to a
  map of the punctured root covers (`pullBase`, `pullTotal`, `puncturedProj_pullTotal`) with a
  bijection on fibres (`pullFibre`).  Naturality of monodromy (`Pi1/Topological/MonodromyNat.lean`)
  then gives the square

  ```lean
  theorem monodromyHom_comp_map_pullBase … :
      (monodromyHom hP hS _).comp (FundamentalGroup.map (pullBase s e hbase) _)
        = (Equiv.permCongrHom (pullFibre P s e hbase hw₀)).toMonoidHom.comp
            (monodromyHom (monic_pullFam hP s e) (separable_spec_pullFam hS hbase) hw₀)
  ```

  and the containment of monodromy groups `range_monodromyHom_pullFam_le`.  Combined with the degree
  engine this is the statement that the local monodromy of the pullback at `w = 0` is `σᵉ`, the
  first step of the Abhyankar argument.

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
at the punctures matching the loops.*  Half of that sentence — the **completeness** half, that every
algebraic cover with a prescribed branch locus is named by loops, with its branch cycles generating
and multiplying to one in the prescribed order — is now a **theorem**, for every finite group and
every number of branch points (`geomRETCompleteness_of_injective`).  What the rigidity tree still
assumes is the other half alone: **existence**, the passage from a topological cover to an algebraic
one — and only that passage, because the topological cover itself is now built, for every finite
group and every prescribed set of branch points, with the prescribed monodromy at them and trivial
monodromy at infinity (`exists_cover_of_prodOne_ordered`).

And it is assumed only where it has to be.  The whole sentence, existence included, is *proven*
with no hypothesis on the group for `r ≤ 2` (`geomRET_of_le_two`) — the once-punctured sphere is
simply connected and the twice-punctured one has cyclic fundamental group, algebraically — and it is
proven for every `r` when the deck group is abelian (`geomRETComm`).  The branch data has been
stripped of everything inessential: trivial branch cycles may be added and removed, the points may
be permuted along with their cycles, and — by Möbius transport — *where* the three points of a
three-point datum sit does not matter at all, so W1 in the rigidity regime is one statement rather
than a moduli of them.  Over such a triple the first non-abelian instance of `exists_cover` is
proven outright, for every dihedral group.  What is left is one regime and one clause in it: the
existence of a cover with prescribed non-abelian monodromy over three or more branch points.  That
is the regime the rigidity method lives in, and it is the regime in which the correspondence
genuinely sees the topology.

Everything else is a theorem.  The arithmetic half — the branch-cycle rationality descent from
`ℚ̄(T)` to `ℚ(T)`, the whole of §3 — is proven from W1, rung by rung: the branch locus of the
arithmetic Galois closure is bounded (rungs 3, 4), its branch cycles are read off by `exists_cycles`
(rung 1, now unconditional), pushed down to arithmetic inertia (rung 5), given a model carrying the
right roots of unity (rung 6b), and matched against the certificate by rigidity (rung 6a).  From
there Fried's branch-cycle formula, the centerless extension lemma and Hilbert irreducibility — all
already proven — give `rigidity_realizable`.

So the statement of the whole development is now: *the existence direction of the Riemann Existence
Theorem over `ℚ̄` implies the rigidity criterion for the Inverse Galois Problem*, formalized, with
the implication itself carrying no assumption, and with the completeness direction supplied rather
than assumed.  Closing what is left needs analytification and coherent-sheaf GAGA (§2); that is the
remaining work, and it is of a different kind from everything above.

Over `ℂ` the shape of that remaining work is now visible in one line.  The covering space is built,
the ring of functions of moderate growth on it is a domain with the deck group acting by ring
automorphisms, the invariants are the rational functions of the base coordinate, and faithfulness
turns the fraction field into a Galois extension of `ℂ(T)` with the deck group as Galois group.  The
only thing not proven is that the ring is big enough to be faithful — `HasEnoughFunctions`,
equivalently `HasSeparatingFunctions` — and granting it, every finite group is a Galois group over
`ℂ(T)` of degree its order, branched over prescribed points (`exists_isGalois_ratFunc`).  Producing
a single nonconstant function of moderate growth on an abstract covering is where the transcendence
sits: it is a `∂̄`-problem, and Mathlib has neither the Cauchy–Pompeiu formula nor any other means
of solving one.
