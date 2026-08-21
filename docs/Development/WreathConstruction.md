# The wreath-product engine, designed against this repository

*Design study.  No Lean was written or changed for this document; every declaration quoted below
was read out of the tree at the file and line given.*

**Goal.** An engine
`H` realizable ⟹ `A ≀ᵣ H` realizable (`A` finite abelian), so that
`InverseGalois/Solvable/Wreath.lean` turns it into every semidirect product `A ⋊[φ] H`, and
iteration turns it into every finite **semiabelian** group (Ikeda / Kisilevsky–Neftin–Sonn).

---

## 0. Verdict up front

* **Recommended target:** *one variable, regular, over `ℚ(T)`* —
  `IsRegularInverseGalois H → IsRegularInverseGalois (A ≀ᵣ H)`.
  This is stronger than the non-regular one-variable statement, and — decisively — it needs **no
  new Hilbert irreducibility theorem**: `IsRegularInverseGalois.isInverseGalois`
  (`Rigidity/RET/Specialization.lean:1107`) is already proved.  The non-regular route is blocked
  behind a HIT for a *not absolutely irreducible* polynomial, which does not exist in the tree
  (`Hilbert/HilbertIrreducibility.lean:423` demands `hf_abs_irr`).
* **Recommended construction — "route δ":** keep the abelian layer as a **black box**
  (`IsRegularInverseGalois.of_commGroup`, `Rigidity/RET/AbelFinale.lean:73`) and pull it back along
  the `|H|` conjugates `λ·h(θ) + c` of a primitive element `θ` of the `H`-extension, with `(λ, c)`
  generic.  Independence of the `|H|` pulled-back layers is proved by **inertia at one fibre**, not
  by disjointness of branch loci and not by Kummer divisor arithmetic.
* **The base field does *not* need to be quantified.**  Contrary to the framing in the task update,
  the induction closes over `ℚ` alone: the abelian input is already available over `ℚ`
  (`of_commGroup`), the `H`-input is over `ℚ`, and *all* ramification bookkeeping happens after
  base change to `ℚ̄`, where the repository's entire geometric stack lives.  `ℚ(ζₙ)` never appears.
  (`IsRegularGaloisGroupOver K G` *is* base-general if it is ever wanted; see §2.)
* **Roots of unity are a non-issue in route δ** (§6.1) and **cyclic kernels buy nothing** (§6.2):
  general finite abelian `A` costs exactly the same, because `A` enters only through the black box.
* **Effort:** ≈ 3 000 – 3 500 lines, 5–8 focused sessions.  One file (F5, pullback inertia) carries
  most of the risk.

---

## 1. Inventory

### 1.1 Realization predicates

| Predicate | Location | Statement |
|---|---|---|
| `IsInverseGalois G` | `Core/Basic.lean:29` | `∃ L/ℚ` finite Galois with `Gal(L/ℚ) ≃* G` |
| `IsRegularGaloisGroupOverBase k F G` | `Rigidity/RET/Statement.lean:66` | see below |
| `IsRegularGaloisGroupOver K G` | `Statement.lean:81` | `= IsRegularGaloisGroupOverBase K (RatFunc K) G` |
| `IsRegularInverseGalois G` | `Statement.lean:91` | `= IsRegularGaloisGroupOver ℚ G` |
| `IsGeometricGaloisCover G` | `Rigidity/RET/Existence.lean:91` | Galois ext. of `GeomFunctionField = RatFunc ℚ̄` with group `G` |

```lean
def IsRegularGaloisGroupOverBase (k : Type*) [Field k] (F : Type*) [Field F] [Algebra k F]
    (G : Type*) [Group G] : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L) (_ : IsGalois F L)
    (_ : Algebra k L) (_ : IsScalarTower k F L),
    algebraicClosure k L = ⊥ ∧ Nonempty ((L ≃ₐ[F] L) ≃* G)
```

Transport lemmas that exist and are base-general:
`IsRegularGaloisGroupOverBase.of_mulEquiv` (`Statement.lean:115`),
`IsRegularGaloisGroupOverBase.of_algEquiv` (`Rigidity/RET/Descent/BaseTransfer.lean:41`,
replaces the base by any `k`-isomorphic field),
`Rigidity.RET.Descent.algebraicClosure_ratFunc (K : Type*) [Field K] :
algebraicClosure K (RatFunc K) = ⊥` (`Descent/RegularBase.lean:34`).

### 1.2 The geometric layer

Everything geometric is phrased against `LineCover` (`Rigidity/RET/TamePi1.lean:47`), a finite
Galois extension of `RatFunc k` *together with* the integral structure over `Polynomial k`:

```lean
structure LineCover where
  M : Type
  [field : Field M]
  [alg : Algebra (RatFunc k) M]
  [algPoly : Algebra (Polynomial k) M]
  [tower : IsScalarTower (Polynomial k) (RatFunc k) M]
  [findim : FiniteDimensional (RatFunc k) M]
  [isGalois : IsGalois (RatFunc k) M]

abbrev deck (L : LineCover) : Type := L.M ≃ₐ[RatFunc k] L.M
```

and **`k` is fixed**: `abbrev k : Type := AlgebraicClosure ℚ` (`Descent/GeomAKLB.lean:43`).  So the
whole `LineCover` toolkit is `ℙ¹` over `ℚ̄`, no other base curve and no other constant field.  The
one general-constant-field variant, `Descent/AKLBGen.lean:50`, still assumes `[IsAlgClosed κ]` and
still has base `Polynomial κ`; its own docstring says the two key results
(`inertia_eq_stabilizer:159`, `card_inertia:179`) *fail* over a non-closed constant field.

Inertia is a genuine `Subgroup`:

```lean
abbrev geomInertia (Q : Ideal (Bring Ω)) : Subgroup (Ω ≃ₐ[RatFunc k] Ω) :=
  Q.inertia (Ω ≃ₐ[RatFunc k] Ω)                      -- Descent/GeomAKLB.lean:138
def IsInertiaAt (L : LineCover) (t : k) (σ : L.deck) : Prop :=
  ∃ Q : Ideal (Bring L.M), Q.IsMaximal ∧ Q.LiesOver (placeP t) ∧ σ ∈ geomInertia L.M Q
```

`Ideal.inertia`, `Ideal.ramificationIdx`, `Ideal.ramificationIdxIn`, `Ideal.ramificationIdx_tower`
(`Mathlib/NumberTheory/RamificationInertia/Basic.lean:979`) are Mathlib-general — the restriction to
`ℙ¹/ℚ̄` is the repository's, not Mathlib's.  That matters for F5 below.

The bridge in both directions between the predicate and the structure:
`isGeometricGaloisCover_iff_exists_lineCover` (`Rigidity/RET/ProductGeometric.lean:43`).

### 1.3 Branch loci, unramifiedness, and "unramified ⇒ trivial"

```lean
def IsUnramifiedOutside (L : LineCover) (S : Set k) : Prop :=      -- Unramified.lean:49
  ∀ t ∉ S, ∀ σ : L.deck, L.IsInertiaAt t σ → σ = 1
def IsUnramifiedAtInfinity (L : LineCover) : Prop :=               -- Twist.lean:170
  ∀ σ : (L.twist invSubst.toRingEquiv).deck,
    (L.twist invSubst.toRingEquiv).IsInertiaAt 0 σ → σ = 1
def branchLocus (L : LineCover) : Set k :=                          -- BranchSet.lean:76
  {t : k | ∃ σ : L.deck, σ ≠ 1 ∧ L.IsInertiaAt t σ}
def IsAffineDeckGroup (n : ℕ) (G : Type) [Group G] [Finite G] : Prop :=   -- MoveInfinity.lean:221
  ∃ L : LineCover, Nonempty (L.deck ≃* G) ∧ L.branchLocus.ncard ≤ n
def IsDeckGroupOver (S : Set k) (G : Type) [Group G] [Finite G] : Prop := -- DeckGroups.lean:49
  ∃ L : LineCover, Nonempty (L.deck ≃* G) ∧ L.IsUnramifiedOutside S ∧ L.IsUnramifiedAtInfinity
```

* every cover has a finite branch locus: `LineCover.exists_unramifiedOutside_finite`
  (`BranchLocus.lean:107`), `_range` (`:136`) — so a branch locus never has to be prescribed;
* `subsingleton_deck_of_unramifiedOutside_zero` / `_singleton`
  (`TranslateInfinity.lean:440`, `:453`) — a cover unramified outside one point **and at
  infinity** is trivial; the `_empty` version is the `π₁(𝔸¹) = 1` statement;
* **the disjointness workhorse** (§4.2), with *no* infinity hypothesis:

```lean
theorem LineCover.inf_eq_bot_of_disjoint' (L : LineCover)
    (A B : IntermediateField (RatFunc k) L.M) [Normal (RatFunc k) A] [Normal (RatFunc k) B]
    {S₁ S₂ : Set k} (hdisj : Disjoint S₁ S₂)
    (hA : (L.sub A).IsUnramifiedOutside S₁) (hB : (L.sub B).IsUnramifiedOutside S₂) :
    A ⊓ B = ⊥                                          -- ProductTranslate.lean:114
```
  (the variant with `IsUnramifiedAtInfinity` is `SubcoverBranch.lean:112`);
* `IsDeckGroupOver.prod` (`Product.lean:43`) is the packaged two-factor version;
  `exists_translate_disjoint` and `IsDeckGroupOver.translate` (`ProductTranslate.lean`) are the
  genericity precedent reused in F4;
* the inertia groups of a cover of `ℙ¹` **generate** the deck group:
  `exists_places_iSup_geomInertia_eq_top_of_comm` (`AbelianGeneration.lean:334`) for abelian
  deck groups — this is the fact route δ needs (§4.4, step 4).

### 1.4 Compositum, linear disjointness, deck group of a compositum

* `Rigidity/RET/Compositum.lean`: `LineCover.closure := AlgebraicClosure (RatFunc k)`, `embed`,
  `image`, `imageEquiv`, `compositum`, `compositumLeft/Right`, `compositumLeft_sup_compositumRight`.
* `LineCover.nonempty_deck_mulEquiv_prod (L) (A B) (hsup : A ⊔ B = ⊤) (hbot : A ⊓ B = ⊥)`
  (`SubcoverProduct.lean:71`) — the deck group of a cover generated by two linearly disjoint normal
  subcovers is the product.  **This is the two-factor case of what F6 needs for `|H|` factors.**
* Mathlib: `IntermediateField.LinearDisjoint.of_inf_eq_bot` (needs `[IsGalois F A]`),
  `.finrank_sup`, `.of_finrank_coprime`, `.of_isField'`
  (`Mathlib/FieldTheory/LinearDisjoint.lean:452, 412, 608, 644`).
* The **arithmetic** analogue to imitate is `Rigidity/RET/RegularProduct.lean`: embed two
  realizations into `AlgebraicClosure (RatFunc ℚ)` with `IsAlgClosed.lift`, take `⊔`, compute the
  group, and prove regularity of the join (`algebraicClosure_sup_eq_bot`,
  `IsRegularInverseGalois.prod_of_coprime`).  Route δ's assembly file F7 is a `|H|`-fold version of
  that file with "coprime degrees" replaced by "inertia-separated layers".

### 1.5 Kummer theory (base-generic!)

```lean
structure Kummer.Setup (E L : Type*) [Field E] [Field L] [Algebra E L] (ι : Type*) [Fintype ι]
    (n : ℕ) where                                        -- KummerIndep.lean:39
  zeta : E ; g : ι → E ; w : ι → L
  isPrimitiveRoot : IsPrimitiveRoot zeta n
  g_ne_zero : ∀ i, g i ≠ 0
  w_pow : ∀ i, w i ^ n = algebraMap E L (g i)
  adjoin_eq_top : IntermediateField.adjoin E (Set.range w) = ⊤
  indep : ∀ (m : ι → ℤ) (y : E), y ≠ 0 → y ^ n = ∏ i, g i ^ m i → ∀ i, (n : ℤ) ∣ m i
```
with `psi_bijective`, `galEquiv : (L ≃ₐ[E] L) ≃* (ι → rootsOfUnity n L)`,
`card_aut : Nat.card (L ≃ₐ[E] L) = n ^ Fintype.card ι`, `finrank_eq`, `exists_aut_zpow`;
`setupOfIndep` (`KummerBase.lean:120`) builds a `Setup` on the splitting field of
`∏ (Xⁿ - g i)` from the independence hypothesis alone; `isField_tensor` (`KummerBase.lean:172`)
is the base-change statement.  Only `[CharZero E]`/`[NeZero n]` are assumed — **the Kummer core is
already base-general**, and `RadicalIndep.lean` (`phiF`, `eq_zero_of_phiF_eq_one`) supplies the
independence for `ℙ¹`-linear radicands over an arbitrary `F`.  Route α (§4.1) would consume exactly
`Setup.indep`; route δ does not need any of it.

### 1.6 Descent, specialization

`Rigidity/RET/Descent/` — `constFieldBase`, `exists_regular_over_constant_base`,
`exists_regular_numberField_of_orbitRigid`, `branch_cycle_descent`, `geomModel_descent`
(`Descent/ModelDescent.lean:614`) and `geomModel_exists` (`Descent/Tower.lean:215`) go
**geometric → arithmetic**.  The direction route δ needs, **arithmetic → geometric**, is

```lean
theorem isField_baseChange_of_regular {L : Type*} [Field L] [Algebra (RatFunc ℚ) L]
    [FiniteDimensional (RatFunc ℚ) L] [Algebra ℚ L] [IsScalarTower ℚ (RatFunc ℚ) L]
    (hreg : algebraicClosure ℚ L = ⊥) :
    IsField (FractionRing (Polynomial (AlgebraicClosure ℚ)) ⊗[RatFunc ℚ] L)
                                                    -- GeometricIrreducibility.lean:523
```
and its base-general twin `isField_baseChange_of_regular_gen` (`Descent/RegularityGen.lean:321`,
arbitrary `CharZero k₀`).  Then `Rigidity/RET/Specialization.lean:1107`:

```lean
theorem IsRegularInverseGalois.isInverseGalois {G : Type} [Group G] [Finite G]
    (h : IsRegularInverseGalois G) : IsInverseGalois G
```

### 1.7 Hilbert irreducibility

`hilbert_irreducibility_theorem` (`Hilbert/HilbertIrreducibility.lean:423`) **requires**
`hf_abs_irr : Irreducible (f.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))))`.  There is no
version for a polynomial that is irreducible over `ℚ(T)` but not over `ℚ̄(T)`, and no version over a
number-field base.  `Hilbert/RegularExtension.lean:102` (`realizable_of_embeds_and_root`) is the
per-specialization core and the model for the "cardinality + injection" identification pattern.

### 1.8 Wreath products

Mathlib `RegularWreathProduct` (`≀ᵣ`) with
`(a * b).left = a.left * fun x ↦ b.left (a.right⁻¹ * x)`, `(a*b).right = a.right * b.right`
(`Mathlib/GroupTheory/RegularWreathProduct.lean:45–62`).  Repo side
(`InverseGalois/Solvable/Wreath.lean`): `twistedProd`, `toSemidirectProduct : A ≀ᵣ H →* A ⋊[φ] H`
(`:75`), `toSemidirectProduct_surjective` (`:99`), and the two consumers
`IsInverseGalois.semidirectProduct_of_wreath` (`:120`),
`IsRegularInverseGalois.semidirectProduct_of_wreath` (`:129`).  So the *only* missing input is the
realization of `A ≀ᵣ H` itself.

---

## 2. How deep does the `ℚ` hard-wiring go?  (question b)

Three strata, and the answer is different in each.

1. **The predicates and their transport are already base-general.**  `IsRegularGaloisGroupOverBase`
   takes `k` and `F` as parameters; `of_mulEquiv`, `of_algEquiv`, `algebraicClosure_ratFunc`,
   `isField_baseChange_of_regular_gen` all quantify over the base.  Nothing has to be re-stated to
   *say* the engine over an arbitrary `k`.
2. **The abelian input and the closure properties are hard-wired to `ℚ`, but shallowly.**
   `IsRegularInverseGalois.of_commGroup` (`AbelFinale.lean:73`),
   `.of_surjective` / `.quotient` (`RegularQuotient.lean:38, 71`),
   `.prod_of_coprime` (`RegularProduct.lean`) are all stated for `ℚ`.  `of_surjective`/`.quotient`
   are pure Galois correspondence and port to `IsRegularGaloisGroupOverBase k F` almost verbatim
   (**S**, ~150 lines).  `of_commGroup` does *not* port cheaply: the layers under it
   (`KummerBlocks`, `AbelKummer`, `AbelRegular`, `KummerAbelian`) hard-code `KK n = ℚ(ζₙ)`,
   `FF = RatFunc ℚ` and the branch points `ζₙᶜ·b ∈ ℚ̄`.  Porting it to arbitrary `k` is **XL**.
3. **The geometry is hard-wired to `ℙ¹` over `ℚ̄`, deeply** — `GeomAKLB.k := AlgebraicClosure ℚ`,
   `LineCover`'s `Algebra (Polynomial k)` field, `placeP t = span {X - C t}`.  Every branch-locus,
   inertia and disjointness theorem lives here.

**Consequence for the design.**  Any route whose induction needs the *abelian input over a varying
base field* runs straight into stratum 2 (XL).  Route δ is chosen precisely because it consumes the
abelian input **only over `ℚ`** and does all its geometry **only over `ℚ̄`** — i.e. it stays inside
strata where the repository is already strong.  The base field therefore does not need to be
quantified: the recursion `H` regular over `ℚ(T)` ⟹ `A ≀ᵣ H` regular over `ℚ(T)` closes on itself.

---

## 3. Base change of a regular realization (question 2)

**Nothing in the tree does this.**  There is no
`IsRegularGaloisGroupOver k G → IsRegularGaloisGroupOver k' G` for an extension `k'/k`.  The
nearest neighbours are:

* `isField_baseChange_of_regular` / `_gen` — base change of the *field* to `k₀‾(T)` only
  (`GeometricIrreducibility.lean:523`, `Descent/RegularityGen.lean:321`);
* `RegularityConverse.algebraicClosure_eq_bot_of_isField_tensor` — the converse direction;
* `Descent/BaseTransfer.of_algEquiv` — replaces the base by an *isomorphic* one, not an extension.

If a route needs it, the cleanest formulation is

```lean
theorem IsRegularGaloisGroupOver.baseChange {k k' : Type} [Field k] [Field k'] [Algebra k k']
    [CharZero k] {G : Type} [Group G] (h : IsRegularGaloisGroupOver k G) :
    IsRegularGaloisGroupOver k' G
```
proved by `L' := k'(T) ⊗_{k(T)} L`, a field by an `isField_tensor`-style argument, with regularity
from linear disjointness of `k'` and `L` over `k`.  Effort **L**; the hazards are exactly the ones
the memory file `splittingfield-ratfunc-diamond-pinning` records — the two `Algebra k (RatFunc k')`
routes (`k → k' → RatFunc k'` and `k → RatFunc k → RatFunc k'`) are not definitionally equal, so
every statement must pin `IsScalarTower` explicitly, and the tensor product must be handed to
`IsField` before any `Field` instance is derived, or `Algebra` instances diverge.

**Route δ does not need this lemma.**  That is one of its main advantages.

---

## 4. Four routes, and why route δ

Fix: `E/ℚ(T)` a regular Galois extension with `Gal(E/ℚ(T)) ≃ H` (the input), `X` its curve,
`A` finite abelian, `n = exp A`.

### 4.1 Route α — Kummer divisor independence on the curve

Adjoin `n`-th roots of the `|H|` conjugates `f^h` of a single `f ∈ E` whose divisors are
independent mod `n`, feeding `Kummer.Setup.indep`.  The independence itself is easy and
genus-independent: with `B = integralClosure (Polynomial ℚ̄) E` (Dedekind, `H`-stable), CRT gives
`f` with `v_Q(f) = 1`, `v_{hQ}(f) = 0` for `h ≠ 1`, whence `v_Q(f^h) = δ_{h,1}` and
`∏_h (f^h)^{e_h} = yⁿ ⟹ n ∣ e_h`.

**Two obstructions, both real.**

* *A free `H`-orbit of places need not exist.*  `v_{hQ}(f) = 0` for all `h ≠ 1` presupposes the
  orbit of `Q` is free, i.e. `Q` lies over a place of `k(T)` that splits **completely**.  Over
  `k = ℚ` that can fail: take `H = C₂` and `E = ℚ(T)(y)`, `y² = -1-T²`.  `E/ℚ(T)` is regular Galois
  (the conic `x²+y²+z²=0` is smooth, hence geometrically integral, so `ℚ` is algebraically closed
  in `E`), but a completely split place of degree `1` would be a `ℚ`-point of that conic, and there
  are none.  Degree-2 split places *do* exist here, but nothing in general guarantees any.  The fix
  is to strengthen the induction invariant to "carries a completely split place", which then has to
  be *preserved*: the new cover is ramified over the split place used to build `f`, so a *second*
  split place is needed where `f` is a local `n`-th power, and iterating wants infinitely many.
  That invariant is not obviously preserved and there is no Chebotarev over `k(T)` for infinite `k`.
* *μₙ.*  `L({f^{h/n}})` is Galois over `k(T)` only when `μₙ ⊆ k`.  Removing it needs the
  `H`-equivariant twisted-Kummer descent (§6.1) generalized from `ℙ¹`-linear radicands to prime
  elements of a Dedekind domain, with a `Δ = Gal(k(ζₙ)/k)` orbit twist.  **XL, research-level.**

Verdict: sound mathematics, wrong repository.

### 4.2 Route β — disjoint branch loci

The classical argument: make the `|H|` layers unramified outside pairwise disjoint sets, apply
`inf_eq_bot_of_disjoint'`, conclude linear disjointness.

**This does not generalize to a regular one-variable engine**, and the reason is structural, not
Lean-specific: `inf_eq_bot_of_disjoint'` is powered by
`subsingleton_deck_of_unramifiedOutside_singleton` (`TranslateInfinity.lean:453`), i.e. by
`π₁(ℙ¹ ∖ {pt}) = 1`.  Over a base curve `X` of positive genus "unramified everywhere ⇒ trivial" is
**false**, so the disjointness lemma has no analogue there.  The argument survives only where the
base is `ℙ¹` — which is exactly route γ, where the `H`-layer is a *constant* extension and the
covers still live over `ℙ¹`.

So: **keep route β in the toolbox for route γ, discard it for any route whose `H`-layer is
geometric.**  Compared with route α's divisor independence, β is cleaner in Lean (it is already
written, `ProductTranslate.lean`) but strictly less general; α is genus-blind but drags in μₙ and
split places.  Route δ below uses *neither*: it replaces "unramified outside disjoint sets" by
"ramified at a fibre where the others are unramified", which is genus-blind **and** needs no
Kummer theory.

### 4.3 Route γ — the arithmetic translate (one variable, non-regular)

`L/ℚ` a number field with `Gal(L/ℚ) = H`, `θ` primitive with conjugates `θ_h`; `N/ℚ(x)` a regular
`A`-extension; embed `N` into `Ω = AlgebraicClosure (RatFunc ℚ)` `|H|` times along
`x ↦ c·θ_h + T`; set `M := ⨆_h ε_h(N) ⊔ L(T)`.

*Advantages:* the `|H|` covers are honest **translates** of one cover of `ℙ¹`, so the existing
`LineCover.twist` + `exists_translate_disjoint` + `inf_eq_bot_of_disjoint'` machinery applies
verbatim; the `H`-action on the index set is free for free (the `θ_h` are distinct constants);
there is no μₙ problem, no split-place problem, no genus problem.  The degree is pinched
geometrically: `|A|^{|H|} = [M·ℚ̄(T) : ℚ̄(T)] ≤ [M : L(T)] ≤ |A|^{|H|}`, which simultaneously proves
the degree, the group, and that the constant field of `M` is exactly `L`.

*Fatal cost:* `M/ℚ(T)` is **not** regular (`L ⊆ M`), so the conclusion is
`Gal(M/ℚ(T)) ≃ A ≀ᵣ H` with no route to `IsInverseGalois` short of a Hilbert irreducibility theorem
for a polynomial that is *not* absolutely irreducible.  The needed interface is exactly

```lean
theorem isInverseGalois_of_galois_ratFunc {G : Type} [Group G] [Finite G] (M : Type) [Field M]
    [Algebra (RatFunc ℚ) M] [FiniteDimensional (RatFunc ℚ) M] [IsGalois (RatFunc ℚ) M]
    (e : (M ≃ₐ[RatFunc ℚ] M) ≃* G) : IsInverseGalois G
```
— "every finite Galois group over `ℚ(T)` is a Galois group over `ℚ`".  Until that lands, route γ
realizes nothing.

### 4.4 Route δ — generic pullback of a black-box abelian cover  ★ recommended

Inputs: `hH : IsRegularInverseGalois H` giving `E/ℚ(T)` regular Galois, and
`hA : IsRegularInverseGalois A` (free, `AbelFinale.lean:73`) giving `N/ℚ(x)` regular Galois.

1. **Choose the transporting function.**  `θ ∈ E` a primitive element for `E/ℚ(T)`, conjugates
   `θ_h := h(θ)`, `h ∈ H`, pairwise distinct.  Parameters `λ, c ∈ ℚ`; write `θ_h^{λ,c} := λθ_h + c`.
2. **Pull back.**  `N_h :=` the compositum of `E` with the image of `N` under the embedding
   determined by `x ↦ θ_h^{λ,c}`, inside `Ω = AlgebraicClosure (RatFunc ℚ)`.  Set `M := ⨆_h N_h`.
   `H` permutes `{N_h}` regularly: any `σ ∈ Gal(M/ℚ(T))` over `q ∈ H` carries the embedding
   `x ↦ θ_h^{λ,c}` to `x ↦ θ_{qh}^{λ,c}`, and `N/ℚ(x)` normal makes the image independent of the
   chosen extension, so `σ(N_h) = N_{qh}`.
3. **Genericity.**  Let `S ⊂ ℚ̄` be the (finite) branch locus of `N ⊗ ℚ̄(x)`, and move `∞` out of it
   with `MoveInfinity.lean`.  Claim: for all but finitely many `(λ, c)`, every closed point `Q` of
   `X_{ℚ̄}` with `θ^{λ,c}(Q) ∈ S` satisfies (a) `θ^{λ,c}` is unramified at `Q`, and
   (b) `θ_h^{λ,c}(Q) ∉ S` for every `h ≠ 1`.
   *Proof:* (b) fails only if `(θ − θ_h)(Q) ∈ λ⁻¹(S − S)`, a finite set of values; each
   `θ − θ_h` is either non-constant — giving a finite set `W` of bad `Q`, independent of `c` — or a
   nonzero constant, which `λ` is chosen to push out of `λ⁻¹(S−S)`.  Add the (finitely many)
   ramification points of `θ` to `W`.  The fibres `D_c := (θ^{λ,c})^{-1}(S)` for `c` in a set of
   representatives with pairwise differences outside `S − S` are pairwise disjoint, so at most
   `#W` of them meet `W`.  This is the curve analogue of `exists_translate_disjoint`
   (`ProductTranslate.lean`).
4. **Independence by inertia.**  Fix such `(λ, c)` and work over `ℚ̄`.  For each `s ∈ S` pick
   `Q ∈ (θ^{λ,c})^{-1}(s)`.  Since `θ^{λ,c}` is unramified at `Q`, the inertia of `N̄_1/Ē` at `Q` is
   (isomorphic to) the inertia `I_s` of `N̄/ℚ̄(x)` at `s`; and by (b) every `N̄_h`, `h ≠ 1`, is
   unramified at `Q`.  Put `R := ⨆_{h≠1} N̄_h` and `D := N̄_1 ⊓ R`.  `D/Ē` is unramified at every
   such `Q` (a compositum of unramified extensions is unramified), hence `Gal(N̄_1/D)` contains
   every `I_s`; but `⨆_s I_s = Gal(N̄/ℚ̄(x)) = A`, because a cover of `ℙ¹` unramified everywhere is
   trivial (`subsingleton_deck_of_unramifiedOutside_empty`, packaged as
   `exists_places_iSup_geomInertia_eq_top_of_comm`, `AbelianGeneration.lean:334`).  So `D = Ē`.  By
   symmetry the same holds for every `h`, and since all layers are abelian over `Ē`,
   `[M̄ : Ē] = |A|^{|H|}`.
5. **Degree pinch = group + regularity in one stroke.**
   `|A|^{|H|}·|H| = [M̄ : ℚ̄(T)] ≤ [M : ℚ(T)] ≤ |A|^{|H|}·|H|`, so both are equal, `M ⊗ ℚ̄(T)` is a
   field and `algebraicClosure ℚ M = ⊥` — `M/ℚ(T)` is **regular** — and
   `Gal(M/ℚ(T)) ≃ A ≀ᵣ H` by §5.

*What δ needs that the repository lacks:* a ramification statement for the pullback of a cover of
`ℙ¹` along a **non-structure** map `θ : X → ℙ¹` (F5 below).  That is the whole of the new geometry.
*What δ does not need:* μₙ, split places, positive-genus disjointness, base change of the base
field, a new HIT, any change to the abelian machinery.

### 4.5 Comparison

| | α divisor indep. | β disjoint loci | γ arithmetic translate | **δ generic pullback** |
|---|---|---|---|---|
| conclusion | regular | regular | **non**-regular | regular |
| needs new HIT | no | no | **yes (blocking)** | no |
| μₙ / twisted Kummer | **yes (XL)** | no | no | no |
| needs split place invariant | **yes (unproven)** | no | no | no |
| genus-safe | yes | **no** | n/a (`ℙ¹`) | yes |
| reuses repo geometry | little | fully | fully | partly (F5 is new) |
| new Lean (est.) | 4 000+ | — | 1 800 + HIT | **3 200** |

---

## 5. Identifying the group with `A ≀ᵣ H`  (question 4)

**Recommendation: an explicit homomorphism from coordinates, then cardinality — not an abstract
`MulEquiv`, not a surjection.**  The reason a bare surjection is not enough: the extension
`1 → A^H → Gal(M/ℚ(T)) → H → 1` *is* always split (Shapiro: `H²(H, Ind₁^H A) = H²(1, A) = 0`), but
turning that into a Lean `MulEquiv` with `RegularWreathProduct` would go through group-cohomology
and group-extension API that is not usable off the shelf.  The coordinates are free here anyway.

**The coordinates.**  Fix the embeddings `ε_h : N → Ω` of step 2 (`ε_h(N) ⊆ N_h`).  For
`σ ∈ G := Gal(M/ℚ(T))` with `q := σ|_E ∈ H`, `σ ∘ ε_h` is another embedding of `N` with image
`N_{qh}`, so there is a unique `a_h(σ) ∈ Aut(N) ≃ A` with `σ ∘ ε_h = ε_{qh} ∘ a_h(σ)`.  Then

```
(στ) ∘ ε_h = σ ∘ ε_{q_τ h} ∘ a_h(τ) = ε_{q_σ q_τ h} ∘ a_{q_τ h}(σ) ∘ a_h(τ)
  ⟹  a_h(σ τ) = a_{q_τ h}(σ) · a_h(τ).
```

Mathlib's law is `(a*b).left x = a.left x * b.left (a.right⁻¹ * x)`, so the correct packaging is

```
Ψ(σ) := ⟨fun x ↦ a_{q_σ⁻¹ x}(σ), q_σ⟩ ,
```

which I verified against the cocycle:
`Ψ(στ).left x = a_{(q_σ q_τ)⁻¹x}(στ) = a_{q_σ⁻¹x}(σ) · a_{q_τ⁻¹ q_σ⁻¹ x}(τ) = (Ψ(σ)Ψ(τ)).left x`. ✔

**The Lean statement** (pure group theory, no fields — this makes the file trivially reusable by
routes γ and δ alike):

```lean
namespace Wreath
variable {G A H : Type*} [Group G] [CommGroup A] [Group H]

/-- Coordinates satisfying the wreath cocycle identity assemble into a homomorphism. -/
def coordHom (π : G →* H) (a : H → G → A)
    (hcocycle : ∀ (h : H) (σ τ : G), a h (σ * τ) = a (π τ * h) σ * a h τ)
    (hone : ∀ h, a h 1 = 1) : G →* A ≀ᵣ H where
  toFun σ := ⟨fun x => a ((π σ)⁻¹ * x) σ, π σ⟩
  map_one' := by ext x <;> simp [hone]
  map_mul' := by
    intro σ τ
    ext x
    · simp only [RegularWreathProduct.mul_left, Pi.mul_apply, map_mul, mul_inv_rev]
      rw [hcocycle]
      congr 2 <;> group
    · simp

theorem mulEquiv_of_injective_of_card [Finite G] [Finite A] [Finite H]
    (Ψ : G →* A ≀ᵣ H) (hinj : Function.Injective Ψ)
    (hcard : Nat.card G = Nat.card A ^ Nat.card H * Nat.card H) :
    Nonempty (G ≃* A ≀ᵣ H) := by
  have hc : Nat.card G = Nat.card (A ≀ᵣ H) := by rw [hcard, RegularWreathProduct.card]
  have hbij : Function.Bijective Ψ := (Nat.bijective_iff_injective_and_card Ψ).2 ⟨hinj, hc⟩
  exact ⟨MulEquiv.ofBijective Ψ hbij⟩
end Wreath
```

**Both declarations above were typechecked as written** (`lake env lean` on a scratch file, exit 0);
`RegularWreathProduct.card` is `Mathlib/GroupTheory/RegularWreathProduct.lean:130` and its shape
`Nat.card D ^ Nat.card Q * Nat.card Q` is exactly the pinch of §4.4 step 5.  So F1 is not an
estimate — it is done modulo docstrings.

Injectivity of `Ψ` is immediate: `π σ = 1` and all `a_h(σ) = 1` say `σ` fixes `E` and each `ε_h(N)`,
hence fixes `M = ⨆ N_h`.  The cardinality comes from the pinch of §4.4 step 5.  This mirrors
`realizable_of_embeds_and_root` (`Hilbert/RegularExtension.lean:102`) exactly:
`Nat.card_le_card_of_injective`, then `le_antisymm`, then `Finite.injective_iff_bijective`.

---

## 6. Roots of unity, and cyclic kernels

### 6.1 FACT 3 — the twisted-Kummer / Φ-exponent machinery

`isGeometricGaloisCover_of_commGroup` (`KummerAbelian.lean:307`) and the `AbelFinale`/`AbelRegular`/
`AbelKummer`/`KummerBlocks` tower are **too abelian-specific and too `ℚ`-specific to reuse as
technique**: they hard-code `KK n = ℚ(ζₙ)`, the branch points `ζₙᶜ·b`, and the `Δ`-orbit exponent
recipe on `ℙ¹`-linear radicands.  Transplanting that to prime elements of a Dedekind domain with an
`H`-equivariant twist is the XL wall of route α.

The right way to reuse them is **as a theorem, not as a technique**: route δ consumes
`IsRegularInverseGalois.of_commGroup` as a black box.  All the μₙ pain has then already been paid
for, once, inside the abelian file — which is exactly what that file is for.  The genuinely
generic Kummer layer (`KummerIndep.lean`, `KummerBase.lean`, `RadicalIndep.lean`) is base-generic
and would be reusable, but route δ does not need it.

### 6.2 FACT 4 — only cyclic kernels are needed

Correct (Kisilevsky–Neftin–Sonn Lemma 3.1: every finite semiabelian group is an image of a
descending iterated wreath product of cyclic groups), and it lets the final theorem be assembled
from `C_{n₁} ≀ (C_{n₂} ≀ ⋯)` plus `IsRegularInverseGalois.of_surjective`
(`RegularQuotient.lean:38`).  **But it does not simplify route δ at all**: `A` enters only through
`IsRegularInverseGalois A`, which holds for every finite abelian `A` at the same price, and step 4
uses only that `A` is abelian (so that `Gal(M̄/Ē) ↪ ∏_h A` and intersection-triviality upgrades to
a direct product).  *Recommendation: state the engine for general finite abelian `A`* — it is free,
and it avoids having to phrase the semiabelian corollary through `ZMod`.

Note also that the induction over `ℚ` is genuinely self-contained: start from
`IsRegularInverseGalois C_{n_r}` (abelian, available), apply the engine `r−1` times from the inside
out, then `of_surjective`.  No intermediate base field is ever needed.

---

## 7. File-by-file plan

Namespace `Rigidity.RET.Wreath` unless stated.  All files `import Mathlib` plus the listed repo
imports, matching house style.

| # | File | Effort | Content |
|---|---|---|---|
| F1 | `InverseGalois/Solvable/WreathRecognition.lean` | **S** ~250 | `Wreath.coordHom`, `mulEquiv_of_injective_of_card` (§5) — **both already typechecked, see §5**. Pure group theory. Imports: `InverseGalois.Solvable.Wreath`. **Start here — zero risk, needed by every route.** |
| F2 | `InverseGalois/Rigidity/RET/RegularBaseGen.lean` | **S** ~180 | Base-general ports of `IsRegularInverseGalois.of_surjective` / `.quotient` to `IsRegularGaloisGroupOverBase k F`. Independently useful. Imports: `…RET.RegularQuotient`. |
| F3 | `…/RET/Wreath/Conjugates.lean` | **M** ~400 | `θ`, its conjugates, the `|H|` embeddings `ε_h : N →ₐ[ℚ] Ω` into `Ω = AlgebraicClosure (RatFunc ℚ)` via `RatFunc.liftAlgHom` + `IsAlgClosed.lift`; `σ(ε_h(N)) = ε_{qh}(N)`; the coordinate function `a_h` and its cocycle identity, discharged into F1. Imports: `…RET.RegularProduct` (for the `IsScalarTower`/`IsAlgClosed.lift` idioms), F1. |
| F4 | `…/RET/Wreath/Genericity.lean` | **M–L** ~500 | §4.4 step 3: for all but finitely many `(λ,c)`, the fibre of `λθ+c` over the branch locus avoids `W`. Model: `exists_translate_disjoint` (`ProductTranslate.lean`). Imports: `…RET.BranchLocus`, `…RET.MoveInfinity`. |
| F5 | `…/RET/Wreath/PullbackInertia.lean` | **L–XL** ~700 | **The new geometry.** Give `Ē` a second `Algebra (Polynomial ℚ̄)` structure along `x ↦ θ^{λ,c}`; show `N̄_h = Ē ⊗_{ℚ̄(x)} N̄` is a field; compute its inertia at `Q` from the inertia of `N̄` at `θ(Q)` when `θ` is unramified at `Q`, via `Ideal.ramificationIdx_tower` (Mathlib) and `Ideal.inertia`. Also: a compositum of extensions unramified at `Q` is unramified at `Q`. Imports: `…RET.Descent.AKLBGen`, `…RET.Descent.GeomAKLB`. |
| F6 | `…/RET/Wreath/Independence.lean` | **L** ~500 | §4.4 step 4: `N̄_h ⊓ ⨆_{h'≠h} N̄_{h'} = ⊥` for all `h`, then `[M̄ : Ē] = |A|^{|H|}` by induction over a `Finset H`. Generalizes `nonempty_deck_mulEquiv_prod` (`SubcoverProduct.lean:71`) from 2 to `|H|` factors. Imports: F5, `…RET.SubcoverProduct`, Mathlib `FieldTheory.LinearDisjoint`. |
| F7 | `…/RET/Wreath/Engine.lean` | **M** ~350 | The pinch and the theorem: `isRegularInverseGalois_wreath`. Model: `RegularProduct.lean` (`algebraicClosure_sup_eq_bot`, `isScalarTower_rat`). Imports: F1, F3, F4, F6, `…RET.GeometricIrreducibility`, `…RET.ProductGeometric`. |
| F8 | `…/RET/Wreath/Semiabelian.lean` | **M** ~300 | Iterated wreath products of cyclic groups; `IsRegularInverseGalois` for every semiabelian group; the semidirect-product corollary via `Solvable/Wreath.lean:129`; catalogue entry. Imports: F2, F7, `InverseGalois.Solvable.Wreath`. |

Headline statements:

```lean
-- F7
theorem isRegularInverseGalois_wreath {A H : Type} [CommGroup A] [Finite A]
    [Group H] [Finite H] (hH : IsRegularInverseGalois H) :
    IsRegularInverseGalois (A ≀ᵣ H)

-- F8
theorem IsRegularInverseGalois.semidirectProduct {A H : Type} [CommGroup A] [Finite A]
    [Group H] [Finite H] (φ : H →* MulAut A) (hH : IsRegularInverseGalois H) :
    IsRegularInverseGalois (A ⋊[φ] H)
```

**Dependency order:** F1 → F3 → (F4 ∥ F5) → F6 → F7 → F8; F2 anywhere.  F1 and F2 are landable
immediately and independently.

**Fallback wiring (route γ).**  If F5 stalls, F1 + F3 + `LineCover.twist` +
`inf_eq_bot_of_disjoint'` give route γ in ~600 further lines, producing
`Gal(M/ℚ(T)) ≃ A ≀ᵣ H` with constant field a number field `L`; it then waits on the
`isInverseGalois_of_galois_ratFunc` interface of §4.3.  F1/F3 are shared, so this is not wasted work.

---

## 8. Verdict, effort, risks

**Total effort:** ≈ 3 200 lines, 5–8 sessions, concentrated in F5 and F6.

**Cheaper partial results worth landing first** (in this order):

1. **F1 + F2** (~430 lines, near-zero risk).  F1 is the identification engine every route needs;
   F2 unblocks base-general quotient closure and is useful independently of this project.
2. **`C_n ≀ C_m` regular over `ℚ`.**  When `H` is itself abelian, `E` can be taken to be the
   repository's own Kummer cover, `θ` a radical, and the pullback `N_h` is then given by explicit
   radicals — so `Kummer.Setup`/`setupOfIndep` computes steps 4–5 directly and **F5 is not needed**.
   This lands genuinely new groups (e.g. `C₃ ≀ C₃`, order 81; the catalogue currently has abelian,
   dihedral, `Sₙ`, `Aₙ`, `PGL₂(𝔽_p)`, Mathieu) and de-risks F3/F4/F6/F7 against a computable case.
3. Then F5, then the general engine.

**Top three risks.**

1. **F5, the second algebra structure (L–XL).**  Putting a second `Algebra (Polynomial ℚ̄) Ē` on the
   same field, along `x ↦ λθ+c`, is precisely the situation the memory files
   `lean-semilinear-pitfalls` and `ratfunc-shortcut-instance` warn about: competing instances make
   `whnf`/`isDefEq` diverge and can turn a 100 s file into a 5 000 s file.  *Mitigation:* never make
   it an instance — carry the algebra map as an explicit `RingHom` argument through the whole file,
   define `N̄_h` as a `SplittingField` of a transported polynomial rather than as a tensor product,
   and keep `Bring` abstract (`IsIntegralClosure`) instead of the `integralClosure` abbreviation.
2. **F6's `|H|`-fold compositum (L).**  `⨆ h ∈ Finset.univ, N_h` over a group-indexed family
   elaborates badly; `Product.lean` is already the most expensive file in the tree (~82 min).
   *Mitigation:* index by `Fin (Nat.card H)` through a fixed equivalence, do the induction over
   `Finset (Fin n)` with `Finset.sup`, and state the intermediate lemmas about `finrank` rather than
   about deck groups (degrees compose; group isomorphisms do not).
3. **The genericity bookkeeping of F4 (M–L).**  Two parameters, three simultaneous exclusion
   conditions (`θ − θ_h` constant; `Q ∈ W`; `θ` ramified at `Q`), all "finitely many bad values in
   an infinite field".  This kind of argument is where sorries linger.  *Mitigation:* state each
   exclusion as its own `Set.Finite` lemma, combine with `Set.Finite.union`, and reuse the shape of
   `exists_translate_disjoint`.

**Residual honest caveats.**

* Step 4's claim "the inertia of the pullback at `Q` equals the inertia of `N̄` at `θ(Q)` when `θ` is
  unramified at `Q`" is standard but is the one step of route δ I have not checked against a
  fully written-out Lean proof; it is the mathematical core of F5.
* The literature statement (Dentzer, *manuscripta math.* **86** (1995) 199–216; Stoll, *Glasgow
  Math. J.* **37** (1995) 99–104) quantifies over the base field.  That quantification is *not*
  needed here, and my reading of the obstructions in §4.1 suggests why the literature carries it:
  the Kummer-style proofs need `μₙ` and a split place, and quantifying over `k` is how one gets
  them.  Route δ buys the same conclusion over `ℚ` by outsourcing both to the already-proved
  abelian realization.
