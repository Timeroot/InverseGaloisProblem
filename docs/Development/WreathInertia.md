# Wreath products, part II: how to prove `[M̄ : Ē] = |A|^{|H|}`

*Reconnaissance memo. Supersedes §7 (F4–F6) of `WreathConstruction.md`. No Lean was written; every
signature below was either copied verbatim out of the repo/Mathlib or elaborated in a scratch file
(marked ✅ where checked).*

## TL;DR

1. **The whole `LineCover` layer is hard-wired to `ℙ¹` over `ℚ̄`.** `k := AlgebraicClosure ℚ`, base
   ring `Polynomial k`, base field `RatFunc k`. It cannot host `Ē`, and `AKLBGen.lean` does *not*
   help (it generalises the *constant* field, not the base curve). **But** the whole `RET/Genus/`
   subtree is already base-generic — arbitrary Dedekind chart of an arbitrary field — and that is
   where the curve-level work belongs.
2. **The Kummer reformulation wins, decisively.** Two decisive facts the coordinator did not know:
   * `Rigidity.RET.Kummer.Setup` (`RET/KummerIndep.lean:38`) is **already base-generic**: it needs
     only `[Field E] [Field L] [Algebra E L] [CharZero E] [NeZero n]`, with the root of unity as
     *structure data*, not a typeclass. Its `Setup.finrank_eq` (`:373`) is literally
     `Module.finrank E L = n ^ Fintype.card ι` — the theorem we want, with `E := Ē`. ✅
   * `RET/Wreath/Independence.lean` **already exists and is sorry-free** (119 lines, untracked). It
     is exactly step 3 of the coordinator's §7, including the `n = 6` gcd caveat, stated abstractly
     over a `CommGroup` with a bare additive `ℤ`-valued function.
   So the "hard lemma (b)" of §3 is not needed at all, `PiQuotient.lean` is not needed either
   (`Setup.finrank_eq` gives the degree directly), and the remaining work is one genuinely new
   theorem: *the private-place existence statement*.
3. **Lemma (b) verdict** (asked for even though it is now moot): *reachable but expensive* —
   roughly 500–700 lines, requiring a base-generic re-run of `Descent/AKLBGen.lean`. It is not out
   of reach, but on the Kummer route it costs nothing and buys nothing. **Do not build it.**
4. **Holes found: six.** Two are in the coordinator's §4 genericity argument and are fatal as
   stated (`φ_g` merely *nonzero* is not enough — it must be *non-constant*; and the bad set `B`
   omits the poles). Both have three-line fixes, given below. The other four are missing
   hypotheses/steps rather than errors.

---

## §1. The repo's ramification vocabulary, and its base field

### 1.1 The `LineCover` layer — base is `ℙ¹_{ℚ̄}`, always

`InverseGalois/Rigidity/RET/Descent/GeomAKLB.lean:43`:

```lean
abbrev k : Type := AlgebraicClosure ℚ
```

`:56`, `:95`, `:138`:

```lean
abbrev Bring : Type := integralClosure (Polynomial k) Ω
abbrev placeP (t : k) : Ideal (Polynomial k) := Ideal.span {(X - C t : Polynomial k)}
abbrev geomInertia (Q : Ideal (Bring Ω)) : Subgroup (Ω ≃ₐ[RatFunc k] Ω) :=
  Q.inertia (Ω ≃ₐ[RatFunc k] Ω)
```

`RET/TamePi1.lean:47` (this is also the answer to coordinator question §7(c); see §7.3):

```lean
structure LineCover where
  M : Type
  [field : Field M]
  [alg : Algebra (RatFunc k) M]
  [algPoly : Algebra (Polynomial k) M]
  [tower : IsScalarTower (Polynomial k) (RatFunc k) M]
  [findim : FiniteDimensional (RatFunc k) M]
  [isGalois : IsGalois (RatFunc k) M]
```

`RET/TamePi1.lean:82`:

```lean
def IsInertiaAt (L : LineCover) (t : k) (σ : L.deck) : Prop :=
  ∃ Q : Ideal (Bring L.M), Q.IsMaximal ∧ Q.LiesOver (placeP t) ∧ σ ∈ geomInertia L.M Q
```

`RET/Unramified.lean:49` and `RET/BranchSet.lean:76`, `:96`:

```lean
def IsUnramifiedOutside (L : LineCover) (S : Set k) : Prop :=
  ∀ t ∉ S, ∀ σ : L.deck, L.IsInertiaAt t σ → σ = 1
def branchLocus (L : LineCover) : Set k := {t : k | ∃ σ : L.deck, σ ≠ 1 ∧ L.IsInertiaAt t σ}
theorem finite_branchLocus (L : LineCover) : L.branchLocus.Finite
```

**Every one of these is indexed by a point `t : k` of the affine line and by a prime of
`Polynomial k`.** There is no version over a curve. The branch locus is a `Set k`, not a set of
places of a cover.

`Descent/AKLBGen.lean:50` is the only generalisation in the tree, and it generalises the wrong
thing:

```lean
variable (κ : Type*) [Field κ] [CharZero κ] [IsAlgClosed κ]
  (Ω : Type*) [Field Ω] [Algebra (RatFunc κ) Ω] … [Algebra (Polynomial κ) Ω]
```

— the *constant* field `κ` is arbitrary, the base is still `Polynomial κ` / `RatFunc κ`. So:

> **Answer to question 1: the base of every `LineCover`-flavoured notion is `RatFunc (AlgebraicClosure ℚ)`, and it cannot be an arbitrary finite extension. `Ē` is a curve, and none of `geomInertia` / `IsInertiaAt` / `IsUnramifiedOutside` / `branchLocus` / `LineCover` applies to it as-is.**

There is *one* escape hatch, and it is the right one for §4: `Ē` **is** the function field of a
`LineCover` for a *different* algebra structure — the one given by a transcendental `u ∈ Ē` — and
the repo already has the primitive for that, `RET/LineParam.lean:56`:

```lean
def paramHom (u : M) (hu : Transcendental k u) : RatFunc k →+* M :=
  IsFractionRing.lift (A := Polynomial k) (K := RatFunc k)
    (g := (Polynomial.aeval u : Polynomial k →ₐ[k] M).toRingHom)
    (transcendental_iff_injective.mp hu)
```

with `paramHom_X : paramHom u hu RatFunc.X = u` (`:67`) and
`paramHom_const : paramHom u hu (algebraMap k (RatFunc k) c) = algebraMap k M c` (`:74`).

### 1.2 The `Genus/` layer — fully base-generic, and chart-independent

This is the part of the repo that *does* work over a curve. Variable blocks verbatim.

`RET/Genus/Ord.lean:41-42`:

```lean
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
```

```lean
def ord (v : HeightOneSpectrum R) (x : K) : ℤ :=                         -- :46
  FractionalIdeal.count K v (spanSingleton R⁰ x)
theorem ord_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :                    -- :68
    ord K v (x * y) = ord K v x + ord K v y
theorem ord_pow  {x : K} (hx : x ≠ 0) (n : ℕ) : ord K v (x ^ n) = n * ord K v x   -- :83
theorem ord_zpow {x : K} (hx : x ≠ 0) (n : ℤ) : ord K v (x ^ n) = n * ord K v x   -- :88
theorem ord_finite (x : K) : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, ord K v x = 0  -- :95
theorem mem_iff_ord_pos {r : R} (hr : r ≠ 0) : r ∈ v.asIdeal ↔ 0 < ord K v (algebraMap R K r) -- :110
```

`RET/Genus/OrdUltra.lean:90`:

```lean
theorem ord_prod {ι : Type*} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, f i ≠ 0) :
    ord K v (∏ i ∈ s, f i) = ∑ i ∈ s, ord K v (f i)
```

`RET/Genus/Place.lean:59` and `RET/Genus/PlaceInertia.lean:55`, `:132`, `:149`:

```lean
def placeSubring (v : HeightOneSpectrum B) : ValuationSubring F := (v.valuation F).valuationSubring
def IsInertialAtPlace (A : ValuationSubring F) (σ : G) : Prop := ∀ x ∈ A, A.valuation (σ • x - x) < 1
theorem mem_inertia_iff_isInertialAtPlace (v : HeightOneSpectrum B) (σ : G) :
    σ ∈ Ideal.inertia G v.asIdeal ↔ IsInertialAtPlace (placeSubring F v) σ
theorem inertia_eq_of_placeSubring_eq … (hv : placeSubring F v₁ = placeSubring F v₂) :
    Ideal.inertia G v₁.asIdeal = Ideal.inertia G v₂.asIdeal
```

`RET/Genus/Chart.lean:67`:

```lean
theorem existsUnique_place (A : ValuationSubring F) (hBA : ∀ b : B, algebraMap B F b ∈ A)
    (hA : A ≠ ⊤) : ∃! v : HeightOneSpectrum B, placeSubring F v = A
```

`RET/Genus/Fundamental.lean:87` — **the bridge between orders of vanishing and ramification
indices**, base-generic:

```lean
theorem ord_algebraMap_eq_ramificationIdx (p : Ideal R) (P : HeightOneSpectrum B) {x : R}
    (hx : Ideal.span {x} = p) (hmap0 : Ideal.map (algebraMap R B) p ≠ ⊥) :
    ord F P (algebraMap R F x) = (ramificationIdx (algebraMap R B) p P.asIdeal : ℤ)
```

`RET/InertiaTransport.lean:35`, `:47` — fully general (arbitrary `CommRing`s and groups):

```lean
theorem mem_inertia_comap (f : B →+* B') (ρ : G' →* G)
    (hρ : ∀ (σ : G') (x : B), f (ρ σ • x) = σ • f x) (Q : Ideal B') {σ : G'}
    (hσ : σ ∈ Q.inertia G') : ρ σ ∈ (Q.comap f).inertia G
theorem inertia_comap_le … : (Q.inertia G').map ρ ≤ (Q.comap f).inertia G
```

**Summary of §1.** The repo commits to *both* framings and has already bridged them
(`mem_inertia_iff_isInertialAtPlace`, `inertia_eq_of_placeSubring_eq`, `existsUnique_place`,
`ord_algebraMap_eq_ramificationIdx`). The curve-level work should be done entirely in the
`Genus/` idiom — arbitrary Dedekind chart `B` with `IsFractionRing B Ē` — and never touch
`LineCover` except through `paramHom`.

---

## §2. Relative ramification over a curve

### 2.1 What Mathlib gives (v4.28.0, all verified)

Tower multiplicativity, `NumberTheory/RamificationInertia/Basic.lean:1006`:

```lean
theorem Ideal.ramificationIdx_algebra_tower [IsDedekindDomain S] [IsDedekindDomain T]
    {p : Ideal R} {P : Ideal S} {Q : Ideal T} [hpm : P.IsPrime] [hqm : Q.IsPrime]
    (hg0 : map (algebraMap S T) P ≠ ⊥) (hfg : map (algebraMap R T) p ≠ ⊥)
    (hg : map (algebraMap S T) P ≤ Q) :
    ramificationIdx (algebraMap R T) p Q =
      ramificationIdx (algebraMap R S) p P * ramificationIdx (algebraMap S T) P Q
```

and `Basic.lean:1018` `Ideal.inertiaDeg_algebra_tower` (no Dedekind hypotheses at all).

`|I| = e`, `NumberTheory/RamificationInertia/Galois.lean:320`:

```lean
lemma Ideal.card_inertia_eq_ramificationIdxIn
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [IsTorsionFree R S]
    (p : Ideal R) (hp : p ≠ ⊥) (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (P.inertia G) = Ideal.ramificationIdxIn p S
```

and `Galois.lean:215` `Ideal.ramificationIdxIn_mul_ramificationIdxIn`. The fundamental identity is
`Basic.lean:912` `Ideal.sum_ramification_inertia`.

**All of these are stated for an arbitrary Dedekind base `R`** — none of them knows about number
fields or about `Polynomial k`. So the *arithmetic* of a tower `ℚ̄(x) ⊆ Ē ⊆ M̄` is fully supported
even when the bottom inclusion is not the structure map, **provided** you supply the algebra
instances by hand.

### 2.2 What Mathlib does *not* give

Reported honestly, after grepping:

* **No `HeightOneSpectrum` functoriality at all.** No `HeightOneSpectrum.comap`, no
  `HeightOneSpectrum.under`, no map `HeightOneSpectrum B → HeightOneSpectrum A`, and no lemma
  `v.valuation L ∘ algebraMap K L = (w.valuation K) ^ e`. You must go through
  `Ideal.under` / `Ideal.LiesOver` on `.asIdeal` by hand. (The repo partly fills this:
  `Genus/Place.lean` has `underPrime`, `underPlace`, `placeSubring_underPlace`.)
* **No `Valuation.ramificationIdx`, no `Valuation.IsUnramified`.** The valuation-theoretic
  ramification index does not exist in Mathlib.
* **No existence theorem for extending a valuation along a finite field extension.**
* **Nothing whatsoever about composita being unramified** — grepped `unramified` ∩
  `sup|compositum|⊔|IntermediateField` across all of Mathlib: zero mathematical hits.
* `Ideal.decompositionGroup` does **not** exist; the decomposition group is spelled
  `MulAction.stabilizer G P`.

### 2.3 Verdict on framing

> **Ideal-theoretic for arithmetic, valuation-theoretic for geometry, bridged by `ord`.**

Mathlib supports the *ideal-theoretic* tower far better (there is no valuation-level ramification
index at all). But the ideal-theoretic framing forces a choice of chart, and a tower
`ℚ̄(x) ⊆ Ē ⊆ M̄` where the bottom map is `paramHom u` needs a *different* chart of `Ē` from the
one the `H`-cover comes with. The repo's own answer to that is `Genus/Place.lean` +
`Genus/Chart.lean`: make the `ValuationSubring` the primary object, and use
`existsUnique_place` / `inertia_eq_of_placeSubring_eq` to move between charts.

For the route this memo recommends (§7), **none of this is needed**: `ord` is chart-relative but
the *statement* we prove is a statement about a single fixed chart of `Ē`, and the tower is never
formed.

---

## §3. The three lemmas (kept for the record; **superseded by §7**)

### (a) Pullback is unramified off the pulled-back branch locus

*Status: must be built, but cheap on the Kummer route and unnecessary on it.*

```lean
/-- Candidate signature. NOT elaborated. -/
theorem isUnramifiedAt_pullback
    {Ebar : Type} [Field Ebar] [Algebra k Ebar] [CharZero Ebar]
    {B : Type} [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra B Ebar]
    [IsFractionRing B Ebar]
    (N : LineCover) (u : Ebar) (hu : Transcendental k u)
    (v : HeightOneSpectrum B) (hv : ∀ t ∈ N.branchLocus, ord Ebar v (u - algebraMap k Ebar t) = 0) :
    …
```

On the Kummer route this degenerates to the trivial statement
`ord_Q(κ(u)) = 0 ⇒ Q unramified in Ē(κ(u)^{1/n})`, which is one application of `ord_pow`.

### (b) Pullback preserves inertia — **the hard one**

*Status: **reachable, not out of reach**, but expensive; and on the Kummer route, unnecessary.*

The intended statement:

```lean
/-- Candidate signature. NOT elaborated; deliberately schematic. -/
theorem inertia_pullback_equiv
    (N̄ : LineCover) (Ē B M̄ …) (Q : HeightOneSpectrum B_M̄) (Q₀ := Q.under Ē) (s : k)
    (hunram : ramificationIdx (algebraMap _ _) (placeP s) Q₀.asIdeal = 1) :
    Ideal.inertia (M̄ ≃ₐ[Ē] M̄) Q.asIdeal ≃* Ideal.inertia (N̄.deck) (…)
```

The proof I worked out: restriction `Gal(N̄_h/Ē) → Gal(N̄/ℚ̄(x)) = A` is injective; over an
algebraically closed residue field in char 0, `|I| = e` (`Ideal.card_inertia_eq_ramificationIdxIn`);
multiplicativity in the two towers `ℚ̄(x) ⊆ Ē ⊆ N̄_h` and `ℚ̄(x) ⊆ N̄ ⊆ N̄_h`
(`Ideal.ramificationIdx_algebra_tower`) gives `e(Q̃|Q) = e(Q̃|q̃)·e(q̃|s) ≥ e(q̃|s)` when
`e(Q|s) = 1`; injectivity gives `≤`; hence restriction `I(Q̃|Q) → I(q̃|s)` is a **bijection**.

Cost estimate: a base-generic re-run of `Descent/AKLBGen.lean` (its `inertia_eq_stabilizer` `:159`
and `card_inertia` `:179` are the pieces needed, and they use only that `Polynomial κ` is Dedekind
with fraction field `RatFunc κ`, so they generalise mechanically, ~200 lines), plus the place
bookkeeping across two charts (~300 lines), plus the statement itself. **500–700 lines, medium
risk.**

**Recommendation: do not build it.** §7 makes it dead weight.

### (c) Inertia restricts to subextensions

*Status: **essentially free**.* `RET/InertiaTransport.lean:35` is fully general and elaborates
against arbitrary `CommRing`/`Group` data. ✅ (verified in scratch). Combine with
`RET/SubcoverProduct.lean:42 eq_of_subHom_eq_one`. No new file needed; three lines at the point of
use.

---

## §4. Genericity — the coordinator's `λ = 1` argument, stress-tested

### 4.1 The argument, restated

`θ ∈ Ē` primitive for `E/ℚ(T)`; `θ_h := h(θ)`; `u_h := θ_h + c`; `s_1,…,s_r ∈ ℚ̄` the zeros of the
normalised radicand `κ`. Want, for each `h` and each `i`, a place `Q` of `Ē` with

* `v_Q(u_h - s_i) = 1`,
* `v_Q(u_{h'} - s_j) = 0` for every `h' ≠ h` and every `j`.

Translate by the deck action, `P := h^{-1}Q`. Then the conditions read `θ(P) = s_i - c`, `θ`
unramified at `P`, `θ(gP) ∉ {s_1-c,…,s_r-c}` for `g ≠ 1`. Setting `φ_g := θ∘g - θ`, the bad
coincidence `θ(gP) = s_j - c ∧ θ(P) = s_i - c` forces `φ_g(P) = s_j - s_i`, **a condition not
involving `c`**. So

```
B := Ram(θ) ∪ ⋃_{g ≠ 1} ⋃_{i,j} φ_g^{-1}(s_j - s_i)
```

is a finite, `c`-independent subset of `X`, and it suffices to pick `c ∈ ℚ` with
`s_i - c ∉ θ(B)`.

**I believe the shape of this argument and I recommend adopting it.** It removes the two-parameter
`(λ,c)` bookkeeping entirely. But as written it has two gaps.

### 4.2 Hole #1 (fatal as stated): `φ_g` must be **non-constant**, not merely nonzero

The claim "`φ_g^{-1}(value)` is finite because `φ_g` is a nonzero element of a function field" is
false: a nonzero *constant* has empty or full preimage. If `φ_g = δ ∈ ℚ̄^×` and `δ = s_j - s_i` for
some pair, then **every** point of `X` is bad and the argument collapses.

**Fix (three lines, char 0 only).** Let `g` have order `N` in `H`. Then
`θ∘g^m = θ + m·δ` by induction, so `θ = θ∘g^N = θ + N·δ`, whence `N·δ = 0` and `δ = 0` in
characteristic zero — contradicting `φ_g ≠ 0`. Therefore `φ_g` is non-constant, i.e.
`Transcendental k (g • θ - θ)`. Candidate signature (elaborates ✅ modulo `sorry`):

```lean
theorem transcendental_conj_sub {H : Type} [Group H] [Finite H] [MulSemiringAction H Ebar]
    [SMulCommClass H k Ebar] (θ : Ebar) (g : H) (hg : g • θ ≠ θ) :
    Transcendental k (g • θ - θ)
```

This is a genuine strengthening and should be its own lemma. **It is also the only place in the
whole programme where characteristic zero is used essentially rather than for convenience.**

### 4.3 Hole #2: `B` omits the poles

The wanted conclusion includes "`u_{h'}` regular at `Q`", but `B` as defined does not exclude
`P` with `θ(gP) = ∞`. Such a `P` is *not* a solution of `φ_g(P) = s_j - s_i`; it is a pole of
`φ_g`. Concretely, if `θ_{h'}` has a pole at `Q` then `v_Q(u_{h'} - s_j) < 0` for every `j`, so
`v_Q(κ(u_{h'})) = -(Σ_j m_j)·(pole order) ≠ 0` and privacy fails.

**Fix.** Enlarge `B` by `⋃_{g ≠ 1} (poles of φ_g)`, equivalently by
`⋃_{g ≠ 1} g^{-1}(poles of θ)` — still finite, still independent of `c`. One extra `Set.Finite`
union.

### 4.4 The two facts about places of `Ē`, exact repo forms

**(i) "a nonzero element has nonzero order at only finitely many places"** — `RET/Genus/Ord.lean:95`:

```lean
theorem ord_finite (x : K) : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, ord K v x = 0 :=
  FractionalIdeal.finite_factors _
```

Base-generic, one line. This covers both "finitely many zeros" and "finitely many poles", and
therefore both `φ_g^{-1}(δ)` (apply to `φ_g - δ`) and the pole set.

**(ii) "a non-constant element has at least one zero"** — **NOT FOUND** in this form, and you
should not look for it. It is *false* for a fixed affine chart (`1/T` has no affine zero), and the
honest statement needs the place at infinity, which Mathlib has only for `RatFunc`
(`FunctionField.inftyValuation`) and not for a general function field.

**Do not prove it. Use the θ-chart instead.** Take `R_θ := integralClosure (Polynomial k) Ē` for
the algebra structure `paramHom θ hθ : RatFunc k →+* Ē`. Then the fibre of `θ` over `a` is
nonempty *by lying over* — the repo's own pattern, `Descent/GeomAKLB.lean:107`:

```lean
theorem exists_Q_over_placeP (t : k) : ∃ Q : Ideal (Bring Ω), Q.IsMaximal ∧ Q.LiesOver (placeP t)
```

(base-generic version: `Ideal.exists_ideal_over_maximal_of_isIntegral`). And in that same chart,
`ord_algebraMap_eq_ramificationIdx` (`Genus/Fundamental.lean:87`) turns
`ord_Q(θ - a) = 1` into `e(Q | placeP a) = 1`. **So "θ unramified at Q" and "θ - a vanishes to
order exactly 1 at Q" are literally the same statement, already bridged.**

### 4.5 Coordinator item (ii): "`θ` unramified at all but finitely many places"

You do **not** need this. You need the weaker and much cheaper

> the set of `a ∈ ℚ̄` such that *some* place over `x = a` is ramified in `Ē/ℚ̄(θ)` is finite,

because the only use is to exclude finitely many values of `c`.

**Cheapest route: the Galois closure, as a `LineCover` in the θ-chart.** `Ē/ℚ̄(θ)` is finite
separable but *not* Galois, so `Ē` itself cannot be a `LineCover` (Hole #3, see §6). Let `Ẽ` be
the Galois closure of `Ē` over `ℚ̄(θ)`. Then:

* `Ẽ` **is** a `LineCover` — build the term by supplying `LineCover.M := Twist … Ẽ` and every
  structure field explicitly, exactly as `RET/Twist.lean:156 LineCover.twist` does. `LineCover` is
  a *structure* with bundled instance fields, so there is no diamond (see §7.3).
* `finite_branchLocus` (`BranchSet.lean:96`) then gives a finite `Set k` of bad values.
* If `Q` of `Ē` has `e(Q|p_a) > 1` then any `Q̃` of `Ẽ` above `Q` has `e(Q̃|p_a) > 1`
  (`Ideal.ramificationIdx_algebra_tower`), so `a ∈ Ẽ.branchLocus`.

Cost: ~150 lines. **Cheaper than the discriminant route** of `RET/SeparableUnramified.lean`, whose
usable entry points

```lean
theorem LineCover.isUnramifiedAt_of_separable (L : LineCover) {x : L.M} …   -- :178
theorem LineCover.branchLocus_subset_of_separable (L : LineCover) {x : L.M} … -- :213
```

are themselves stated for a `LineCover` and would need the same Galois-closure detour *plus* an
explicit monic model. **Neither can be applied to a second algebra structure on `Ē` without the
type-synonym move; with it, both can.**

### 4.6 What the repo already has for "all but finitely many"

Honest answer: **almost nothing packaged.** I grepped. There is no `∀ᶠ`/`Filter.cofinite`
genericity lemma anywhere in `RET/` outside `Genus/Ord.lean:95`. Every genericity argument in the
repo is inlined as `Set.Finite.infinite_compl |>.nonempty`. The single closest analogue is
`RET/ProductTranslate.lean:61`:

```lean
theorem exists_translate_disjoint {S₁ S₂ : Set k} (hS₁ : S₁.Finite) (hS₂ : S₂.Finite) :
    ∃ a : k, Disjoint S₁ ((· - a) ⁻¹' S₂)
```

proved by `Set.Finite.image2` + `.infinite_compl.nonempty`, with `instance : Infinite k` at `:56`.
**This is exactly the shape of the `c`-choice** and should be reused (or generalised to a finite
family) verbatim.

The `LineSubst`/`Scale`/`Translate`/`MoveInfinity` lemmas
(`Translate.lean:94 IsUnramifiedOutside.twist_translate`,
`Scale.lean:211 IsUnramifiedOutside.twist_scale`,
`MoveInfinity.lean:119 exists_twist_isUnramifiedAtInfinity_ncard`) are all about moving *the line*,
not about moving a curve, and are **not** reusable here. Flagged as a dead end.

---

## §5. Recommended file decomposition

Superseding `WreathConstruction.md` §7's F4–F6. Total new Lean: **≈ 900–1200 lines**, versus the
≈ 2000+ implied by the inertia route.

| # | File | Size | Headline theorem |
|---|------|------|------------------|
| **W0** | `RET/Wreath/Independence.lean` | **exists, 119 lines, sorry-free** | `dvd_of_prod_zpow_eq_pow` — private valuations with gcd coprime to `n` force `n ∣ eᵢ`. |
| **W1** | `RET/Wreath/CyclicNormalForm.lean` | S, ~120 | `gcd (n, m₁,…,m_r) = 1` for the radicand produced by `exists_multiKummer_model`; i.e. the missing coprimality clause of the normal form. |
| **W2** | `RET/Wreath/CurvePlaces.lean` | M, ~250 | `ord_kappa` (✅ elaborates): `ord Ē v (∏ᵢ (u - sᵢ)^{mᵢ}) = Σᵢ mᵢ · ord Ē v (u - sᵢ)`; plus the `Ebarˣ → ℤ` additive-function packaging that feeds W0 (✅ elaborates), and `charZero_of_injective_algebraMap` boilerplate. |
| **W3** | `RET/Wreath/ConjNonConstant.lean` | S, ~100 | `transcendental_conj_sub` — a nontrivial conjugate difference is non-constant (§4.2). |
| **W4** | `RET/Wreath/ThetaChart.lean` | L, ~350 | `Ẽ`, the Galois closure of `Ē/ℚ̄(θ)`, as a `LineCover`; hence `Finite {a : k | some place over a is ramified in Ē/ℚ̄(θ)}` (§4.5). |
| **W5** | `RET/Wreath/PrivatePlace.lean` | L, ~300 | `exists_private_place` (✅ elaborates): for a good `c`, every `(h,i)` has a place of `Ē` with `ord(u_h - sᵢ) = 1` and `ord(u_{h'} - s_j) = 0`. Assembles W2+W3+W4 + `ProductTranslate.exists_translate_disjoint`. |
| **W6** | `RET/Wreath/CurveKummer.lean` | M, ~200 | Builds `Kummer.Setup Ē M̄ H n` from W1+W5+W0; concludes `Module.finrank Ē M̄ = n ^ Fintype.card H` by `Setup.finrank_eq`. |

**Deleted from the old plan:** F5 `Wreath/PullbackInertia.lean` (the "new geometry", L–XL ~700
lines) — not needed. F6 as originally scoped — already exists as W0. The `PiQuotient.lean`
reduction — still correct and still useful as a fallback, but **not on the critical path**, since
`Setup.finrank_eq` gives the degree directly.

**Dead ends, flagged:**

* Trying to make `Ē` a `LineCover` over `ℚ̄(θ)` directly. It is not Galois there.
* `Translate.lean` / `Scale.lean` / `MoveInfinity.lean` — these move the *line*, and `Ē` is a curve.
* A base-generic rewrite of `Descent/GeomAKLB.lean`. Tempting, ~200 mechanical lines, and it buys
  only lemma (b), which we are not building.
* `RadicalIndep.lean` / `dvd_of_pow_eq_phiF` (`:140`). It looks like exactly what W6 needs, but it
  is hard-wired to `RatFunc F` via `Polynomial.rootMultiplicity` on `num`/`denom` and there is no
  bridge to `Genus/Ord.lean`. Do not try to reuse it; W0 is the right abstraction.

---

## §6. Sanity check: holes

### Hole #1 — `φ_g` non-constant (§4.2). **Fatal as stated; fixed in three lines.**

### Hole #2 — poles missing from `B` (§4.3). **Real; fixed by one extra finite union.**

### Hole #3 — `Ē` is not Galois over `ℚ̄(θ)`

Both `BranchLocus.lean` and `SeparableUnramified.lean` route through `LineCover`, which *requires*
`[IsGalois (RatFunc k) M]`, and `BranchLocus.exists_unramifiedOutside_finite` (`:107`) rests on
`FaithfulSMul L.deck (Bring L.M)`. So neither applies to `Ē/ℚ̄(θ)`. The Galois-closure detour of
§4.5 is **not optional**; it is file W4 and it is the single largest new file in the plan.

### Hole #4 — `θ` need not be transcendental over `ℚ̄`

`θ` is a primitive element of `E/ℚ(T)`. If `H` is nontrivial and `E/ℚ(T)` is regular then `θ ∉ ℚ̄`
and hence (`ℚ̄` algebraically closed in `Ē`) `θ` is transcendental over `ℚ̄`. **But when `H` is
trivial, `E = ℚ(T)` and "a primitive element" may be a constant.** `Transcendental k θ` must
therefore be an explicit hypothesis (always satisfiable: replace `θ` by `θ + T`). Everything
downstream — `paramHom`, `u_h - s_i ≠ 0`, the θ-chart — depends on it.

### Hole #5 — the connectedness assumption (inertia route only)

The original brief silently assumes `Gal(N̄_h/Ē) ≅ A`, i.e. that the pullback is *connected*. That
is **not automatic**. It does follow from the same "onto" lemma (if `⨆_s I_s = A` and each
`I(Q̃|Q) ↠ I(q̃|s)` then the restriction is surjective, hence an isomorphism), so one lemma buys
both connectedness and generation — but the logical order must be stated. On the Kummer route this
hole disappears: `Setup.indep` implies `[Ē(κ(u_h)^{1/n}) : Ē] = n` for each `h` individually.

### Hole #6 — `e_Q = 1` is load-bearing, not cosmetic

If `ord_Q(u_h - s_i) = e > 1` then the private place gives only `n ∣ m_h · m_i · e`, which is
strictly weaker. Concretely `n = 2`, `m_1 = 1`, every place over `s_1 - c` with `e = 2`: the
constraint becomes `2 ∣ 2 m_h`, vacuous. This is the same phenomenon as the coordinator's `n = 6`
warning, one level down, and it is why W4 (finiteness of the ramified values) cannot be skipped.

### §6(i) — does private-place inertia really generate `A`?

**On the inertia route**, the relevant existing theorem is `RET/AbelianGeneration.lean:334`:

```lean
theorem exists_places_iSup_geomInertia_eq_top_of_comm (L : LineCover)
    (hab : ∀ a b : L.deck, a * b = b * a) {r : ℕ} (t : Fin r → k)
    (hS : L.IsUnramifiedOutside (Set.range t)) (hinf : L.IsUnramifiedAtInfinity) :
    ∃ Q : Fin r → Ideal (Bring L.M),
      (∀ i, (Q i).IsMaximal ∧ (Q i).LiesOver (placeP (t i))) ∧
        ⨆ i, geomInertia L.M (Q i) = ⊤
```

Two hypotheses to notice. It gives **one place per affine branch point**, and it requires
`L.IsUnramifiedAtInfinity` as an explicit hypothesis — the place at infinity is *not* included in
the supremum. So on the inertia route you would have to arrange the `N̄` model to be unramified at
`∞`, i.e. `n ∣ Σ mᵢ`, which is an extra normalisation. **On the Kummer route this hypothesis
evaporates**, because generation is replaced by the arithmetic condition
`gcd(n, m₁,…,m_r) = 1`, and `gcd(n, m₁,…,m_r, Σmᵢ) = gcd(n, m₁,…,m_r)`. This is a real advantage
of §7 that I did not expect to find.

For non-abelian deck groups only normal-closure and mod-commutator versions exist
(`AbelianGeneration.lean:589`, `:614`) — irrelevant here since `A` is abelian by hypothesis.

### §6(ii) — is `θ` unramified at enough points of each fibre?

Yes, **after** the fix in §4.5, and the reason is worth stating precisely: we do not need "many"
points of the fibre, only **one**, and we get it not by counting but by choosing `c` so that
`sᵢ - c` avoids the finite bad-value set. The fibre over a non-branch value is then *entirely*
unramified, so any point of it works, and it is nonempty by lying-over. **The coordinator's
formulation ("`θ` is unramified at all but finitely many points, so pick a good fibre") is the
harder statement; the branch-*value* formulation is both weaker and directly available from
`finite_branchLocus`.**

### §6(iii) — degenerate cases

* **`H` trivial.** The `φ_g` layer is vacuous (no `g ≠ 1`), the privacy conditions are empty, and
  the statement degenerates to "`[Ē(κ(u)^{1/n}) : Ē] = n`" — still meaningful and still needing
  W1+W2+W4+W5. The downstream statement `A ≀ᵣ 1 ≅ A` is correct. **But see Hole #4**: this is
  exactly the case where `θ` may be constant, so the `Transcendental k θ` hypothesis is doing real
  work here and nowhere else.
* **`n = 1`.** `A` trivial, `M̄ = Ē`, `finrank = 1 = 1^{|H|}`. `Kummer.Setup` needs `[NeZero n]`
  which `n = 1` satisfies; `indep` is vacuous since every integer is divisible by 1. Harmless, but
  note `exists_multiKummer_model` then produces `r = 0` and the "gcd = 1" clause of W1 must be
  stated so that it is true for `r = 0` (`Finset.gcd ∅ = 0`, and `IsCoprime 1 0` holds). **Check
  the `r = 0` edge in W1.**
* **`r = 1`.** Perfectly fine. `κ = (x - s₁)^{m₁}`, and W1 gives `gcd(n, m₁) = 1`, so a single
  private place per layer suffices. The cover `N̄` is then branched at `s₁` and `∞` only.
* **The place at infinity.** *I have been ignoring `∞`, deliberately, and here is why that is
  sound:* the normal form of `RET/KummerNormalForm.lean:153` produces `κ` as a **polynomial**
  `∏(T - tᵢ)^{eᵢ}` times an `n`-th power, so `v_∞(κ) = -Σ eᵢ`, generally nonzero mod `n`. But the
  private-place argument only ever evaluates `ord_Q` at places of `Ē` where `u_h` is **finite**
  (that is the content of the fix in §4.3). The place `∞` of the `x`-line is never used as a source
  of a private place, and no place of `Ē` above it is either. Its exponent `-Σ mᵢ` therefore never
  appears in any divisibility constraint. **The one thing that would break if it did — generation
  failing because `gcd` had to include `Σ mᵢ` — cannot happen, since `gcd(n, m₁,…,m_r, Σmᵢ) = gcd(n, m₁,…,m_r)`.**
* **`X` of genus `> 0`.** Nothing breaks. Not one step of the Kummer route uses genus, degree, or
  Riemann–Roch. This is the single strongest argument for §7 over §3: the inertia route would need
  the fundamental identity `Σ e·f = [Ē : ℚ̄(θ)]` on a curve of arbitrary genus
  (`Genus/Fundamental.lean:69`, which is available but requires the exact-constant-field
  hypothesis), whereas the Kummer route needs only lying-over.
* **Exact constant field.** `Ē` must have `ℚ̄` as its *exact* field of constants (equivalently
  `E/ℚ(T)` is regular). This is used for: `θ ∉ ℚ̄ ⇒ θ` transcendental (Hole #4); residue fields of
  places of `Ē` being `ℚ̄`; and `φ_g` constant `⇒ φ_g ∈ ℚ̄` (§4.2). It is a hypothesis of the whole
  construction and should appear in every signature.

---

## §7. The Kummer reformulation

### 7.1 Verdict, up front

**Yes. Build the Kummer route. Do not build the inertia route.** Two things I found make it not
merely simpler but *already half-built*.

### 7.2 Sub-question (a): does Mathlib support step 1 (cyclic ⟹ radical, with normal form)?

**Partly, and the repo has already closed the gap.**

Mathlib `FieldTheory/KummerExtension.lean`:

* `isCyclic_iff_exists_isSplittingField_X_pow_sub_C` — **does not exist**. I grepped the whole of
  Mathlib; zero hits. The classification is packaged as a TFAE plus two lemmas.
* `:464` is the "cyclic ⟹ radical" step, verbatim:

  ```lean
  lemma exists_root_adjoin_eq_top_of_isCyclic [IsGalois K L] [IsCyclic Gal(L/K)] :
      ∃ (α : L), α ^ (finrank K L) ∈ Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤
  ```
* `:542 isCyclic_tfae`, `:411 autEquivZmod`, `:441 finrank_of_isSplittingField_X_pow_sub_C`,
  `:378 autEquivRootsOfUnity` all exist as expected.
* `X_pow_sub_C_irreducible_iff_of_prime` is **not** in `KummerExtension.lean`; it is at
  `FieldTheory/KummerPolynomial.lean:123`.
* **There is no statement of "degree of `K(a^{1/n})` = order of `a` in `Kˣ/(Kˣ)ⁿ`" anywhere in
  Mathlib.** The only place Mathlib forms `Kˣ/(Kˣ)ⁿ` at all is a *local* notation in
  `RingTheory/DedekindDomain/SelmerGroup.lean:69`.

The repo closes both gaps, but only over `k = ℚ̄`:

`RET/KummerNormalForm.lean:153`:

```lean
theorem exists_multiA_mul_pow {n : ℕ} (hn : 0 < n) {a : RatFunc k} (ha : a ≠ 0) :
    ∃ (r : ℕ) (t : Fin r → k) (e : Fin r → ℕ) (b : RatFunc k),
      Function.Injective t ∧ (∀ i, e i < n) ∧ b ≠ 0 ∧
      a = algebraMap (Polynomial k) (RatFunc k) (multiA t e) * b ^ n
```

`RET/CyclicKummerModel.lean:38` (the *only* theorem in that file) is exactly step 1:

```lean
theorem exists_multiKummer_model (L : LineCover) [IsCyclic L.deck] :
    ∃ (r : ℕ) (t : Fin r → k) (e : Fin r → ℕ),
      Function.Injective t ∧ (∀ i, e i < finrank (RatFunc k) L.M) ∧
      Irreducible (X ^ finrank (RatFunc k) L.M -
          C (algebraMap (Polynomial k) (RatFunc k) (multiA t e))) ∧
      IsSplittingField (RatFunc k) L.M
        (X ^ finrank (RatFunc k) L.M -
          C (algebraMap (Polynomial k) (RatFunc k) (multiA t e)))
```

**Missing clause:** it does *not* record `gcd(n, e₁,…,e_r) = 1`. That is file **W1**, and it is
derivable from the `Irreducible` clause already present: if `d := gcd(n, eᵢ) > 1` then
`κ = (∏(T-tᵢ)^{eᵢ/d})^d`, so `X^n - κ` factors. ~120 lines.

### 7.3 Sub-question (c): is `LineCover` a structure or typeclass-based?

**It is a `structure` with bundled instance fields.** Verbatim, `RET/TamePi1.lean:47-60`:

```lean
structure LineCover where
  M : Type
  [field : Field M]
  [alg : Algebra (RatFunc k) M]
  [algPoly : Algebra (Polynomial k) M]
  [tower : IsScalarTower (Polynomial k) (RatFunc k) M]
  [findim : FiniteDimensional (RatFunc k) M]
  [isGalois : IsGalois (RatFunc k) M]

attribute [instance] LineCover.field LineCover.alg LineCover.algPoly LineCover.tower
  LineCover.findim LineCover.isGalois
```

There *is* a typeclass-driven smart constructor, `LineCover.of`, but the raw constructor takes all
six instances as explicit fields. **So a second `LineCover` term with a twisted algebra map is
constructible, and the repo already does exactly that twice:**

`RET/Twist.lean:54` and `:156`:

```lean
def Twist (_φ : RatFunc k ≃+* RatFunc k) (M : Type) : Type := M

def LineCover.twist (L : LineCover) (φ : RatFunc k ≃+* RatFunc k) : LineCover where
  M := Twist φ L.M
  field := Twist.instField φ L.M
  alg := Twist.instAlgebraRatFunc φ L.M
  algPoly := Twist.instAlgebraPoly φ L.M
  tower := Twist.instTower φ L.M
  findim := Twist.instFiniteDimensional φ L.M
  isGalois := Twist.instIsGalois φ L.M
```

and the *non-automorphism* precedent, `RET/LineSubst.lean:51`:

```lean
def LineSubst (_φ : RatFunc K →ₐ[K] RatFunc K) : Type _ := RatFunc K
```

used for the genuinely non-linear dihedral substitution at `DihedralBranch.lean:126`.

> **Answer: structure, with the type-synonym idiom as the established diamond-avoidance pattern.
> `RET/BranchLocus.lean`'s finiteness can be reused verbatim on a second algebra structure,
> provided the field is Galois over the new base — which is why W4 goes through the Galois
> closure `Ẽ` rather than `Ē` itself.**

### 7.4 Sub-question (b): the multi-radical independence criterion

**Mathlib: no.** Grepped exhaustively — `IsKummerExtension`, `IsRadicalExtension`,
`radicalExtension`: zero hits. `FieldTheory/Galois/Abelian.lean` is a bare class with no
classification. There is no multi-radical degree formula anywhere.

**The repo: yes, and it is base-generic.** `RET/KummerIndep.lean:38-51`, verbatim:

```lean
structure Setup (E L : Type*) [Field E] [Field L] [Algebra E L] (ι : Type*) [Fintype ι]
    (n : ℕ) where
  zeta : E
  g : ι → E
  w : ι → L
  isPrimitiveRoot : IsPrimitiveRoot zeta n
  g_ne_zero : ∀ i, g i ≠ 0
  w_pow : ∀ i, w i ^ n = algebraMap E L (g i)
  adjoin_eq_top : IntermediateField.adjoin E (Set.range w) = ⊤
  indep : ∀ (m : ι → ℤ) (y : E), y ≠ 0 → y ^ n = ∏ i, g i ^ m i → ∀ i, (n : ℤ) ∣ m i
```

with variable block `variable {E L : Type*} [Field E] [Field L] [Algebra E L]` (`:35`) and
`variable [NeZero n] [CharZero E] (S : Setup E L ι n)` (`:55`), and the payoff at `:373`:

```lean
theorem finrank_eq : Module.finrank E L = n ^ Fintype.card ι
```

plus `:363 galEquiv : (L ≃ₐ[E] L) ≃* (ι → rootsOfUnity n L)`, `:380 exists_aut`,
`:410 exists_aut_zpow`.

**No `RatFunc`, no `LineCover`, no algebraically closed constant field, no `IsGalois` hypothesis.**
The root of unity is *structure data*, so `μ_n ⊆ Ē` costs nothing. Verified to elaborate with
`E := Ē`: ✅

```lean
example {Mbar : Type} [Field Mbar] [Algebra Ebar Mbar] {H : Type} [Fintype H] [DecidableEq H]
    {n : ℕ} [NeZero n] (S : Kummer.Setup Ebar Mbar H n) :
    Module.finrank Ebar Mbar = n ^ Fintype.card H := S.finrank_eq
```

**Gotcha (small but real):** `CharZero Ē` is **not** found by instance search from
`[Algebra k Ē]`. ✅ verified failure, and ✅ verified fix:
`charZero_of_injective_algebraMap (algebraMap k Ebar).injective`. Every signature must carry
`[CharZero Ebar]` or a local `haveI`.

**And step 3 of the coordinator's argument already exists**, sorry-free, in
`RET/Wreath/Independence.lean` (untracked, 119 lines). Verbatim, `:110`:

```lean
theorem dvd_of_prod_zpow_eq_pow {G : Type*} [CommGroup G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} {n : ℕ} {a : ι → G} {e : ι → ℤ} {b : G} (hb : ∏ j, a j ^ e j = b ^ n) (i : ι)
    (s : Finset κ) (V : κ → G → ℤ) (hV : ∀ k ∈ s, ∀ x y, V k (x * y) = V k x + V k y)
    (hkill : ∀ k ∈ s, ∀ j, j ≠ i → V k (a j) = 0)
    (hcop : IsCoprime (n : ℤ) (s.gcd fun k ↦ V k (a i))) :
    (n : ℤ) ∣ e i
```

Its docstring even contains the coordinator's `n = 6` example. Note the design: **a valuation is a
bare function `G → ℤ` plus additivity**, precisely so that `ord Ē v` can be plugged in with no
API friction. Verified ✅:

```lean
example (v : HeightOneSpectrum B) : ∀ x y : Ebarˣ,
    (fun z : Ebarˣ => ord Ebar v (z : Ebar)) (x * y)
      = (fun z : Ebarˣ => ord Ebar v (z : Ebar)) x + (fun z : Ebarˣ => ord Ebar v (z : Ebar)) y :=
  fun x y => by simpa using ord_mul v (x.ne_zero) (y.ne_zero)
```

### 7.5 Step 2, made precise

With `u_h := θ_h + c ∈ Ē` and `g_h := κ(u_h) = ∏ᵢ (u_h - sᵢ)^{mᵢ}` — a product of *explicit
elements of `Ē`* — the valuation computation is `ord_prod` + `ord_pow`, verified to elaborate ✅:

```lean
theorem ord_kappa (v : HeightOneSpectrum B) {r : ℕ} (s : Fin r → k) (m : Fin r → ℕ) (u : Ebar)
    (hu : ∀ i, u - algebraMap k Ebar (s i) ≠ 0) :
    ord Ebar v (∏ i, (u - algebraMap k Ebar (s i)) ^ m i)
      = ∑ i, (m i : ℤ) * ord Ebar v (u - algebraMap k Ebar (s i))
```

**Confirmed: no composite valuations, no ramification index of `X → ℙ¹`, no tower of Dedekind
domains, no "pullback preserves inertia".** The coordinator's claim here is exactly right.

The private-place statement, also verified to elaborate ✅:

```lean
theorem exists_private_place {H : Type} [Group H] [Fintype H] [DecidableEq H]
    (θ : H → Ebar) {r : ℕ} (s : Fin r → k) (c : k) (h : H) (i : Fin r) :
    ∃ v : HeightOneSpectrum B,
      ord Ebar v (θ h + algebraMap k Ebar c - algebraMap k Ebar (s i)) = 1 ∧
      ∀ (h' : H), h' ≠ h → ∀ j, ord Ebar v (θ h' + algebraMap k Ebar c
        - algebraMap k Ebar (s j)) = 0
```

(with `variable {Ebar : Type} [Field Ebar] [Algebra k Ebar] {B : Type} [CommRing B]
[IsDedekindDomain B] [Algebra k B] [Algebra B Ebar] [IsFractionRing B Ebar]`). This is **the one
genuinely new theorem in the whole programme**, and §4 is its proof sketch.

### 7.6 Sub-question (d): does the Kummer route dominate?

| | inertia route (§3) | Kummer route (§7) |
|---|---|---|
| new Lean | ~2000+ lines | ~900–1200 lines |
| needs a base-generic AKLB rewrite | **yes** (~200 lines, plus 300 of chart bookkeeping) | no |
| needs "pullback preserves inertia" | **yes**, the hard lemma | no |
| needs connectedness of the pullback | **yes** (Hole #5) | no |
| needs `IsUnramifiedAtInfinity` of `N̄` | **yes** (`AbelianGeneration.lean:334`) | no (§6(i)) |
| needs genus/degree theory | for the fundamental identity, yes | no |
| already-built machinery reused | `InertiaTransport`, `SubCover`, `InertiaSub` | `Kummer.Setup` (**gives the theorem outright**), `Wreath/Independence` (**already written**), `Genus/Ord` |
| generality | any finite abelian `A` | cyclic `A` (which `Solvable/WreathCyclic.lean` already reduces to) |

**The Kummer route dominates on every axis. §3 should be regarded as background, not as a plan.**

The one caveat worth stating: `Kummer.Setup` handles a family of radicals *of the same exponent
`n`*, so a non-cyclic `A` would need a product of setups. `Solvable/WreathCyclic.lean` already
reduces to cyclic `A`, so this is not a live constraint — but if that reduction ever changes, the
Kummer route needs a `Setup` for each cyclic factor and a separate linear-disjointness argument,
which is where `PiQuotient.lean` would come back into play. **Keep `PiQuotient.lean`.**

---

## Appendix: names I looked for and did **not** find

Reported so nobody hunts for them again.

* `isCyclic_iff_exists_isSplittingField_X_pow_sub_C` — not in Mathlib.
* `Ideal.ramificationIdx_eq_one` — not in Mathlib (only `_iff`, `_of_map_localization`,
  `_of_isUnramifiedAt`). The docstring name
  `Ideal.ramificationIdx_eq_one_iff_of_isDedekindDomain` at `Basic.lean:181` is **stale**; the real
  name is `Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff` (`Basic.lean:257`).
* `Ideal.decompositionGroup`, `Ideal.stabilizer`, `Ideal.IsUnramifiedAt`, `Algebra.IsUnramified`,
  `Valuation.ramificationIdx`, `Valuation.IsUnramified` — none exist.
* `HeightOneSpectrum.comap` / `.under` / any functoriality — does not exist in Mathlib.
* `IsKummerExtension`, `IsRadicalExtension` — do not exist.
* Any Mathlib statement that a compositum of unramified extensions is unramified — does not exist.
* In the repo: no Möbius branch-locus transport for `LineCover`; no `branchLocus` transport for
  scaling or inversion; no `LineSubst`/`paramHom` branch-locus lemma; no packaged "inertia at `t`
  fixes `A` when `L.sub A` is unramified at `t`" (compose `SubCover.IsInertiaAt.restrict` `:204`
  with `SubcoverProduct.eq_of_subHom_eq_one` `:42`); no `∀ᶠ`/`Filter.cofinite` genericity lemma
  outside `Genus/Ord.lean:95`.
