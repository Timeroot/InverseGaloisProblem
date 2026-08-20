# `PSL₂(𝔽ₚ)` over `ℚ(T)`: Shih's theorem vs. index-two descent

*Assessment written 2026-08-20, on the `shih` branch.*

The goal is to realize the simple groups `PSL₂(𝔽ₚ)` as **regular** Galois groups over `ℚ(T)`.
There are two candidate routes. This document compares them, ranks the specific obstructions to
each, and records what has been formalized so far.

**Verdict: Route 2 (index-two descent) is cheaper by two or three orders of magnitude, but it is
still weeks of work, and it only reaches a finite list of primes. Route 1 (Shih) is not
formalizable with today's Mathlib; the gap is a multi-year algebraic-geometry programme.**

---

## The two routes at a glance

| | Route 1 — Shih, modular curves | Route 2 — index-two descent from `PGL₂(𝔽ₚ)` |
|---|---|---|
| Primes reached | all `p` with `(2/p) = -1` or `(3/p) = -1` or `(7/p) = -1`, i.e. density `7/8` | only `p` for which `PGL₂(𝔽ₚ)` has a *rational rigid triple*: `p ∈ {5, 7, 11, 13, 17, 19, 31, 37}` (a finite list) |
| Mathematical input | moduli of elliptic curves, Weil pairing, Atkin–Lehner, Shimura reciprocity | the rigidity method (already in this repo) plus ramification bookkeeping |
| Mathlib prerequisites | essentially all absent (see below) | all present |
| Repo prerequisites | none | `RigidityCertificate`, the full RET descent tower, the `PGL₂(𝔽₇)` certificate |
| Open `sorry`s today | 2 (both are the whole construction) | 2 (both are bridging lemmas over existing machinery) |
| Honest effort estimate | multi-year, and gated on a large Mathlib programme | 3–8 focused weeks |

Two remarks that matter for choosing:

* Route 2 does **not** subsume Route 1. `PGL₂(𝔽ₚ)` has a rational rigid triple only for finitely
  many `p` (see `docs/` note *Lie-type rigidity survey*: `q = 5, 7, 11, 13, 17, 19, 31, 37`, and
  *not* `23` or `29`). Shih covers seven eighths of all primes. So Route 2 is a shortcut to a few
  named groups, not to the family.
* Route 2 is genuinely worth doing anyway: the same index-two theorem also unlocks `M₂₂` from the
  landed `Aut(M₂₂) = M₂₂ : 2` certificate, which rigidity provably cannot reach directly (`M₂₂`
  has no rigid triple at all).

---

## Route 1: Shih's construction

### The mathematics

Fix a prime `p ≥ 5` and an auxiliary level `N ∈ {2, 3, 7}`.

1. The modular curve `X(p)` is a Galois cover of the `j`-line, defined over `ℚ`, with group
   `GL₂(𝔽ₚ)/{±1}`. Its constant field is `ℚ(ζₚ)`, and the restriction map to
   `Gal(ℚ(ζₚ)/ℚ) ≅ (ℤ/p)ˣ` is the determinant. The geometric monodromy group is therefore
   `SL₂(𝔽ₚ)/{±1} = PSL₂(𝔽ₚ)` — the right group, but with far too many constants.
2. Pull back along `X₀(N) → X(1)`. For `N ∈ {2, 3, 7}` the curve `X₀(N)` has genus `0` with a
   rational cusp, so `ℚ(X₀(N)) = ℚ(t)`, with hauptmoduln
   `j = (t+256)³/t²` (`N = 2`), `j = (t+27)(t+243)³/t³` (`N = 3`),
   `j = (t²+13t+49)(t²+245t+2401)³/t⁷` (`N = 7`).
3. The Atkin–Lehner involution `w_N` acts on `ℚ(t)` as a fractional linear substitution
   `t ↦ c/t`, and `ℚ(t)^{w_N}` is again a rational function field.
4. On moduli `w_N` sends `(E, C)` to `(E/C, E[N]/C)`; an `N`-isogeny multiplies the Weil pairing
   on the `p`-torsion by `N`, so a lift `ω` of `w_N` to the level-`p` tower acts on `μₚ` by
   `ζ ↦ ζ^N`.
5. If `N` is a quadratic non-residue mod `p`, `ω` moves the constants by a non-square multiplier,
   and the twisted tower over `ℚ(t)^{w_N}` is a **regular** `PSL₂(𝔽ₚ)`-extension.

### Which primes

Shih's hypothesis depends only on `p mod 168`. It **fails** exactly for
`p ≡ 1, 25, 47, 121, 143, 167 (mod 168)` — six of the forty-eight units mod `168`, density `1/8`.
The smallest excluded prime is `47`. Note `p = 7` qualifies (`3` is a non-residue mod `7`) and
`p = 23` qualifies (`7` is a non-residue mod `23`) — and `23` is precisely a prime that Route 2
misses, since `PGL₂(𝔽₂₃)` has no rational rigid triple.

This part is **fully formalized and proved** in `InverseGalois/Rigidity/Examples/Shih.lean`
(`Rigidity.Shih.shihPrime_iff`), together with the three underlying quadratic-residue criteria
(`isSquare_two_iff`, `isSquare_three_iff`, `isSquare_seven_iff`).

### Ranked list of Mathlib gaps blocking Route 1

A dedicated Mathlib survey was run for this assessment. Ranked by how much has to be built:

1. **Algebraic curves over a field, with genus, divisors and Riemann–Roch.** Zero coverage. Every
   later item depends on this. Mathlib has schemes and `AlgebraicGeometry.Proj`, but no theory of
   curves, no genus, no Riemann–Roch. *This alone is a large multi-year Mathlib project.*
2. **Modular curves as algebraic curves over `ℚ`.** Zero coverage. Mathlib has `Γ₀(N)`, `Γ₁(N)`,
   `Γ(N)` as subgroups of `SL(2, ℤ)` (`Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`),
   the upper half-plane with the Möbius action and a fundamental domain
   (`Mathlib/NumberTheory/Modular.lean`), modular forms, slash actions and cusps — but no quotient
   *curve*, no model over `ℚ`, no function field. `ModularCurve` does not exist as an identifier.
3. **Moduli interpretation.** Zero coverage of level structures, of the moduli functor, or of the
   modular interpretation of points. Mathlib has Weierstrass curves, the group law and the
   `j`-invariant, but no `E[n]` as a group scheme or Galois module.
4. **Isogenies and the Weil pairing.** Zero coverage of either. The Weil-pairing multiplier is
   *the* arithmetic content of Shih's twist; without it there is nothing to twist by.
5. **Shimura reciprocity / the modular Galois representation.** Zero coverage. The statement
   "`Gal(ℚ(X(p))/ℚ(j)) ≅ GL₂(𝔽ₚ)/{±1}`, with the determinant equal to the cyclotomic character"
   is the hard input; it needs items 1–4 first. Even the group-theoretic prerequisite
   `SL(2, ℤ) ↠ SL(2, ℤ/N)` is absent.
6. **Atkin–Lehner and Fricke involutions.** Zero coverage.
7. **`PGL`.** Does not exist in Mathlib in any form. `PSL(n, R)` exists only as a bare `abbrev`
   (`Matrix.ProjectiveSpecialLinearGroup`, `Mathlib/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean`)
   with no theorems attached — not even simplicity of `PSL(2, q)`, though the Iwasawa criterion is
   available and this repo's `Mathieu/PSL211Simple.lean` shows how to apply it.
8. **Regular extensions, rigidity, Hilbert irreducibility.** Absent from Mathlib — but *present in
   this repo*, so not actually a blocker.

Items 1–5 are the wall. Nothing short of a sustained Mathlib effort in arithmetic algebraic
geometry moves them.

### What of Route 1 *is* formalized here

`InverseGalois/Rigidity/Examples/Shih.lean` (unimported leaf; **2 open `sorry`s**) contains:

* **proved** — `ShihPrime`, `isSquare_mod_three`, `isSquare_mod_seven`,
  `isSquare_of_mod_four_eq_three`, `isSquare_two_iff`, `isSquare_three_iff`, `isSquare_seven_iff`,
  `shihPrime_iff` (the `mod 168` characterization), `exists_level`;
* **proved** — `atkinLehner`, `atkinLehner_mul_self`, `atkinLehner_sq`, and
  `exists_ringEquiv_atkinLehnerFixedField`: *the Atkin–Lehner quotient of a rational curve is
  rational*. This is step 3 above, and it is real content: it uses the repo's Möbius-substitution
  calculus (`RET/MobiusAut.lean`), Artin's theorem and Lüroth's theorem
  (`RET/FixedField.lean`, `Hilbert/Analytic/Luroth.lean`);
* **stated, not proved** — `LevelTower` (the level-`p` tower packaged as exactly the two facts the
  descent consumes: the determinant character is surjective with kernel `PSL₂(𝔽ₚ)`, and it is the
  character of the action on the constants), `AtkinLehner` (a lift of `w_N` with multiplier `N` on
  `μₚ`), and the two `sorry`s:
  * `levelTower_atkinLehner_exists` — the modular input (items 1–6 above);
  * `isRegularInverseGalois_of_atkinLehner` — the twist. This one is *pure group theory plus field
    theory* once the tower exists, and is the smaller of the two by far;
* **proved** — `shih`, the assembly of the two into the theorem statement.

So the deliverable "a precise Lean statement of Shih's theorem with a decomposition into named
intermediate lemmas, every provable leaf proved" is met; the two unproved leaves are exactly the
modular geometry and the twist.

### Effort estimate for Route 1

* `isRegularInverseGalois_of_atkinLehner` alone (assuming `LevelTower` and `AtkinLehner` as
  hypotheses): **2–4 weeks**. It is a `RegularFixedField`-style argument: identify the geometric
  subgroup, show `ω` normalizes it, show the multiplier being a non-square forces the extension to
  split off the constants, then apply `Rigidity.RET.isRegularGaloisGroupOverBase_fixedField` over
  the Atkin–Lehner line (which is already known to be rational).
* `levelTower_atkinLehner_exists`: **not estimable in person-months** with current Mathlib. It is
  gated on gaps 1–5 above. A defensible lower bound, assuming a Mathlib curves-and-Riemann–Roch
  library appears, is **1–2 person-years** on top of that.

---

## Route 2: index-two descent from `PGL₂(𝔽ₚ)`

### The mathematics

Let `cert` be a rigidity certificate for `A` with `r = 3` branch points, so the rigidity method
produces a regular `A`-cover `L/ℚ(T)` branched at three rational points `t₀, t₁, t₂` with branch
cycles `b₀, b₁, b₂` satisfying `b₀b₁b₂ = 1`. Let `H ⊴ A` have index `2`.

1. `b₀b₁b₂ = 1` forces **exactly two** of the `bᵢ` to lie outside `H`
   (`exists_two_notMem_of_index_two`, **already proved** in `Index2.lean`).
2. `F := L^H` is a regular quadratic extension of `ℚ(T)` (`finrank_sub`, **already proved**), so
   `F = ℚ(T)(√f)`.
3. `F/ℚ(T)` ramifies at `tᵢ` exactly when `bᵢ ∉ H`, and nowhere else. So exactly two finite places
   ramify and `f = c(T - tᵢ)(T - tⱼ)` up to squares.
4. The conic `y² = c(x - tᵢ)(x - tⱼ)` has the rational point `(tᵢ, 0)`, so `F ≅ ℚ(u)`
   (explicitly `u = y/(x - tᵢ)`, `x = (u²tᵢ - ctⱼ)/(u² - c)`) —
   `nonempty_algEquiv_ratFunc_of_conic`, **already proved**.
5. `L/F` is then a regular `H`-extension of a rational function field:
   `IsRegularInverseGalois H` (`isRegularInverseGalois_of_index_two`, **already proved**).

### Current state of `InverseGalois/Rigidity/RET/Descent/Index2.lean`

Unimported leaf, ~400 lines, **2 open `sorry`s**.

**Proved:**

* `algebraicClosure_eq_bot_of_algHom` — regularity passes to subfields.
* `exists_two_notMem_of_index_two` — the parity count on a product-one generating triple.
* `nonempty_algEquiv_ratFunc_of_transcendental` — a field generated over `k` by one transcendental
  element is `RatFunc k`. Reusable; no such lemma exists in Mathlib (the repo's
  `RatFunc.exists_algEquiv_ratFunc` in `Hilbert/Analytic/Luroth.lean` only handles a generator
  that already lives inside `RatFunc k`).
* `transcendental_algebraMap_X` — the coordinate stays transcendental in any extension of `k(T)`.
* `nonempty_algEquiv_ratFunc_of_conic` / `nonempty_ringEquiv_ratFunc_of_conic` — **step 4 of the
  index-two argument, in full**: if `F = k(T)(y)` with `y² = c(T-a)(T-b)`, `a ≠ b`, `c ≠ 0`, then
  `F ≅ RatFunc k` over `k`, via `u = y/(T-a)`.
* `nonempty_algEquiv_rat_of_ringEquiv` — a ring isomorphism of characteristic-zero fields is a
  `ℚ`-algebra isomorphism. Needed to cross the `Algebra ℚ (RatFunc ℚ)` instance diamond
  (`DivisionRing.toRatAlgebra` vs `RatFunc.instAlgebraOfPolynomial`), which bites whenever an
  `AlgEquiv` over a general base field `k` is instantiated at `k = ℚ`.
* `BranchedRegularCover.finrank_sub` — `[L^H : ℚ(T)] = H.index`, by the Galois correspondence.
* `BranchedRegularCover.sub_algEquiv_ratFunc` — now **derived** from `exists_conic_generator`.
* `BranchedRegularCover.isRegularGaloisGroupOverBase_sub` and the assembly
  `isRegularInverseGalois_of_index_two`.

**Open:**

* `branchedRegularCover_of_certificate : RigidityCertificate A → Nonempty (BranchedRegularCover A cert.r)`
* `exists_conic_generator : (c : BranchedRegularCover A 3) → H.index = 2 → ∃ i j d y, i ≠ j ∧ d ≠ 0 ∧ y² = d(T - tᵢ)(T - tⱼ) ∧ ℚ(T)⟮y⟯ = ⊤`

The second sorry is what `sub_algEquiv_ratFunc` used to be, minus the conic step, which is now
proved. It is exactly the *ramification* content of the argument: Kummer theory plus the
identification of the ramified places.

### Why `branchedRegularCover_of_certificate` is not a one-liner

A survey of the descent tower for this assessment found that **the existing chain destroys exactly
the data `BranchedRegularCover` asks for**, at three points:

1. `Descent/BranchCycles.lean:112` — `geomCompositum_exists_of_cover_unramified` returns
   `hcov : c.cover.IsUnramifiedOutside (Set.range t)`, and `geomCompositum_branchCycles_exists`
   throws it away. This is the loss point for the `inertia_bot` field.
2. `Descent/Tower.lean:942 geomTower_nonempty` — the passage
   `ClassInertiaPlaceData → CycloBranchData → GeomTower` drops `branch`, `place` and
   `gen_inertia`. Everything downstream (`Descent.lean` and the public
   `RigidityCertificate.isRegularInverseGalois`) is branch-blind. This is the loss point for
   `inertia_eq`.
3. `Descent/FieldTranslation.lean:59 descentTranslation` — its output is the bare `Prop`
   `IsRegularInverseGalois G`; the field `Ω^{ker ψ'}` and the isomorphism are existentially buried.

Consequently one cannot route through `branch_cycle_descent`; the construction has to be re-run
from `geomCompositum_exists_of_cover_unramified` and `classInertiaPlaceData_of_branchCycles`,
keeping the data. Two genuinely **new** lemmas are needed on top of that:

* **Geometric inertia surjects onto arithmetic inertia.** `Descent/GeomArithBridge.lean:160
  mem_inertia_bridge` goes geometric ⟶ arithmetic only. To turn `geomInertia = zpowers g` into
  `arithInertia = zpowers (…)` (rather than `⊇`), and to turn geometric unramifiedness into
  `arithInertia = ⊥`, the reverse direction is required and does not exist anywhere in the repo.
  A full grep confirms the only arithmetic-side `inertia = ⊥` in the tree is
  `Specialization.lean:334 inertia_trivial_of_separable`, whose hypothesis is separability of a
  specialization at an integer, not "outside the branch locus".
* **Inertia transport down to the fixed field.** `InertiaPlaceData`'s places live on the big tower
  `m.Ω`, whereas `BranchedRegularCover.L` must be the regular field `Ω^{ker ψ'}` produced by
  `RegularFixedField.lean`. Primes have to be contracted along `L ↪ m.Ω`; the repo's transport
  lemmas (`InertiaTransport.lean`, `GeomArithBridge.lean`) all go the other way.

Two smaller mismatches: `InertiaPlaceData` has no `Function.Injective branch` field and records
inertia only as a *membership* (`gen_inertia`), although the *generation* statement
`geomInertia L.M (Q i) = Subgroup.zpowers (g i)` is available and discarded at `Tower.lean:743`.
Branch points are freely choosable (`geomRET` takes any injective `t : Fin r → k`;
`classInertiaPlaceData_of_branchCycles` takes `branch` as an explicit argument), so
`branch i = i` is fine.

### Why `exists_conic_generator` is not a one-liner

Of steps 2–4 above, step 4 is now done. What remains:

* **Kummer**: a degree-`2` Galois extension in characteristic `0` is `ℚ(T)(√f)`. Standard (take
  `β = α - σα`), maybe 100 lines. `finrank_sub` supplies the degree.
* **Ramification ↔ odd valuation of `f`**: this is the substantial part. It has to connect the
  structure's `inertia_eq`/`inertia_bot` (stated for `ArithAKLB.arithInertia` of `L`) with the
  divisor of `f` in `ℚ[X]`, through the intermediate field `F`. There is no "inertia of a
  subextension" API on the arithmetic side.
* **The conic** — **done**: `nonempty_algEquiv_ratFunc_of_conic`, about 80 lines, resting on the
  new general `nonempty_algEquiv_ratFunc_of_transcendental`.

Alternatives considered and rejected: pulling back along a degree-`2` map (the same identification
problem reappears); genus / Riemann–Hurwitz (the repo's `Genus/` modules do not reach function
fields of conics); getting `deg f ≤ 2` without ramification data (impossible — `deg f ≤ 3` is all
that unramifiedness alone gives, and a degree-`3` `f` is an elliptic curve, generally not
rational).

### Effort estimate for Route 2

* `exists_conic_generator`: **1.5–3 weeks** (down from 2–4: the conic step is now proved, and
  `finrank_sub` is in place; what is left is Kummer plus the ramification bookkeeping, and the
  ramification bookkeeping was always the bulk of it).
* `branchedRegularCover_of_certificate`: **2–5 weeks**, most of it in the "geometric inertia
  surjects onto arithmetic inertia" lemma and in re-running the compositum construction while
  keeping the unramifiedness hypothesis.
* Then `PSL₂(𝔽₇)` needs one more concrete step: an explicit isomorphism between the index-two
  subgroup `ker(sign ∘ PGL2F7.subtype) ≤ Equiv.Perm (Fin 8)` and `PSL(2, ZMod 7)`. `PGL2F7` is
  built in `Examples/PGL27.lean` as a permutation group precisely to avoid `Nat.card` reasoning,
  so the identification is an explicit-generator computation in the style of
  `Mathieu/PSL211Simple.lean`: **3–7 days**.

Total: **2.5–7 focused weeks** for `PSL₂(𝔽₇)` (plus `M₂₂` essentially for free), against
"not this decade" for the Shih family.

---

## Recommendation

1. Do Route 2. It is the only realistic path to any `PSL₂(𝔽ₚ)` in this repo, and it pays for
   `M₂₂` at the same time.
2. Attack `exists_conic_generator` first: it needs no new tower plumbing, only field theory, and it
   is the half that generalizes (any `r = 3` certificate with an index-two subgroup). Its conic
   step and its degree computation are already done.
3. Keep `Examples/Shih.lean` as the standing statement of what the modular route would give, and
   revisit it only if Mathlib acquires curves and Riemann–Roch.
4. Both files must stay out of `InverseGalois.lean` and out of every `defaultTargets` root until
   they are `sorry`-free.
