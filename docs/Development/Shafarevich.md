# Solvable groups over ℚ: a literature and feasibility study

**Target.** Shafarevich's theorem: *every finite solvable group is a Galois group over ℚ*.

**Purpose.** Decide what part of the classical route is formalizable in Lean/Mathlib given what
this repository already has (regular realizations of every finite abelian group over ℚ(T), Sₙ, Aₙ,
dihedral, rigidity for many simple groups, Hilbert irreducibility with integer specializations,
closure of realizability under quotients and coprime products), and what part is out of reach
because it rests on class field theory.

**Executive summary.**

* The *full* Scholz–Reichardt theorem, as written by Serre, needs **class field theory twice**
  (Brauer–Hasse–Noether, and Kronecker–Weber/local CFT to glue local characters) and
  **Chebotarev once**. Neither is in Mathlib and both are multi-year projects.
* But the Chebotarev use compresses to a *strictly weaker* statement than Dirichlet's theorem,
  and Mathlib already has its analytic core (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`).
* The genuinely reachable target is **not** Scholz–Reichardt but **Ikeda's theorem** and the
  class of **semiabelian groups**, which is CFT-free, Chebotarev-free, and whose two inputs
  (regular abelian realizations over a base field, and Hilbert irreducibility) are *exactly* the
  two things this repository already owns. That is the recommendation.

---

## 0. Status (2026-08-21) — what has since been formalized

This section is later than the rest of the document and supersedes it where they disagree. The
study below rated Shafarevich "do not start"; that verdict was about the *arithmetic*, and it
still stands. But the split was drawn in the wrong place. The **group-theoretic half is not
expensive at all**, and it is now done — sorry-free and axiom-free.

**Landed in `InverseGalois/Solvable/Shafarevich/`:**

| file | content |
|---|---|
| `Frattini.lean` | `exists_nilpotent_normal_supplement` — Ore's supplement theorem |
| `SemidirectAssoc.lean` | `SemidirectProduct.prodAssoc : (A × B) ⋊ U ≃* A ⋊ (B ⋊ U)` |
| `Reduction.lean` | `SplitNilpotentEP`, and Ore's induction on the order |
| `PrimePower.lean` | `splitNilpotentEP_of_splitPrimePowerEP` — Sylow splitting of the kernel |
| `Main.lean` | the capstones |
| `SplitAbelian.lean` | the unconditional abelian case |

The headline is

```lean
theorem Shafarevich.isSolvable_isInverseGalois_of_splitPrimePowerEP
    (hEP : SplitPrimePowerEP) (G : Type) [Group G] [Finite G] [IsSolvable G] :
    IsInverseGalois G
```

**Shafarevich's theorem now follows from one statement**, `SplitPrimePowerEP`: *if a finite group
`U` is a Galois group over `ℚ` and `H` is a finite `p`-group with a `U`-action, then `H ⋊[φ] U` is
a Galois group over `ℚ`.* No group theory is left.

The whole reduction is carried out for an **abstract realization predicate** `P : ∀ (G : Type)
[Group G], Prop`, the only structural input being `Shafarevich.IsQuotientClosed P` (transport along
a surjection) together with the trivial group. So it specializes for free to the regular predicate
over `ℚ(T)`: `isSolvable_isRegularInverseGalois_of_splitPrimePowerEP` is the same theorem with
`IsRegularInverseGalois` throughout. That statement is of course still conditional, and on a
hypothesis that is *not* known — see "A warning about the regular route" below: regular
realizability of an arbitrary ℓ-group over `ℚ(T)` is an open problem, so there is no theorem there
to discharge it with. It is recorded because the reduction genuinely is predicate-independent.

Two remarks on how this differs from the plan in §5:

* **The Fitting subgroup is not needed, and is absent from Mathlib for groups.** Ore's theorem is
  proved instead through `frattini` plus a Gaschütz argument (two Frattini arguments via
  `Sylow.normalizer_sup_eq_top`, then `frattini_nongenerating`). The Gaschütz step is stated
  quotient-free as `⁅N,N⁆ ≤ frattini G ∧ frattini G ≤ N ⇒ Group.IsNilpotent N`, which avoids
  `↥N ⧸ …` entirely.
* **The abelian and nilpotent cases do not meet.** `SplitAbelian.lean` records that a split
  embedding problem with *abelian* kernel is already unconditional here, via the Dentzer–Stoll
  wreath construction. It does not bootstrap: filtering a `p`-group kernel by its centre turns one
  split problem into a split problem with abelian kernel **plus a residual lifting that is no
  longer split**, and that lifting is exactly where class field theory is unavoidable. This is the
  structural reason Ikeda/wreath reaches precisely the semiabelian groups and stops.

**Arithmetic bricks landed alongside:**

* **Milestone 7 is done.** `InverseGalois/NumberTheory/SplitCompletely.lean` proves Schur's theorem
  on prime divisors of polynomial values (`infinite_setOf_prime_dvd_eval`) and deduces Serre's
  Lemma 2.1.4, `infinite_setOf_prime_splitsCompletely`: for `K/ℚ` Galois, infinitely many rational
  primes split completely in `K`. Elementary — no density theory, no L-functions, no Chebotarev.
  Note that Mathlib has **no** "splits completely" predicate, so `SplitsCompletely` is defined here
  as "every prime above `p` has ramification index and inertia degree one".
* **Milestone 6 is done, in full and unconditionally.** Three files:
  * `IdealNormCount.lean` proves `n ↦ #{I ⊴ 𝒪_K : absNorm I = n}` multiplicative and derives the
    **Euler product for `NumberField.dedekindZeta`** indexed by the rational primes — which Mathlib
    does not have. The proof uses no unique factorization of ideals, only `absNorm I ∈ I` together
    with Bézout comaximality.
  * `IdealEulerProduct.lean` gives the Euler product in its intrinsic form,
    `dedekindZeta_eulerProduct_primeIdeal : ∏' 𝔭, (1 - N𝔭^{-s})⁻¹ = ζ_K(s)` for `re s > 1`. There is
    no Euler product for a Dedekind domain anywhere in Mathlib — everything under
    `Mathlib/NumberTheory/EulerProduct/` is ℕ-indexed — so this is built from scratch, mirroring
    the structure of `EulerProduct/Basic.lean`.
  * `SplitDensity.lean` defines `HasDirichletDensity` (Mathlib has no notion of prime density at
    all) and proves `hasDirichletDensity_splitSet`: **the primes splitting completely in a Galois
    number field of degree `n` have Dirichlet density `1/n`.** Hence the payoff, **statement (★) of
    §1.5**, unconditionally:

    ```lean
    theorem infinite_setOf_splitsCompletely_not_splitsCompletely
        (A B : Type*) [Field A] [NumberField A] [IsGalois ℚ A]
        [Field B] [NumberField B] [IsGalois ℚ B]
        (hlt : Module.finrank ℚ A < Module.finrank ℚ B) :
        {p : ℕ | p.Prime ∧ SplitsCompletely A p ∧ ¬ SplitsCompletely B p}.Infinite
    ```

    This is the **only** consequence of Chebotarev's theorem that Scholz–Reichardt actually needs,
    so the whole of class **(c)** in the §1.4 classification is now discharged. Note the hypotheses
    differ slightly from (★) as stated in §1.5: no containment `A ⊆ B` and no index condition are
    required, a degree inequality suffices, but **both** fields must be Galois over `ℚ`, not just
    `B`. In the Scholz–Reichardt application that is free — the field `A` there is a compositum of
    Galois extensions of `ℚ`. Two side-products worth
    noting: `finite_ramifiedSet` (only finitely many rational primes ramify) had to be proved here,
    since Mathlib has no "ramified ⇒ divides discriminant"; and `log ζ_K` is built as
    `∑' 𝔭, -log(1 - N𝔭^{-s})` directly rather than by taking a logarithm of the product.

---

## 0.1 Status (2026-08-21, later the same day) — the class field theory layer

Milestone 9 has since been done. **Mathlib contains no class field theory at all** — no Chebotarev
in general, no Grunwald–Wang, no Kronecker–Weber, no Hasse norm theorem, no Artin map, no ray class
groups, no ideles, no local class field theory, no Tate cohomology, no cup products, no Herbrand
quotients, no Hochschild–Serre, no `K^ur`, no Krasner's lemma, no crossed products, no relative
Brauer group, no local invariant `inv_v : Br(K_v) → ℚ/ℤ`. `Mathlib/Algebra/BrauerGroup/Defs.lean`
carries the Brauer *monoid* of central simple algebras; the group law, Galois descent, and the
uniqueness half of Wedderburn's theorem were all absent (Wedderburn uniqueness is still an explicit
Mathlib TODO, and `L ⊗[K] L ≃ (Gal(L/K) → L)` does not exist there either). The class
`IsNonarchimedeanLocalField` (`Mathlib/NumberTheory/LocalField/Basic.lean`) exists but has **zero
instances**: not even `ℚ_[p]` is one.

So the whole layer had to be built. It lives in `InverseGalois/CFT/`, is indexed by
`InverseGalois/CFT.lean`, and is sorry-free and axiom-free throughout (`#print axioms` gives
`[propext, Classical.choice, Quot.sound]` on every capstone).

| group | content |
|---|---|
| `CFT/GaloisDescent.lean` | Galois descent for modules, absent from Mathlib |
| `CFT/GroupCohomology/*` | cocycle ↔ `H²` dictionary, corestriction and the `[G : S] • id` relation, killing by the order of the group, normal form for cocycles of a cyclic group, `H²(cyclic) = invariants / norms` |
| `CFT/Brauer/CrossedProduct*.lean` | the crossed product `⨁_σ L·u_σ`: central simple, split by `L`, multiplicative in the cocycle, trivial exactly for a coboundary |
| `CFT/Brauer/Centralizer.lean`, `Split.lean`, `SkolemNoether.lean`, `Division.lean` | the double centralizer theorem, Skolem–Noether, Wedderburn's theorem in the split case, the division representative |
| `CFT/Brauer/SplittingSubfield.lean`, `CrossedProductRecognition.lean`, `H2Surjective.lean` | **`Br(L/K) ≅ H²(Gal(L/K), Lˣ)`** for every finite Galois `L/K`, and hence `Br(L/K)` is killed by `[L : K]` |
| `CFT/Brauer/CyclicBrauer.lean`, `CyclicNorm.lean` | for `L/K` cyclic, **`Br(L/K) ≅ Kˣ / N_{L/K}(Lˣ)`** |
| `CFT/Brauer/MaximalSubfield.lean` | maximal commutative subalgebras; every Brauer class is split by a finite subextension of the algebraic closure |
| `CFT/Brauer/Quaternion.lean`, `RealPlace.lean` | `-1` is not a norm from `ℂ` or from `ℚ(i)`, so `Br(ℂ/ℝ)` and `Br(ℚ(i)/ℚ)` are nontrivial; **`Br(ℂ/ℝ) ≅ ℤ/2`** |

This is the classical Brauer-group half of local class field theory, over an arbitrary field. What
it does **not** contain, and what item 2 of the §1.4 table needs, is the *arithmetic* input:
the local invariant maps and the exactness of
`0 → Br(K) → ⊕_v Br(K_v) → ℚ/ℤ → 0` (Albert–Brauer–Hasse–Noether). Those need the local theory —
unramified extensions of a local field, the valuation-theoretic computation
`Br(K^ur/K) ≅ ℚ/ℤ`, and then global reciprocity — none of which is reachable from here, and the
first of which cannot even be stated until `ℚ_[p]` is made an instance of the local-field class.

## 0.2 Status (2026-08-21) — the reduction, sharpened twice more

`SplitPrimePowerEP` is no longer the frontier. Two further purely group-theoretic reductions have
landed:

* `Shafarevich/AbelianKernel.lean` peels the centre off a `p`-group kernel one layer at a time. The
  centre is characteristic, so the quotient carries an induced action and the projection
  `H ⋊[φ] U → (H/Z) ⋊[φ'] U` has commutative kernel; induction on the order gives
  `splitPrimePowerEP_of_abelianKernelEP`. The hypothesis is now about embedding problems that are
  no longer split, but whose kernel is **abelian**:
  ```lean
  def AbelianKernelEP : Prop :=
    ∀ (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (π : E →* W),
      Function.Surjective π → IsMulCommutative π.ker → IsInverseGalois W → IsInverseGalois E
  ```
* `Shafarevich/MinimalKernel.lean` filters that abelian kernel further, down to a **minimal
  elementary abelian** one.

Both reductions are again carried out for an abstract quotient-closed predicate, so the regular
analogues over `ℚ(T)` come for free.

**Revised verdict.** Milestone 9 is done. Milestones 8, 10 and 11 — Kronecker–Weber,
Scholz–Reichardt, Shafarevich's arithmetic core — remain out of reach, for exactly the reasons
given in §4.1, and the two blockers are precisely rows 2 and 5 of the §1.4 table:
Albert–Brauer–Hasse–Noether, and the gluing of local abelian characters (which over `ℚ` *is*
Kronecker–Weber). Everything else on the route is now either done or elementary. What has changed
is that the non-arithmetic scaffolding is no longer a cost, that the crossed-product side of the
Brauer group is available in full, and that the target is a single, precisely stated,
self-contained proposition about embedding problems with minimal elementary abelian kernel.

## 0.3 Status (2026-08-22) — the degree-two slice of the arithmetic is done

§0.1 named the missing arithmetic input as "the local invariant maps and the exactness of
`0 → Br(K) → ⊕_v Br(K_v) → ℚ/ℤ → 0`". **In degree two, over `ℚ`, that is now proved**, by an
argument that goes around the invariant maps entirely rather than through them: in exponent two the
whole sequence degenerates into a statement about ternary quadratic forms, and Legendre's descent
proves it directly.

| statement | file |
|---|---|
| the local Hilbert symbol at every place of `ℚ`, bimultiplicative, computed explicitly | `CFT/Local/*` |
| **Hilbert reciprocity** `∏_v (a, b)_v = 1` | `CFT/Global/Reciprocity.lean` |
| **Hasse–Minkowski for ternary forms over `ℚ`** | `CFT/Global/HasseMinkowski.lean` |
| **the Hasse norm theorem for `ℚ(√b)/ℚ`** = ABHN for quaternion algebras over `ℚ` | `CFT/Global/HasseNorm.lean` |
| **Hasse–Minkowski for diagonal forms in any number of variables** | `CFT/Global/DiagHasse.lean` |
| the same, freed of the invertibility hypothesis, and as a principle for **representing** a rational number | `CFT/Global/DiagRepr.lean` |
| a diagonal form in ≥ 5 variables is isotropic at every **odd** place, so only `ℝ` and `ℚ₂` matter | `CFT/Global/OddQuinary.lean` |
| the real place by inspection, and the resulting two-condition criterion in ≥ 5 variables | `CFT/Global/RealSigns.lean` |
| **Hasse–Minkowski for an arbitrary (non-diagonal) rational form**, via congruence to a diagonal one | `CFT/Global/MatHasse.lean` |
| a diagonal form in five dyadic **units** is isotropic, hence the ≥ 5-variable criterion for **odd integer** coefficients is the sign condition alone | `CFT/Local/DyadicQuinary.lean` |
| nondegeneracy of the **dyadic** Hilbert symbol: `[ℚ_2^× : N(L^×)] = 2` and `Br(L/ℚ_2) ≅ ℤ/2` | `CFT/Local/DyadicNondegenerate.lean` |
| **`IsNonarchimedeanLocalField ℚ_[p]`**, with `𝒪[ℚ_[p]] ≃+* ℤ_[p]` compact, complete, discrete, finite residue field | `CFT/Local/PadicLocalField.lean` |
| a diagonal dyadic form with three unit coefficients and one of valuation one is isotropic | `CFT/Local/DyadicQuaternary.lean` |
| isotropy is invariant under rescaling coefficients by squares or by a common scalar; dyadic square-class normalisation | `CFT/Global/DiagScale.lean` |
| **`u(ℚ₂) ≤ 4`**: every diagonal form over `ℚ₂` in ≥ 5 variables is isotropic | `CFT/Global/Meyer.lean` |
| **Meyer's theorem**: a diagonal rational form in ≥ 5 variables is isotropic iff it is indefinite, and then represents everything the real place allows | `CFT/Global/Meyer.lean` |
| `u(ℚ_p) ≤ 4` at **every** finite place, and Meyer's theorem for an arbitrary symmetric rational matrix: rational zero iff real zero | `CFT/Global/Meyer.lean` |
| every `p`-adic form in ≥ 5 variables, diagonal or not, is isotropic, and a diagonal one with nonvanishing coefficients is **universal** | `CFT/Global/Meyer.lean` |
| **`u(ℚ₂) = 4` exactly**: the sum of four squares is anisotropic over `ℚ₂`, so five variables are genuinely needed | `CFT/Local/DyadicAnisotropic.lean` |
| **`u(ℚ_p) = 4` exactly, at every finite place**: at an odd place the unramified norm form plus its multiple by the uniformiser is anisotropic | `CFT/Local/OddAnisotropic.lean` |
| the five-variable hypothesis in Meyer's theorem is **sharp**: `⟨1, -5, -2, 10⟩` is isotropic over `ℝ` but anisotropic over `ℚ` | `CFT/Local/DyadicNormFive.lean` |

All sorry-free and axiom-free. See `docs/Development/ClassFieldTheory.md` for the full map of the
layer, the proof architecture of the descent, and why it is not circular with reciprocity.

**This does not move the Shafarevich frontier.** Scholz–Reichardt needs ABHN for **odd** `ℓ`, and
nothing in the ternary-forms argument survives the passage from exponent `2` to exponent `ℓ`: the
whole point of the degree-two case is that a Brauer class of order two is a conic, which has no
analogue. Rows 2 and 5 of the §1.4 table — ABHN in general, and the gluing of local abelian
characters — remain exactly as stated in §0.2. What has changed is that the *degree-two* theory is
complete and usable. The target named here a day earlier — Serre's existence theorem for Hilbert
symbols, i.e. exponent-two Grunwald–Wang, and thence Hasse–Minkowski in `n` variables — has since
been reached: the general-`n` Hasse principle is proved by induction on the number of variables
with the quinary argument as the inductive step, and the odd-place computation then shows that
from five variables on only the real and the dyadic place carry information. The diagonalisation
step is supplied too — every symmetric matrix over a field in which `2` is invertible is congruent
to a diagonal one, and congruence preserves isotropy and commutes with base change — so Serre's
chapter on Hasse–Minkowski is complete for an arbitrary rational quadratic form, not only for a
diagonal one. What is *not* reachable from any of this is the `u`
-invariant of `ℚ₂`, whose proof runs through the classification of `2`-adic forms by their Hasse
invariant. **That gap has since been closed, by a different route.** Rather than classify `2`-adic
forms, normalise the five coefficients to units or twice units by square classes: if all five are
of one kind the quinary unit form settles it, after dividing the whole form by two in the second
case; otherwise, among five booleans not all equal, three agree and a fourth differs, so a
four-variable subform has three coefficients of one kind and one of the other, and that quaternary
form is isotropic by a second modulo-eight search. Hence `u(ℚ₂) ≤ 4`, and with the odd places and
the real place, **Meyer's theorem**: a diagonal rational form in at least five variables is
isotropic exactly when it is indefinite. So the `u`-invariant statement and Meyer's theorem, both
named unreachable a few hours earlier, are proved. The bound is sharp: the sum of four squares is
anisotropic over `ℚ₂` by the same modulo-eight congruence, so `u(ℚ₂) = 4` exactly. At an odd place the
obstruction is a valuation instead of a congruence — the norm form of the unramified quadratic
extension takes only values of even valuation, so adjoining its multiple by the uniformiser gives
an anisotropic quaternary form — and hence `u(ℚ_p) = 4` at **every** finite place.

One remark of §0.1 is now obsolete. It said that the local invariant maps "cannot even be stated
until `ℚ_[p]` is made an instance of the local-field class"; `CFT/Local/PadicLocalField.lean`
supplies that instance — the first anywhere, Mathlib's `IsNonarchimedeanLocalField` having had
none — so the statements of local class field theory are now expressible over `ℚ_[p]`. Being able
to state them is not being able to prove them: ABHN itself is untouched.

---

## 0.4 Status (2026-08-22, later) — auditing the seven inputs against the code

§1.4 below classifies the arithmetic that Scholz–Reichardt consumes into seven inputs. That table
was written before the class field theory layer existed. Re-reading it against what is now in the
repository changes the picture substantially: **five of the seven are done or elementary, and only
one is genuinely out of reach.**

| § 1.4 input | rating there | actual status |
|---|---|---|
| 1. choice of `q` in the split case | (a) | **done** — `CFT/Scholz/PrimeChoice.lean` |
| 2. `H²(ℚ, C_ℓ) → ∏_p H²(ℚ_p, C_ℓ)` injective (ABHN) | (d) | **the one real blocker** |
| 3. local liftability at unramified `p` | (a) | **elementary**, and the statement is available |
| 4. local liftability at tame ramified `p` | (d) | **(d)-lite**; every Scholz prime is tame (below) |
| 5. gluing local characters into a global one | (d) | **elementary in this setting** (below) |
| 6. linear disjointness of `ℚ(μ_ℓ, p^{1/ℓ})` | (a) | group-theoretic half **done** — `CFT/ScalarSemidirect.lean` |
| 7. a prime with prescribed Frobenius | (c) | **done unconditionally** — `NumberTheory/SplitDensity.lean` |

Three of these deserve comment.

**Input 7 is exactly the theorem (★) of §1.5, and it is proved.**
`InverseGalois.NumberTheory.infinite_setOf_splitsCompletely_not_splitsCompletely` states that for
number fields `A ⊂ B` with `finrank ℚ A < finrank ℚ B` there are infinitely many rational primes
splitting completely in `A` and not in `B`; it is deduced from
`hasDirichletDensity_splitSet`, which gives the split set of a Galois number field Dirichlet
density `1 / n`, with the Euler-product input discharged by
`InverseGalois.NumberTheory.eulerProductHypothesis`. No Chebotarev, no `L`-functions of nontrivial
characters — the analytic content is the pole of the Dedekind zeta function alone. So the input
that §1.4 rated hardest after ABHN costs nothing.

**Input 6's group theory is done.** `CFT/ScalarSemidirect.lean` builds
`ScalarSemidirect ℓ s = (Fin s → ZMod ℓ) ⋊ (ZMod ℓ)ˣ` with the scalar action and proves
`scalarSemidirect_not_exists_quotient_card`: for `ℓ` odd it has no quotient of order `ℓ`, because
conjugation by `-1` inverts the module, so the module lies in the commutator subgroup, and the
complement has order `ℓ - 1`, which `ℓ` does not divide. This is the only place in the whole
argument where `ℓ ≠ 2` is used. What remains of input 6 is the *field-theoretic* half: identifying
`Gal(ℚ(μ_ℓ, p₁^{1/ℓ}, …, p_s^{1/ℓ})/ℚ)` with that semidirect product.

**Kronecker–Weber is not a Scholz–Reichardt blocker.** Milestone 8 below lists it as a gate. It is
not one, for the following reason: in the Scholz condition `(S_N)` every ramified prime `p`
satisfies `p ≡ 1 mod ℓ^N`, hence `p ≠ ℓ`, hence the ramification is **tame** and the inertia group
at `p` is cyclic of order dividing `ℓ^N`, with the local extension contained in the tame abelian
part of `ℚ_p^ab`, which is `ℚ_p(μ_{p^k})`-by-unramified and completely explicit. Input 4 is
therefore a statement about `(ℤ/ℓ^N)²` = (unramified) × (tame), and input 5 — Serre's Lemma
2.1.6, gluing prescribed local abelian characters into one global Dirichlet character — reduces
to choosing a Dirichlet character of the right conductor, because the local conditions live on
cyclotomic fields to begin with. Neither needs the *converse* statement that every abelian
extension of `ℚ` is cyclotomic.

A caution recorded here so it is not rediscovered: **`(S_N)` is not closed under compositum**
without the splitting hypotheses of `CFT/Scholz/SplitCase.lean`. Take `ℓ = 2`, `N = 1`: `ℚ(√3)`
and `ℚ(√−3)` are each ramified only at `3` (and, for the first, `2`), but their compositum
`ℚ(√3, i)` acquires a ramified prime whose inertia is not of split type. The compositum theorem
`IsScholz.of_sup_eq_top` genuinely needs the two-way splitting hypotheses it carries.

**Conclusion.** The single irreducible obstruction is the central embedding step, isolated in the
code as the hypothesis `InverseGalois.CFT.IsCentralStepSolvable ℓ` of
`CFT/Scholz/Induction.lean`, and its arithmetic content is ABHN for cyclic algebras of odd degree
over `ℚ`. Everything the induction needs *around* that step is now either proved or elementary.
`isScholzRealizable_of_isPGroup` is stated with that hypothesis and is otherwise complete: supply
ABHN and every finite `ℓ`-group, `ℓ` odd, is realised over `ℚ`.

---

## 0.5 Status (2026-08-22, evening) — the hypothesis narrowed three times

ABHN did not fall. What did happen is that the *statement* of the remaining hypothesis was cut
down three times, so that the arithmetic still owed is as small as the argument allows, and input 6
was finished on both halves.

**The step is only needed for `ℓ`-groups.** The induction of `CFT/Scholz/Induction.lean` peels a
central subgroup of order `ℓ` off a group of order `ℓ ^ k`, so the source of the surjection it
feeds to the step is always an `ℓ`-group. `IsCentralStepSolvable ℓ` now carries `IsPGroup ℓ G` as a
hypothesis; the old statement quantified over all finite `G`, which is strictly more than
Scholz–Reichardt proves.

**The step is only needed for non-split extensions.** `CFT/Scholz/SplitReduction.lean` proves
`IsCentralStepSolvable.of_nonsplit`: a surjection with central kernel admitting a homomorphic
section presents its source as `H × C_ℓ` (`mulEquivProdOfSection`), and the compositum construction
of the split case already realises such a product — without even spending a level, since
`IsScholzRealizable.mono` lowers the level for free.

**The step is only needed for kernels inside the Frattini subgroup.**
`CFT/Scholz/FrattiniStep.lean` proves `IsCentralStepSolvable.of_frattini`: a kernel of prime order
escaping some maximal subgroup `M` meets `M` trivially and generates the group with it, so `M` is a
complement and the surjection restricts to an isomorphism `M ≅ H` whose inverse is a section. Only
Frattini kernels are left, and those are exactly the extensions with a nonzero obstruction.

So the hypothesis that stands between the repository and Scholz–Reichardt is now

> `IsFrattiniCentralStepSolvable ℓ`: for a finite **`ℓ`-group** `G` surjecting onto `H` with
> **central** kernel of order `ℓ` contained in the **Frattini subgroup** of `G`, a realization of
> `H` satisfying `(S_{N+1})` extends to one of `G` satisfying `(S_N)`.

**The conclusion was raised from `ℓ`-groups to odd nilpotent groups.**
`CFT/Scholz/NilpotentOdd.lean`: a finite nilpotent group is the product of its Sylow subgroups,
which are `q`-groups for the odd primes `q` dividing its order and pairwise coprime, so granted the
step for every odd prime, **every finite nilpotent group of odd order is a Galois group over `ℚ`.**

**Input 6 is complete.** `CFT/Scholz/RadicalDisjoint.lean` proves the field-theoretic half
abstractly — a number field Galois over `ℚ` and generated by a primitive `ℓ`-th root of unity `ζ`
together with elements whose `ℓ`-th powers are rational has no quotient of order `ℓ`, because the
automorphism squaring `ζ` conjugates every automorphism fixing `ζ` into its square and hence forces
the whole `ζ`-fixing subgroup into the commutator subgroup — and `CFT/Scholz/RadicalTower.lean`
builds the field itself, as the splitting field of `∏_{c ∈ {1} ∪ S} (X ^ ℓ − c)` inside
`AlgebraicClosure ℚ`, so `inf_radicalField_eq_bot` is available in the form the induction wants.

**Unconditional by-product.** The same session's group theory gave a new class of *regular*
realizations, which owe nothing to any hypothesis: a finite group with a normal abelian subgroup of
cyclic quotient is semiabelian (`Solvable/SemiabelianCriterion.lean`), hence regular over `ℚ(T)`
(`Rigidity/RET/Wreath/AbelianByCyclic.lean`). The covering argument replaces a section: the cyclic
group generated by a lift of a generator of the quotient, together with the abelian subgroup,
surjects the semidirect product onto the group. Metacyclic groups and generalized quaternion
groups are the visible cases.

---

## 0.6 Status (2026-08-22, night) — the prime 2 handed to geometry, and a wider semiabelian class

Two things happened. The conditional theorem stopped being about odd groups, and the
unconditional class of regular realizations grew.

**The prime `2` is no longer an exception; it is a hypothesis on one Sylow subgroup.**
`CFT/Scholz/NilpotentSylowTwo.lean` splits the nilpotent assembly by prime: the odd Sylow
subgroups go through the Scholz–Reichardt induction, and the Sylow `2`-subgroup is left as an
assumption. `InverseGalois/Shafarevich.lean`, a new top-level module, discharges that assumption
with the *geometric* route — the Dentzer–Stoll wreath product construction, which is
unconditional — and so proves

> granted `IsCentralStepSolvable q` for every odd prime `q`, **a finite nilpotent group whose
> Sylow `2`-subgroup is semiabelian is a Galois group over `ℚ`**,

together with the corollaries for a Sylow `2`-subgroup that is abelian, cyclic, or of order at
most `8` — the last in the form *every finite nilpotent group of order not divisible by `16`*.
The two routes are genuinely independent: one is arithmetic and conditional, the other geometric
and unconditional, and they are joined only by the coprime-product closure of the realization
predicate.

**The semiabelian class was widened.** All of the following are new, sorry- and axiom-free, and
each one is immediately a *regular* realization over `ℚ(T)` through
`isRegularInverseGalois_of_isSemiabelian`; the corollaries are collected in
`Rigidity/RET/Wreath/SmallGroups.lean`.

* `Solvable/SemiabelianZGroup.lean` — **every finite Z-group is semiabelian**: Mathlib's
  `IsZGroup.isCyclic_commutator` and `IsZGroup.isCyclic_abelianization` exhibit a group all of
  whose Sylow subgroups are cyclic as metacyclic, which the metacyclic criterion already covers.
  In particular **every finite group of squarefree order is regular over `ℚ(T)`.**
* `Solvable/SemiabelianHall.lean` — the splitting criteria: a normal abelian subgroup with a
  complement (Schur–Zassenhaus, or a normal abelian Sylow subgroup, or any homomorphic section)
  and a semiabelian quotient gives a semiabelian group.
* `Solvable/SemiabelianSmall.lean` — a group with an abelian subgroup whose index is the smallest
  prime factor of the order is semiabelian, whence the orders `p`, `p ^ 2`, `p ^ 3` and `p * q`.
* `Solvable/SemiabelianCriterion.lean` gained `IsSemiabelian.of_mul_comm`, the abelian case with
  commutativity as a hypothesis rather than an instance.

What this does *not* do is move ABHN. The hypothesis of §0.5 is unchanged and remains the single
arithmetic debt.

---

## 0.7 Status (2026-08-22, late) — class two, every order below 24, and the Frattini induction

The semiabelian class was pushed again — once structurally, by nilpotency class, and once by
*order* — and the conditional nilpotent theorem moved one power of two.

**Every finite group of nilpotency class at most `2` is semiabelian**
(`Solvable/SemiabelianClassTwo.lean`, `IsSemiabelian.of_commutator_le_center`). This is the
structural high point of the batch and it is proved by the Frattini induction below in three lines
of mathematics: if `G' ≤ Z(G)` and `x ∉ Φ(G)`, then `A = ⟨x⟩ · Z(G)` is abelian, and it is normal
because `[A, G] ≤ G' ≤ Z(G) ≤ A`; a maximal subgroup supplementing `A` is proper and again of class
at most `2`, so the induction closes. Every subgroup of a class-`2` group has class at most `2`,
which is exactly what the induction needs and what fails for class `3`. In particular every
extraspecial group, every group of order `p ^ 3`, and every `2`-group of class `2` — of any order —
is regular over `ℚ(T)`, so the hypothesis on the prime `2` in the conditional Shafarevich theorem is
now met by an unbounded family of `2`-groups.

**Every finite group of order less than `24` is semiabelian**
(`Solvable/SemiabelianSmallOrders.lean`, `IsSemiabelian.of_card_lt_twentyfour`), hence regular over
`ℚ(T)`. Two new shape criteria were needed to close the gaps in the enumeration:

* `Solvable/SemiabelianP2Q.lean` — **order `p ^ 2 * q`** (`IsSemiabelian.of_card_eq_sq_mul_prime`).
  Sylow counting produces a normal Sylow subgroup in every case; the one order at which the counts
  admit no immediate normal subgroup, `12` with `n₂ = 3`, is settled separately by showing the
  Sylow `2`-subgroup is unique there.
* `Solvable/SemiabelianP2Q2.lean` — **order `p ^ 2 * q ^ 2`**
  (`IsSemiabelian.of_card_eq_sq_mul_sq`), whence the orders `36` and `100`. The one shape the
  counts leave open is `36` with four Sylow `3`-subgroups; there the kernel of the conjugation
  action on those four subgroups has order `3`, is central, and its quotient of order `12` hands
  back a normal Sylow `2`-subgroup.
* `Solvable/SemiabelianP4.lean` — **order `p ^ 4` for every prime `p`**
  (`IsSemiabelian.of_card_eq_prime_pow_four`). A maximal abelian normal subgroup of a `p`-group is
  self-centralizing, and in a group of order `p ^ 4` self-centralizing forces index at most `p`,
  so the quotient is cyclic and the criterion of §0.6 applies. In particular every group of order
  `16` is semiabelian.

`24` is exactly the right place for the enumeration to stop. **`SL(2,3)`, of order `24`, is the
smallest non-semiabelian group**: its only abelian normal subgroup is its centre `C₂`, which is
also its Frattini subgroup, so no abelian normal subgroup escapes the Frattini subgroup and no
supplement argument can start. The milestone is sharp, not an artefact of the criteria available.

**The supplement argument was isolated as an induction** (`Solvable/SemiabelianFrattini.lean`).
Call a finite group *Frattini-supplemented* when, unless trivial, it has an abelian normal subgroup
not contained in its Frattini subgroup. Such a subgroup is supplemented by a maximal subgroup —
a *proper*, hence smaller, subgroup — so `IsSemiabelian.of_isFrattiniSupplemented` turns the
covering criterion into a genuine induction on the order. This is the general form of every
order-by-order argument above, and it is also precisely what `SL(2,3)` defeats.

**Two criteria for a dominant prime** (`Solvable/SemiabelianLargePrime.lean`). If `|G| = m * q`
with `q` prime and `m < q`, the number of Sylow `q`-subgroups divides `m` and is `≡ 1 mod q`, so it
is `1`: the Sylow subgroup is normal, cyclic of prime order, and `G` is semiabelian as soon as the
quotient of order `m` is (`IsSemiabelian.of_card_eq_mul_prime_of_lt`). The same argument with
`|G| = m * q ^ 2` gives a normal Sylow subgroup of order `q ^ 2`, which is abelian
(`of_card_eq_mul_prime_sq_of_lt`). Combined with the order-`<24` theorem this yields two infinite
families with no bound on `|G|`: `of_card_eq_mul_prime_of_lt_twentyfour` and
`of_card_eq_mul_prime_sq_of_lt_twentyfour`, for `m < 24 < q`.

`Solvable/SemiabelianSylowCount.lean` replaces the size comparison `m < q` by the exact condition
the counting argument needs: no divisor of `m` other than `1` is congruent to `1` modulo `q`. That
is a statement about the finite set `m.divisors`, hence decidable, so at a concrete order it is
discharged by evaluation — the orders `40`, `45`, `75` and `99` are recorded that way.

**The hypothesis on the prime `2` is now met structurally as well as numerically.**
`isInverseGalois_of_isNilpotent_of_classTwo_sylow_two`: granted the odd central step, a finite
nilpotent group whose Sylow `2`-subgroup has nilpotency class at most `2` is a Galois group over
`ℚ`, with no bound at all on the order.

**The conditional headline moved from `16` to `32`.** With order `16` now semiabelian,
`isInverseGalois_of_isNilpotent_of_not_dvd_thirtytwo` says: granted the odd central step, every
finite nilpotent group of order not divisible by `32` is a Galois group over `ℚ`. The Sylow
`2`-subgroup then has order at most `16`, and every group of order `1, 2, 4, 8, 16` is semiabelian.

**The arithmetic hypothesis was narrowed.** `isInverseGalois_of_..._of_frattini` variants assume
only `IsFrattiniCentralStepSolvable q` — the central step for surjections whose kernel lies inside
the Frattini subgroup of the source. A central kernel of prime order escaping the Frattini subgroup
is complemented by a maximal subgroup, so that extension splits and is realised by a compositum
with no arithmetic at all. This is the narrowest form the induction actually calls for, and hence
the smallest statement ABHN would have to supply.

ABHN itself is untouched. `CFT/Global/` is, on inspection, entirely the `ℓ = 2` world —
Davenport–Cassels, Hilbert symbols, the Hasse principle for diagonal quadratic forms — so the
odd-`ℓ` injectivity of `H²(ℚ, C_ℓ) → ∏_p H²(ℚ_p, C_ℓ)` is not close. It remains the single debt.

---

## 0.8 How far the geometric route can go at all — the semiabelian literature

The conditional nilpotent theorem needs the Sylow `2`-subgroup to be semiabelian, so it is worth
knowing where that hypothesis stops being satisfiable. The reference is

> M. Kida, *On semiabelian groups*, J. Group Theory **27** (2024), 697–712,
> DOI [10.1515/jgth-2024-0010](https://doi.org/10.1515/jgth-2024-0010) (open access),

which is the first systematic study of which groups are semiabelian since Dentzer introduced the
class. Its facts, in the order they matter here.

**Not every finite `2`-group is semiabelian.** Wilkens' classification splits the non-modular
quaternion-free `2`-groups into types A, B, C; types A and B are semiabelian (Kida, Prop. 3.10) but
type C is not (Kida, Thm 4.6). So the geometric route can never, by itself, finish the nilpotent
case of Shafarevich: there is a genuine obstruction at the prime `2`, not merely a gap in the
criteria available here.

**Where the obstruction starts.** Kida's Magma computation (Example 5.5) lists every non-semiabelian
*stem* group of order at most `100`:

  `(24,3) = SL(2,3)`, `(48,28) = C2 . S4`, `(64,8) = C2² . SD16`, `(64,41) = D8 ⋊ C4`,
  `(96,3)`, `(96,190)`, `(96,201)`, `(96,203)`.

Since being semiabelian is invariant under isoclinism (Kida, Thm 1.1) and every group is isoclinic
to a stem group, this says: the smallest non-semiabelian group is `SL(2,3)` of order `24`, and the
smallest non-semiabelian **`2`-group** has order `64`. Every group of order `32` is semiabelian.
So `isInverseGalois_of_isNilpotent_of_not_dvd_thirtytwo` could in principle be improved to
"not divisible by `64`" and no further — but that would mean checking all `51` groups of order `32`,
whereas the criteria formalized here are structural.

**The criteria Kida proves.** Nilpotent of class `2` (Thompson; formalized here in §0.7); solvable
with all Sylow subgroups abelian (Thompson); modular `p`-groups and Hamiltonian `2`-groups
(Prop. 3.6); Wilkens types A and B (Prop. 3.10); the isoclinism invariance (Thm 1.1); and, for
non-nilpotent solvable groups, a criterion through Carter subgroups (Prop. 5.4). The class is closed
under quotients, direct products and wreath products, but **not** under subgroups — `(96,204)` is
semiabelian and contains `SL(2,3)`, which is not. That failure of subgroup-closure is exactly what
makes the Frattini induction of §0.7 have to carry its hypothesis along by hand.

**Consequences worth formalizing, in order of value.** Thompson's abelian-Sylow criterion is the
widest of them and subsumes a great deal: a group of cubefree order has all its Sylow subgroups of
order `1`, `p` or `p²`, hence abelian, so *every finite solvable group of cubefree order is
semiabelian*, which contains the whole `p^a q^b` small-order zoo already treated one shape at a
time. Wreath-product closure is the next: iterated wreath products of `C_p` are exactly the Sylow
`p`-subgroups of the symmetric groups, an unbounded family of `p`-groups.

---

## 0.9 Status (2026-08-22, late evening) — Thompson's criterion, wreath closure, order below 32

Both of the "consequences worth formalizing" of §0.8 are now in the repository, sorry- and
axiom-free, together with one more step of the enumeration of small orders.

**Thompson's abelian-Sylow criterion.** `InverseGalois/Solvable/SemiabelianAGroup.lean`:

```lean
IsSemiabelian.of_forall_sylow_comm {G : Type} [Group G] [Finite G] [IsSolvable G] :
  (∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (x y : ↥(P : Subgroup G)), x * y = y * x) →
    IsSemiabelian G

IsSemiabelian.of_isSolvable_of_cubefree {G : Type} [Group G] [Finite G] [IsSolvable G] :
  (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ Nat.card G) → IsSemiabelian G
```

The proof is the Frattini induction of §0.7 with a new supply of abelian normal subgroups escaping
the Frattini subgroup. Write `Q = frattini G`, which is proper and normal. The quotient `G ⧸ Q` is
nontrivial and solvable, so it has a minimal normal subgroup `K` that is elementary abelian of some
exponent `p`; let `N` be its preimage in `G` and `P` a Sylow `p`-subgroup of `N`. Then `P ⊔ Q = N`,
because the index of the join divides both the `p`-free index of `P` in `N` and the `p`-power
`Q.relIndex N`. Frattini's argument (`Sylow.normalizer_sup_eq_top`) gives
`(P : Subgroup G).normalizer ⊔ N = ⊤`, hence `normalizer ⊔ Q = ⊤`, and since the Frattini subgroup
is non-generating this forces `normalizer = ⊤`: `P` is normal in `G`. It is abelian because it is a
`p`-subgroup and therefore sits inside a Sylow `p`-subgroup of `G`, which is abelian by hypothesis;
and it is not contained in `Q`, since otherwise `N = P ⊔ Q = Q`. The hypothesis passes to subgroups
(a Sylow subgroup of a subgroup is contained in a Sylow subgroup of the whole group), which is what
lets the induction on `Nat.card G` run in spite of the failure of subgroup-closure for
semiabelianness itself.

**Wreath closure.** `InverseGalois/Solvable/SemiabelianWreath.lean`:

```lean
IsSemiabelian.regularWreathProduct : IsSemiabelian D → IsSemiabelian Q → IsSemiabelian (D ≀ᵣ Q)
IsSemiabelian.iteratedWreathProduct : IsSemiabelian G → ∀ n, IsSemiabelian (IteratedWreathProduct G n)
IsSemiabelian.sylow_perm {p n : ℕ} [Fact p.Prime] {α : Type} [Finite α] :
  Nat.card α = p ^ n → ∀ P : Sylow p (Equiv.Perm α), IsSemiabelian ↥(P : Subgroup (Equiv.Perm α))
```

The induction is on the derivation of `IsSemiabelian D`, using the functoriality of `D ≀ᵣ Q` in its
bottom argument: an injection `D₁ →* D₂` induces an injection of wreath products and a surjection
induces a surjection, so the `of_surjective` case is immediate, and the semidirect-product case
identifies the kernel of `mapLeft SemidirectProduct.rightHom` as an abelian normal subgroup with a
semiabelian quotient. The Sylow statement is Mathlib's
`Sylow.mulEquivIteratedWreathProduct`, which presents a Sylow `p`-subgroup of `Equiv.Perm α` for
`Nat.card α = p ^ n` as the `n`-fold iterated wreath product of a group of order `p`.

**One more order.** `IsSemiabelian.of_card_lt_thirtytwo` covers every finite group of order less
than `32` other than `24`: the orders `25` to `31` are `5²`, `2 · 13`, `3³`, `2² · 7`, the primes
`29` and `31`, and the squarefree order `30`, each already covered by a shape criterion. `24` is
`SL(2,3)`'s order and is genuinely excluded. `Squarefree 30` needs `decide +kernel` — plain `decide`
gets stuck on the well-founded recursion in `Nat.minSqFac`, and `norm_num` has no extension for it.

**Regular corollaries.** Each of these appears in `RET/Wreath/SmallGroups.lean` as an entry of the
catalogue of regular Galois groups over `ℚ(T)`: `isRegularInverseGalois_of_forall_sylow_comm`,
`isRegularInverseGalois_of_isSolvable_of_cubefree`, `isRegularInverseGalois_sylow_perm`,
`isRegularInverseGalois_iteratedWreathProduct`, `isRegularInverseGalois_of_card_lt_thirtytwo`.

**What blocks the next order.** The conditional nilpotent theorem is still
`isInverseGalois_of_isNilpotent_of_not_dvd_thirtytwo`, because the criteria above say nothing about
a `2`-group of order `32` in which *every* abelian normal subgroup lies inside the Frattini
subgroup. The situation is completely pinned down: for such a `G`, a maximal abelian normal
subgroup `A` is self-centralizing, `|A| = 4` is impossible (`Aut C4` and `Aut (C2 × C2)` have no
subgroup of order `8`), `|A| ≤ 2` forces `C_G(A) = G`, and `|A| ≥ 16` makes `G` abelian or gives an
abelian subgroup of index `2`; so `|A| = 8` and, `G` being non-cyclic, `A = Φ(G)` with
`G / A ≅ C2 × C2` acting faithfully. For `A ≅ C8` this is contradictory: `x² ∈ A` cannot generate
`A` (that would put `x` in `C_G(A)`), so the commutator `[x, y]` is a square in `A`, and then
`⟨a², y⟩` is an abelian normal subgroup of order `8` outside `A`. The cases `A ≅ C4 × C2` and
`A ≅ C2³` (where `G / A` is one of the Klein subgroups of `GL(3,2)`) are the remaining work, and
they are what stands between `not_dvd_thirtytwo` and the sharp `not_dvd_sixtyfour` of §0.8.

Past `32`, the orders `33` to `47` are all covered already — `40 = 2³ · 5` and `45 = 3² · 5` by the
divisor count that makes the largest Sylow subgroup unique, `36 = 2² · 3²` by the `p² q²` file, the
rest by shape — so `InverseGalois/Solvable/SemiabelianFortyEight.lean` records

```lean
IsSemiabelian.of_card_lt_fortyeight {G : Type} [Group G] [Finite G] :
  Nat.card G < 48 → Nat.card G ≠ 24 → Nat.card G ≠ 32 → IsSemiabelian G
```

and settling the order `32` would remove the second exception at once. The bound `48` is sharp:
`(48,28) = C2 . S4` is not semiabelian.

---

## 0.10 Status (2026-08-24) — class field theory, and the second inequality

Of the two blockers named in §0.2, Albert–Brauer–Hasse–Noether is the one that cannot be dodged:
the embedding problem of Scholz–Reichardt is solvable exactly because a Brauer class that is
locally trivial everywhere is trivial, and there is no elementary substitute for that in exponent
`ℓ > 2`. The degree-two slice of ABHN is already in the tree (`docs/Development/ClassFieldTheory.md`
§1.3), by an argument about ternary quadratic forms that generalises to nothing. So the real
class field theory has to be built, and the route being followed is Milne, *Class Field Theory*,
chapter VII: the two inequalities for the idele class group, then reciprocity, then the exact
sequence of Brauer groups. This section records how far that has got; the file-level map is in
`docs/Development/ClassFieldTheory.md` §4.

**Tate cohomology of a cyclic group.** `InverseGalois/CFT/Tate/` is a self-contained development
of `Ĥ⁰` and `Ĥ⁻¹` for an automorphism `σ` of an abelian group of order dividing `n`, together with
the Herbrand quotient

```lean
InverseGalois.CFT.herbrand (σ : A ≃+ A) (n : ℕ) : ℚ :=
  (Nat.card (tateH0 σ n) : ℚ) / (Nat.card (tateHm1 σ n) : ℚ)
```

and everything the quotient is normally used with: the six-term hexagon of a short exact sequence
(`Exact.lean`, `Hexagon.lean`) and hence multiplicativity, invariance under a commensurable
subgroup (`Commensurable.lean`, `Isogeny.lean`), Shapiro's lemma for an induced module
(`Shapiro.lean`, `InducedLattice.lean`, `PermLattice.lean`), Hilbert 90 for a cyclic action
(`CyclicHilbert90.lean`), and transport along an equivariant isomorphism (`Congr.lean`). For a
trivial action the two groups are the cokernel and the kernel of multiplication by `n`
(`Trivial.lean`, `TrivialLattice.lean`), which is what turns every Herbrand computation below into
an index computation.

**The local layer.** `InverseGalois/CFT/Local/` computes the local invariants a place at a time.
The units of a complete discretely valued field have Herbrand quotient the degree of the extension
(`UnitFiltration.lean`, `FiltrationHerbrand.lean`, `UnitHerbrandChain.lean`), by filtering the unit
group and matching each graded piece against the additive filtration through the exponential
(`Exp.lean`, `ExpEquiv.lean`, `ExpSurjective.lean`). The same exponential, run in the other
direction, shows that a unit congruent to one to sufficient accuracy is an `n`-th power
(`PowNeighbourhood.lean`), the accuracy needed being governed by the valuation of the residue
characteristic and the valuation of `n`. Reading the Herbrand quotient of the units through its
definition then gives the local index of the `n`-th powers:

```lean
InverseGalois.CFT.index_range_powMonoidHom_localUnitGroup
    (hsurj : Function.Surjective (Valued.v : A → ℤᵐ⁰)) [∀ k : ℤ, Finite (gradedAdd A k)]
    (h : HasResidueChar A p e) (hnz : n ≠ 0)
    (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) :
  (powMonoidHom n : ↥(localUnitGroup A) →* ↥(localUnitGroup A)).range.index
    = Nat.card (gradedAdd A 0) ^ m * Nat.card ↥(rootsOfUnity n A)
```

with the corresponding statements for the whole multiplicative group at a finite place
(`AdicPowIndex.lean`) and at an infinite one (`InfinitePowIndex.lean`) — this is Milne 6.8. The
local norm index `(K_v^× : Nm L_w^×) = [L_w : K_v]` for a cyclic local extension is
`NormIndex.lean`, on top of the unramified and ramified norm forms.

**The idele layer.** `InverseGalois/CFT/Units/` assembles the local factors into the ideles.
`Idele.lean` defines them as a restricted product, written additively, of the unit groups of the
completions; `AdicSIdeles.lean` and `SUnit.lean` cut out the `S`-ideles and the `S`-units;
`IdeleClass.lean` forms the idele class group with its Galois action and identifies its Tate
cohomology with that of the `S`-idele classes for a large enough `S`. Combining the local Herbrand
quotients through Shapiro's lemma over the orbits of the Galois group on the places
(`AdicIdeleHerbrand.lean`, `SIdeleHerbrand.lean`, `SUnitHerbrand.lean`) gives

```lean
InverseGalois.CFT.herbrand_ideleClassAut_eq_degree :
  herbrand (ideleClassAut (k := k) (K := K) σ) n = n
```

for a cyclic extension of degree `n`, and hence **the first inequality**:

```lean
InverseGalois.CFT.first_inequality : n ≤ Nat.card (tateH0 (ideleClassAut (k := k) (K := K) σ) n)
```

**The second inequality.** This is Milne VII §6, the algebraic proof. *This subsection describes
the state on 2026-08-24 and has since been overtaken: the second inequality is done. The
prime-degree case is `Kummer/SecondInequality.lean`, the root of unity is removed by
`Kummer/CyclotomicDescent.lean`, and `Kummer/CyclicIndex.lean` climbs the tower to give
`index_ideleDiag_sup_ideleNorm_eq_card`, the norm index of an arbitrary cyclic extension of number
fields being its degree. What follows is kept for the map of the pieces.* The strategy is
Kummer-theoretic: adjoin an `ℓ`-th root of unity, choose a set of
places `S` containing the infinite places, the places above `ℓ` and enough places to make the
class group trivial, and count the index of a large group of `n`-th powers inside the `S`-ideles
in two ways. The counting ingredients are now in place.

* The global index of the `n`-th powers in the `S`-units — Milne 6.7's first half — is
  `Units/SUnitIndex.lean`, `index_range_powMonoidHom_sUnits`, `= n ^ (r₁ + r₂ + |S|)` in the usual
  notation; the proof is the Dirichlet unit lattice plus the Herbrand quotient of a trivial action
  on a finitely generated group.
* The product of the local indices over the relevant places — Milne 6.6 — is
  `Kummer/PowIndex.lean`, `prod_index_range_powMonoidHom_units_of_isPrimitiveRoot`, `= n ^ (2 |S|)`
  when the base field contains a primitive `n`-th root of unity and `S` contains every place at
  which `n` is not a unit. Milne's product runs over `S` alone, which is exactly what this counts.
* Its idele formulation is `Units/PowIdele.lean`: the subgroup of the `S`-ideles carrying the
  `n`-th powers has relative index the product of those local indices,

  ```lean
  InverseGalois.CFT.relIndex_powSIdele_of_isPrimitiveRoot (hζ : IsPrimitiveRoot ζ n)
      (F : Finset (HeightOneSpectrum (𝓞 K))) (hF : ∀ v, v ∈ F ↔ v ∈ S)
      (hn : ∀ v, FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ F) :
    (powSIdele S T n).relIndex (sIdele S T) = n ^ (2 * (Fintype.card (InfinitePlace K) + F.card))
  ```

  resting on the general fact (`PiIndex.lean`) that two subgroups of a product which are given
  place by place and agree outside a finite set have relative index the product of the local
  relative indices.
* Milne 6.4, that the group `E` of Kummer generators consists of norms, is the element-level
  Shapiro chain of `Units/SIdeleNorm.lean`; Milne 6.5 is the index identity
  `relIndex_sup_mul_relIndex_inf`.

What is left of §6 is the Kummer-theoretic half rather than the counting half: 6.3 (an `S`-unit
that is an `n`-th power in every completion at a place of `T` is one in the Kummer extension), 6.9
(surjectivity of `U(S) → ∏_{v ∈ T} U_v/U_v^p`, which needs 6.3 and the order count `[M : L] = p^t`),
the remaining inclusion in 6.7, and then 6.1–6.2, which reduce the general case to one containing
the `p`-th roots of unity and need Milne 4.7 (Frobenius elements generate).

**A topology-free route to the end of §6.** Milne's Proposition 4.5 — a finite solvable extension
with `K^× · D` dense in `I_K` for some `D ⊆ Nm(I_L)` is trivial — is stated with the idele
topology, which the repo does not have. It is not needed. The variant

> if `L/K` is finite solvable and `D ≤ I_K` satisfies `D ⊆ Nm_{L/K}(I_L)` and `K^× · D = I_K`
> **exactly**, then `L = K`

has a two-line proof from the first inequality: pick `K ⊊ K' ⊆ L` with `K'/K` cyclic, then
`I_K = K^× · D ⊆ K^× · Nm(I_{K'}) ⊆ I_K`, so `(I_K : K^× Nm I_{K'}) = 1`, contradicting
`(I_K : K^× Nm I_{K'}) ≥ [K' : K] > 1`. Milne 6.10(b) delivers the *equality* `I_K = D · K^×`,
not merely density, so the whole of §6 can be run without ever topologising the ideles.

Both of the bricks that route needs are now laid, for the cyclic extensions that are all it uses.

1. **The idele norm map.** `Units/IdeleNorm.lean` defines `ideleNorm k K hgen hσ : I_K → I_k` for a
   cyclic extension. The assembly over the places is avoided entirely: the sum of the conjugates of
   an idele is fixed by the generator, hence by the whole group, hence — by the fixed-point theorem
   below — is the image of a unique idele of the base field, and that idele is the norm. The
   defining property is `ideleComap_ideleNorm`, that the norm read in the extension is the Tate norm
   of the Galois action.
2. **Milne Lemma 4.1.** `Units/IdeleFixed.lean` proves `mem_range_ideleComap_iff`, that an idele of
   the extension is fixed by the Galois group exactly when it comes from the base field, and
   `Units/IdeleClassIndex.lean` proves the idele-class half in the form the inequalities want:

   ```lean
   InverseGalois.CFT.ideleQuotEquivTateH0 :
     (↥(idele k) ⧸ ((ideleDiag k).range ⊔ (ideleNorm k K hgen hσ).range))
       ≃+ tateH0 (ideleClassAut (k := k) σ) n
   ```

   The map sends an idele of the base field to the class of its image, which is fixed; it is
   surjective because a fixed class is the class of a fixed idele and a fixed idele comes from the
   base field; and it kills exactly the principal ideles and the norms, because a principal idele of
   the extension fixed by the Galois group is the principal idele of a unit of the base field.

So `first_inequality` now reads in its classical form,

```lean
InverseGalois.CFT.first_inequality_index :
  n ≤ ((ideleDiag k).range ⊔ (ideleNorm k K hgen hσ).range).index
```

that is `(I_k : k^× · Nm I_K) ≥ [K : k]`, and the topology-free 4.5′ is its immediate corollary for
a cyclic extension, `Units/NormIndex.lean`:

```lean
InverseGalois.CFT.subsingleton_gal_of_ideleDiag_sup_ideleNorm_eq_top
    (htop : (ideleDiag k).range ⊔ (ideleNorm k K hgen hσ).range = ⊤) : Subsingleton Gal(K/k)
```

Norm transitivity, `Nm_{L/K} = Nm_{K'/K} ∘ Nm_{L/K'}` — what lets the cyclic step be taken inside a
tower — is `Units/IdeleNormTower.lean`:

```lean
InverseGalois.CFT.ideleNorm_trans (x : ↥(idele K)) :
  ideleNorm k F (ideleNorm F K x) = ideleNorm k K x
```

Both the tower compatibility of the inclusions (`ideleComap_trans`, `Units/IdeleTower.lean`, resting
on the place-by-place compatibilities of `Units/PlaceTower.lean`) and the equivariance of the
inclusion under restriction of automorphisms (`ideleAut_ideleComap_restrict`,
`Units/IdeleRestrict.lean`, resting on `Units/PlaceRestrict.lean`) feed into it; the sum over the
Galois group of the whole extension splits because lifting an automorphism of the middle field and
multiplying by one fixing it is a bijection from the product of the two Galois groups.

With that, **4.5′ holds for a solvable extension**, `Units/SolvableNorm.lean`:

```lean
InverseGalois.CFT.subsingleton_gal_of_isSolvable_of_ideleDiag_sup_le [IsSolvable Gal(K/k)]
    (hD : D ≤ (ideleNorm k K).range) (htop : (ideleDiag k).range ⊔ D = ⊤) :
  Subsingleton Gal(K/k)
```

The cyclic subextension is produced group-theoretically: a nontrivial finite solvable group has a
nontrivial complex character (its abelianization is a nontrivial finite commutative group and
characters separate the elements of such a group), and the quotient by the kernel of a character is
a finite subgroup of `ℂ^×`, hence cyclic; the fixed field of the kernel is the `K'` above.

What remains of the §6 count is recorded above; ABHN itself, however, does not wait for it — see
§0.11.

---

## 0.11 Status (2026-08-25) — Albert–Brauer–Hasse–Noether, and the shape it takes for Scholz

ABHN is in the tree. It did **not** need the second inequality, reciprocity, or the Brauer-group
exact sequence of Milne §7: the cohomological form of the theorem is exactly the injectivity of
`H²(G, K^×) → H²(G, I_K)` together with the vanishing of `H²` of the ideles place by place, and
the injectivity is the long exact sequence of

```text
1 → K^× → I_K → C_K → 1
```

fed by `H¹(G, C_K) = 0`, which the first inequality already gives — `Units/IdeleClassH1.lean` for a
cyclic group and `Units/IdeleClassH1Full.lean` in general, via dévissage along a solvable series.
So the statement is

```lean
InverseGalois.CFT.injective_map_H2_globalUnits (k K) :          -- Units/IdeleClassSES.lean
  Function.Injective ((map … (globalUnitsToIdele k K) …).hom)
```

and, combined with the place-by-place statement `exists_coboundary_idele`
(`Units/IdeleCoboundary.lean`, a two-cocycle of the ideles which is a coboundary at every place is
a coboundary — the restricted-product bookkeeping is `Units/IdeleClass.lean`):

```lean
InverseGalois.CFT.exists_sub_add_eq_globalUnits                 -- Units/ABHN.lean
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (ha  : ∀ x y z, globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y)
    (hinf : ∀ w : InfinitePlace K, … the image of `a` in `w.Completionˣ` is a coboundary …)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), … the image of `a` in `(v.adicCompletion K)ˣ` is … ) :
  ∃ b, ∀ x y, a x y = globalUnitsAut x (b y) - b (x * y) + b x
```

**The local hypotheses, and how many of them are real.** For the Scholz–Reichardt step the cocycle
is killed by an odd prime `ℓ`, and then almost all of `hinf`/`hfin` is free.

* *Archimedean places.* `GroupCohomology/CoprimeCoboundary.lean` proves that summing the cocycle
  identity over its third variable exhibits `|G| • f` as the coboundary of `y ↦ ∑ z, f y z`
  (`nsmul_card_eq_of_isCocycle₂`), so a Bézout combination gives

  ```lean
  InverseGalois.CFT.exists_sub_add_eq_of_coprime (φ : G →* AddAut M)
      (hcop : Nat.Coprime (Nat.card G) n) (hf : … cocycle …) (hn : ∀ x y, n • f x y = 0) :
    ∃ c, ∀ x y, f x y = φ x (c y) - c (x * y) + c x
  ```

  Mathlib's `NumberField.InfinitePlace.nat_card_stabilizer_eq_one_or_two` says the decomposition
  group at an archimedean place has order one or two, which is coprime to an odd `n`.
* *Unramified finite places.* A unit killed by a nonzero integer has valuation zero, because the
  valuation lands in the torsion-free group `ℤ` (`mem_ker_unitVal_of_nsmul_eq_zero`). So the local
  component is a two-cocycle of the decomposition group with values in the units of the valuation
  ring, and there `Local/UnramifiedCoboundary.lean` already had the vanishing: the decomposition
  group is cyclic and the norm on the units of the valuation ring is surjective.
* *Ramified finite places.* These are the only ones left, and they are precisely where Serre's
  condition `(S_{N+1})` — `p ≡ 1 mod ℓ^{N+1}`, residue degree one, tame — is spent.

The assembly of those three observations is the new module `Units/ABHNTorsion.lean`, whose main
statement is the form of ABHN that a central embedding problem with kernel of odd prime order meets:

```lean
InverseGalois.CFT.exists_sub_add_eq_globalUnits_of_odd {n : ℕ} (hn : Odd n)
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (hpow : ∀ x y, n • a x y = 0)
    (ha   : ∀ x y z, globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y)
    (hram : ∀ v, ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal → … local coboundary at `v` …) :
  ∃ b, ∀ x y, a x y = globalUnitsAut x (b y) - b (x * y) + b x
```

It rests on the equivariance of the local embeddings for the decomposition group,
`smulUnitsAut_adicUnitHom` and `smulUnitsAut_infiniteUnitHom`, also in that module.

**Getting back down to `μ_ℓ`.** ABHN is a statement about `K^×`, and the obstruction of the
embedding problem lives in `H²(G, ℤ/ℓ)`. The two are matched by the Kummer sequence, which is
`Kummer/InflationRootsOfUnity.lean`: Hilbert 90 turns a coboundary in `K^×` into an element `β`
with `g • β / β = b g ^ n` (`exists_pow_eq_of_isMulCoboundary₂`), and over an extension containing
an `n`-th root of `β` the inflated cocycle is cobounded by a cochain of `n`-th roots of unity
(`exists_cochain_pow_eq_one`). Since `H²(D, μ_ℓ) → H²(D, K_w^×)` is injective for the local
decomposition groups, nothing is lost in the passage.

**Getting back down from `ℚ(μ_ℓ)`.** The Kummer argument wants the `ℓ`-th roots of unity in the
base, and the degree of that adjunction divides `ℓ - 1`, hence is coprime to `ℓ`. The descent is
group-theoretic, `GroupCohomology/CoprimeSplit.lean`:

```lean
InverseGalois.CFT.exists_splitting_of_coprime_index
    (π : E →* G) (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    (hcop : Nat.Coprime U.index (Nat.card π.ker)) (s : U →* E) (hs : ∀ u, π (s u) = u) :
  ∃ σ : G →* E, ∀ g, π (σ g) = g
```

by the transfer: the transfer of the difference between the identity of `E` and the given section
is the `U.index`-th power map on the kernel, which is bijective there, so inverting it turns the
transfer into a retraction and dividing the identity by that retraction kills the kernel.

**What is still missing for `IsFrattiniCentralStepSolvable ℓ`.** The remaining inputs are all on
the ramified side and all local:

1. local liftability at a ramified tame `p` satisfying `(S_{N+1})`, where `Gal(E/ℚ_p) ≅ (ℤ/ℓ^N)²`;
2. the gluing of the local characters into one global condition;
3. the radical closure — given `β ∈ K^×` and `n`, a finite normal extension `M/k` containing an
   `n`-th root of `β`, which is `IntermediateField.normalClosure` applied to `K(α)` with
   `Polynomial.monic_X_pow_sub_C` supplying integrality;
4. the conversion of the resulting `μ_ℓ`-valued cochain into a solution of the embedding problem,
   the improper-to-proper upgrade through the Frattini kernel (`Scholz/FrattiniStep.lean` already
   has `exists_section_of_not_le_frattini`), and the preservation of `(S_N)`.

---

## 0.12 Status (2026-08-25) — item 5 is *not* Kronecker–Weber; it is one local count at `ℓ`

Items 1, 3 and 4 of the list closing §0.11 are done (`Kummer/RadicalClosure.lean`,
`Kummer/CocycleDescent.lean`, `Kummer/CentralEmbedding.lean`, `Local/PrimeResidue.lean`,
`Units/ABHNRamified.lean`, `GroupCohomology/CoprimeDescent.lean`). What the Kummer tower now
delivers is packaged as

```lean
InverseGalois.CFT.HasProperSolution (K : IntermediateField k Ω) (f : G →* H) (π : Gal(↥K/k) →* H) :=
  ∃ M, K ≤ M ∧ NumberField ↥M ∧ IsGalois k ↥M ∧
    ∃ ρ : Gal(↥M/k) →* Gal(↥K/k), Surjective ρ ∧ (ρ is restriction of automorphisms) ∧
      ∃ φ : Gal(↥M/k) →* G, Surjective φ ∧ ∀ g, f (φ g) = π (ρ g)
```

— a *proper* solution of the embedding problem in a field containing the given one, with the
compatibility retained. **It carries no ramification control at all**, and that is now the whole of
what is left.

### The reduction of Serre's Lemma 2.1.6 over ℚ

Serre glues local characters using local *and* global class field theory. Over ℚ, and for a kernel
`C = C_ℓ` of prime order, the gluing needs strictly less. Write `ε_p := φ̃|_{I_p}`, a character
`I_p → C_ℓ` (it lands in `C_ℓ` because `φ = π ∘ φ̃` is unramified at every `p ∉ ram(L)`, and `L`
satisfies `(S_{N+1})` so `ℓ ∉ ram(L)`). Two elementary observations collapse the problem:

* `ε_p` is invariant under conjugation by the decomposition group `D_p`, because `C_ℓ` is central
  in `G` and `ε_p` is the restriction of the homomorphism `φ̃` defined on all of `D_p`.
* The group `Hom(I_p, C_ℓ)^{D_p}` is therefore the only receptacle, and it is *small*:

| `p` | `Hom(I_p, C_ℓ)^{D_p}` | why |
|---|---|---|
| `p ≠ ℓ`, `ℓ ∤ p − 1` | trivial | Frobenius acts on tame inertia by `τ ↦ τ^p`, so `ε(τ)^{p−1} = 1` |
| `p ≠ ℓ`, `ℓ ∣ p − 1` | cyclic of order `ℓ` | tame quotient of `I_p` is `∏_{q≠p} ℤ_q`, so `Hom(I_p, C_ℓ) ≅ C_ℓ` |
| `p = ℓ` | cyclic of order `ℓ` | inflation–restriction: `H¹(D_ℓ, 𝔽_ℓ)` has order `ℓ²`, `H¹(D_ℓ/I_ℓ, 𝔽_ℓ)` order `ℓ`, `H²(Ẑ, 𝔽_ℓ) = 0` |

and in each of the two nontrivial rows the restriction of an explicit **cyclotomic** character is a
generator: the degree-`ℓ` subfield of `ℚ(μ_p)` for `p ≡ 1 mod ℓ` (totally ramified at `p`,
unramified elsewhere), and the degree-`ℓ` subfield of `ℚ(μ_{ℓ²})` for `p = ℓ`. Hence

> **Lemma 2.1.6 over ℚ for `C = C_ℓ` is: `ε := ∏_p χ_p^{a_p}`**, a finite product of cyclotomic
> characters, with the exponents `a_p` read off one prime at a time. **No Kronecker–Weber, no
> reciprocity law, no global idele class group.**

`InverseGalois/CFT/Cyclotomic/OnePrimeRamified.lean` already supplies the characters of the second
row (`exists_cyclic_ramified_exactly_at_one_prime`), and `Cyclotomic/CyclicSubfield.lean` the cyclic
subfields of `ℚ(μ_q)`; the tame row is `TameCharacter.lean` (`tameChar_conj_arithFrobAt`,
`card_inertia_dvd_sub_one`); `Scholz/Tame.lean` already has tame Kronecker–Weber
(`exists_algHom_cyclotomicField_of_isLevel`).

### What genuinely remains

The single irreducible input is the last row of the table, i.e. the **local count at `ℓ`**:

> **(L_ℓ)** `ℚ_ℓ` has exactly `ℓ + 1` cyclic extensions of degree `ℓ`; equivalently
> `|H¹(G_{ℚ_ℓ}, ℤ/ℓ)| = ℓ²`; equivalently every cyclic degree-`ℓ` extension of `ℚ_ℓ` lies in
> `ℚ_ℓ(μ_{ℓ²}) · ℚ_ℓ^{ur}` — **local Kronecker–Weber in exponent `ℓ` at the residue characteristic**.

An elementary route avoiding local class field theory: descend to `E = ℚ_ℓ(μ_ℓ)`, whose degree
`ℓ − 1` over `ℚ_ℓ` is prime to `ℓ`, so `H¹(G_{ℚ_ℓ}, ℤ/ℓ)` is the `ω`-eigenspace of
`E^×/(E^×)^ℓ` for `Δ = Gal(E/ℚ_ℓ)` (Kummer theory plus inflation–restriction). As a `Δ`-module
`E^×/(E^×)^ℓ ≅ 𝔽_ℓ ⊕ μ_ℓ ⊕ 𝔽_ℓ[Δ]` — valuation, roots of unity, and the principal units, the last
by the `ℓ`-adic logarithm on `U¹` — so the `ω`-eigenspace is two-dimensional. The local unit
filtration machinery this needs is already present (`Local/UnitFiltration.lean`, `Local/Exp.lean`,
`Local/ExpEquiv.lean`, `Local/FiltrationHerbrand.lean`).

*Why the wild place cannot be dodged.* `(S_N)` forbids ramification at `ℓ`, and the tame part of
`I_ℓ` has order prime to `ℓ` so maps trivially into the `ℓ`-group `G`; the obstruction is exactly
`φ̃` on **wild** inertia at `ℓ`. The Kummer freedom in the solution (replacing `β` by `βγ`,
`γ ∈ k^×`) only moves the local class at `λ ∣ ℓ` inside the image of `k_λ^×`, which is a proper
subgroup of `(K_λ^×/(K_λ^×)^ℓ)^{D_λ}` in general; and `(S_N)` does *not* require the solution to be
unramified outside `ram(L)` — extra ramification at good primes `q ≡ 1 mod ℓ^N` splitting completely
in `L` is harmless — but no amount of good extra ramification removes a bad one at `ℓ`.


## 0.13 Status (2026-08-25) — the Scholz-side plumbing

Four bricks, all sorry- and axiom-free, all pushed; full build green at 9106 jobs.

**1. The induction contract now carries the order of the quotient.** All three central-step
predicates — `IsCentralStepSolvable`, `IsNonsplitCentralStepSolvable`,
`IsFrattiniCentralStepSolvable` — gained the hypothesis `Nat.card H ∣ ℓ ^ N`.  It is not
cosmetic.  `exists_surjective_hom_of_forall_ramified_primeResidue` demands `ℓ · |D_v| ∣ p − 1` at
every ramified place; `|D_v|` divides `|H|`, and Serre's condition at level `N + 1` supplies only
`ℓ^{N+1} ∣ p − 1`, so without `|H| ∣ ℓ^N` the arithmetic hypothesis of the local–global engine
cannot be met.  The induction is restructured accordingly: with `level(j) = N + (m − j)` along a
central chain of length `m`, step `j → j+1` needs `2j+1 ≤ N+m`, so `m ≤ N+1`;
`isScholzRealizable_of_card_eq_pow_of_le` carries `k ≤ N + 1` and the general
`isScholzRealizable_of_card_eq_pow` realizes at `max N k` and drops back down with
`IsScholzRealizable.mono` (moved into `Scholz/Realization.lean`, since `Scholz/SplitReduction.lean`
imports `Scholz/Induction.lean` and not conversely).  Every externally visible statement, including
all of `InverseGalois/Shafarevich.lean`, is unchanged.

**2. Serre's condition is inherited by subfields** (`Scholz/Condition.lean`):
`isSplitInertia_of_tower`, `IsScholz.of_tower`.  Both halves of `(S_N)` constrain only the ramified
primes; `ramifiedSet_subset` moves the level condition down, and `Ideal.inertiaDeg_algebra_tower`
factors the residue degree through the intermediate field.

**3. Realizations from an abstract field, and from a quotient** (`Scholz/Realization.lean`):
`isScholzRealizable_of_isGalois` embeds any number field satisfying `(S_N)` into
`AlgebraicClosure ℚ` (via `embSubfield`/`embEquiv`) and transports the condition and the group;
`isScholzRealizable_of_surjective` then realizes **every quotient** of the Galois group, by passing
to the fixed field of the kernel.  This is the adapter the central step will finish with: an
embedding-problem solution hands back a big field plus a surjection, not a `ScholzRealization`.

**4. The local groups are cyclic** (`CFT/TameCyclic.lean`, `Scholz/Tame.lean`):
`isCyclic_inertia_of_tame` — the tame character embeds inertia into the units of a finite field, so
tame inertia is cyclic; `isCyclic_stabilizer_of_isSplitInertia` — the residue-degree half of `(S_N)`
identifies the decomposition group with inertia; and the capstone `IsScholz.isCyclic_stabilizer`:
for a field of `ℓ`-power degree satisfying `(S_N)` with `N ≥ 1`, the decomposition group at every
ramified prime is cyclic.  That discharges the first of the three clauses of `hram` in
`exists_surjective_hom_of_forall_ramified_primeResidue`.

**What `hram` still wants**, per place `v` of `K` ramified over the base `k = ℚ(μ_ℓ)`:
(i) `IsCyclic ↥(stabilizer Gal(K/k) v)` — the analogue over `k` of the capstone above;
(ii) the residue field of `K_v` is prime, i.e. every integral element of the completion is
congruent to a rational integer — this follows from residue degree one over `ℚ` but needs the
identification of the residue field of the completion with `𝓞 K / P`;
(iii) `ℓ · |D_v| ∣ p − 1`, which is now available from the level condition plus the new
`Nat.card H ∣ ℓ ^ N` hypothesis.

**Remaining assembly** (Serre's plan): (A) base-change to `k = ℚ(μ_ℓ)` with
`Gal(K₀·k/k) ≅ Gal(K₀/ℚ)` — coprime degrees, so `CFT/Compositum.lean`'s
`galEquivProd (h : A ⊓ B = ⊥)` is the tool; (B) the three clauses above; (C) the character
`χ : ker f → k^×`; (D) `HasProperSolution`; (E) descent to `ℚ` by
`exists_surjective_hom_comp_eq_of_coprime_index`; (F) ramification control by twisting, which needs
the cyclotomic twisting characters of `Cyclotomic/OnePrimeRamified.lean` together with the local
count `(L_ℓ)` of §0.12.

### 0.14 Status (2026-08-25, later) — the local clauses are all discharged at the ℚ level

Step (B) is finished, in the sense that each of the three clauses of `hram` is now a theorem about
the rational prime below the place.

* **(iii) the congruence.** `mul_card_stabilizer_dvd_sub_one` in `Scholz/Condition.lean`: from
  `IsLevel ℓ (N + 1) E` and `Nat.card Gal(E/ℚ) ∣ ℓ ^ N` one gets
  `ℓ * Nat.card ↥(stabilizer Gal(E/ℚ) P) ∣ p - 1` at every ramified `p`.  The decomposition group
  is a subgroup, so its order divides `ℓ ^ N`, and the level condition supplies one more power.
* **(i) cyclic decomposition group.** `IsScholz.isCyclic_stabilizer` in `Scholz/Tame.lean`.
* **(ii) prime residue field and residue characteristic.** The new module
  `Local/PrimeResidueField.lean`.  Residue degree one makes the residue field an extension of the
  prime field of rank one, so `Int.cast : ℤ → 𝓞 K ⧸ P` is surjective
  (`surjective_intCast_quotient_of_inertiaDeg_eq_one`); composing with the approximation lemma
  `exists_algebraMap_sub_le_exp_neg_one` of `Local/AdicResidue.lean` — which already packages the
  density of `K` in `v.adicCompletion K` — gives the predicate the criterion asks for
  (`exists_intCast_sub_lt_one_of_inertiaDeg_eq_one`).  A companion lemma
  `exists_hasResidueChar_of_liesOver` pins the residue characteristic to the *given* rational prime,
  which the existing `exists_hasResidueChar_adicCompletion` of `Local/AdicHerbrand.lean` leaves
  existentially quantified, and `exists_hasResidueChar_and_primeResidue` packages all three in the
  exact `∃ q e, HasResidueChar ∧ prime residue ∧ m ∣ q - 1` shape of
  `exists_surjective_hom_of_forall_ramified_primeResidue`.

**(A) is now the gating item.**  A ℚ-base assembly is impossible in principle: the criterion needs
a primitive `n`-th root of unity in the base, and `n = ℓ`.  So the local clauses have to be
transported from `ℚ` to `k = ℚ(μ_ℓ)`.  The transport should be cheap — clause (ii) is already a
statement about the residue degree of `v` over the rational prime, and clauses (i) and (iii) follow
from `stabilizer Gal(K/k) v ≤ stabilizer Gal(K/ℚ) P`, since a subgroup of a cyclic group is cyclic
and its order divides.  What is not cheap is the base change itself: `Gal(↥(A ⊔ B)/↥B) ≃* Gal(A/ℚ)`
for `A ⊓ B = ⊥` needs an `Algebra ↥B ↥(A ⊔ B)` structure, hence `IntermediateField.extendScalars`
and the attendant `IsScalarTower` pinning.  The group-theoretic content is already available:
`galEquivProd` identifies `Gal(↥(A ⊔ B)/ℚ)` with `Gal(A/ℚ) × Gal(B/ℚ)`, under which the fixing
subgroup of `B` is the first factor.

## 0.15 Status (2026-08-26) — **the central step is unconditional; the odd nilpotent case is done**

The last arithmetic hypothesis of the Scholz–Reichardt induction is gone.  `IsCentralStepSolvable ℓ`
is now a **theorem** for every odd prime `ℓ` (`CFT/Scholz/FrattiniInertiaBound.lean`), so
`InverseGalois/Shafarevich.lean` carries no hypotheses at all.  Full build green at **9165 jobs**,
zero errors, zero warnings, zero sorries and zero axioms outside the comparator.

Unconditionally over `ℚ`:

* `InverseGalois.isInverseGalois_of_isPGroup_odd` — every finite `ℓ`-group, `ℓ` an odd prime;
* `InverseGalois.isInverseGalois_of_isNilpotent_of_odd` — every finite nilpotent group of odd order;
* `InverseGalois.isInverseGalois_of_isNilpotent_of_semiabelian_sylow_two` — every finite nilpotent
  group whose Sylow `2`-subgroups are semiabelian, hence
  `..._of_not_dvd_thirtytwo` / `..._of_not_dvd_sixteen`.

### The chain that closed it

The induction needed, at a prime `P` over `ℓ` of an `ℓ`-extension `A/ℚ`, that a solution of the
central embedding problem be a *power of one fixed character* on the inertia subgroup.  That is the
rank one condition, and it was reduced in three steps.

**Step 1 — rank one from cyclicity** (`Scholz/AbelianInertia.lean`, `Scholz/InertiaRankOne.lean`).
The values of the solution on inertia are central, so the solution factors through the abelianized
decomposition group `D^ab`; there it suffices that the image `I^ab` of inertia be *cyclic*.

**Step 2 — cyclicity from a small Frattini quotient** (`Scholz/FrattiniInertia.lean`).  `I^ab` is
generated by what it contributes to `D^ab/(D^ab)^ℓ` together with `ℓ`-th powers, and `D/I` is cyclic
of order the residue degree.  If the Frattini image of inertia has order at most `ℓ` **and** `D/I`
is large enough — order divisible by the exponent of `Gal(A/ℚ)` — then `D` is generated by one
element together with `I`, and `I^ab` comes out cyclic.  Largeness is not automatic but is bought:
adjoin a cyclic extension of degree `ℓ^n` in which `ℓ` is *inert*, which forces the residue degree
up, and then bring cyclicity back down with `Scholz/AbelianInertiaTransport.lean`, which moves
`I^ab` along any homomorphism carrying decomposition into decomposition and inertia **onto** inertia
(restriction to a normal subextension, and isomorphism of number fields, are both of this shape).
This is the predicate `IsFrattiniInertiaSmallAt ℓ`.

**Step 3 — the Frattini bound itself** (`Scholz/FrattiniInertiaSmall.lean`, the substantial one).
Work in a field `N` containing a primitive `ℓ`-th root of unity `ζ`, at a prime `W ∣ ℓ`.  Let
`ρ : Gal(N/ℚ) → (ZMod ℓ)ˣ` be the mod `ℓ` cyclotomic character, `S` the decomposition group of `W`,
`H = S ⊓ ker ρ` and `F = fixedField H`.  `F` is *not* normal over `ℚ`, which is the reason the file
carries its own glue (`fixedFieldAut`, `mem_inertia_fixedFieldHom`, …).  The master identity of
`Scholz/FixedFieldRamification.lean` — the ramification index times the residue degree of the prime
below a fixed field is the index of the intersection of the decomposition group with the subgroup —
gives `e · f = |ρ(S)| ≤ ℓ − 1` at the place of `F` below `W`.  Since `ζ − 1` divides `ℓ` to depth
`ℓ − 1`, that bound *pins* both invariants: `e = ℓ − 1`, `f = 1`
(`Kummer/RamifiedCyclotomicPlace.lean`).  In particular `ρ(S) = ⊤`, so some `τ ∈ S` sends `ζ` to
`ζ^g` with `g` a primitive root mod `ℓ`; such a `τ` normalises `H` and so descends to an
automorphism `δ` of `F` fixing the place.  That is exactly the abstract local datum
`IsCyclotomicPlace` of `Kummer/CyclotomicPlace.lean`, whose consequence
`inertia_character_dependent` says: two `ZMod ℓ`-valued characters of `Gal(N/F)` invariant under
conjugation by `τ` are *dependent on inertia*.  Conjugation invariance is free for characters pulled
back from an abelian target containing the image of `τ`.  Transporting the dichotomy along a
homomorphism `f : Gal(N/ℚ) → G` carrying `S` into `D` and inertia **onto** an `ℓ`-subgroup `I`
bounds the image of `I` in `D^ab/(D^ab)^ℓ` by `ℓ`; the missing `(ℓ − 1)`-st roots needed to run the
transfer are supplied by `powCoprime`, using `gcd(ℓ, ℓ − 1) = 1` and the fact that `I` is an
`ℓ`-group.

**Removing the root of unity** (`Scholz/FrattiniInertiaBound.lean`).  An `ℓ`-extension of `ℚ` with
`ℓ` odd contains no `ζ_ℓ`, so Step 3 does not apply directly to `A`.  Pass to `M = A ⊔ ℚ(μ_ℓ)`.
`M` is no longer an `ℓ`-extension — and that is fine, because Step 3 only asks that the *image of
inertia* be an `ℓ`-group, which it is, being a subgroup of `Gal(A/ℚ)`.  With
`f = autCongr eA ∘ restrictNormalHom A₀` for a copy `A₀ ≅ A` inside `M`, `map_inertia_eq_inertia`
supplies the surjectivity onto inertia and `restrictNormal_mem_stabilizer` the containment of
decomposition groups.  Hence `IsFrattiniInertiaSmallAt ℓ`, hence `IsAbelianInertiaCyclicAt ℓ`, hence
`IsInertiaRankOneAt ℓ`, hence `IsCentralStepSolvable ℓ`.

### What remains for full Shafarevich

Exactly two things, and only the second is a wall.

1. **The prime `2` in the nilpotent case.**  Handled today by the geometric (Dentzer–Stoll) route,
   which reaches the semiabelian `2`-groups.  By Kida (2024) the smallest non-semiabelian `2`-group
   has order `64`, so geometry alone can never finish it; the fix is to extend Scholz–Reichardt to
   `ℓ = 2`, where the argument above genuinely breaks (`ζ_2 = −1` lies in every field, `ρ` is
   trivial, and `ℓ − 1 = 1` gives no room).  Mapped out in §0.16, whose first brick is landed.
2. **From nilpotent to solvable.**  `Shafarevich.isSolvable_isInverseGalois_of_splitPrimePowerEP`
   already reduces everything to a *split* embedding problem with `p`-group kernel, and the
   nilpotent realizations above are not of that shape: filtering a `p`-group kernel leaves a
   residual non-split lifting.  The genuine Shafarevich argument uses Ikeda plus a Grunwald–Wang
   input, and Grunwald–Wang is not in the repo.

---

## 0.16 Status (2026-08-26, later) — mapping the prime `2`, and the first brick

Landed: **the whole local–global layer now works at every prime**, `2` included.

### Where oddness actually sat

Tracing `Odd ℓ` down from `exists_surjective_hom_of_forall_ramified_primeResidue`
(`CFT/Kummer/CentralEmbedding.lean`) through `ABHNRamified` → `ABHNLocalPower` → `ABHNCoboundary`
→ `ABHNTorsion` shows it is consumed in **exactly one line** of the whole chain, at the archimedean
places:

```lean
have hcop : Nat.Coprime (Nat.card ↥(stabilizer Gal(K/k) w)) n := by
  rcases InfinitePlace.nat_card_stabilizer_eq_one_or_two k w with h | h
  ...
  · rw [h]; exact Nat.coprime_two_left.mpr hn
```

Everything else — the unramified finite places, the ramified ones, the Kummer bookkeeping, the
Frattini argument — never looks at the parity of `ℓ`.

That line is now the predicate `InverseGalois.CFT.IsCoprimeAtInfinitePlaces k K n`, and it has a
second source besides oddness: `IsCoprimeAtInfinitePlaces.of_isUnramifiedAtInfinitePlaces`, which
applies whenever no archimedean place of `K` ramifies over `k` — over `ℚ`, whenever `K` is totally
real.  The chain is restated over the predicate, with the old `_of_odd` statements kept as
corollaries, so:

> **At `ℓ = 2` the Albert–Brauer–Hasse–Noether reduction, and with it the solvability of a central
> Frattini embedding problem with kernel of order `2`, holds verbatim for a totally real base.**

### What the rest of the `ℓ = 2` argument needs

The induction hypothesis has to carry *totally real* alongside the Scholz condition.  That is not a
burden — for odd `ℓ` it is automatic, an odd-degree Galois extension of `ℚ` having no element of
order `2` to act as complex conjugation — and at `ℓ = 2` it is exactly what buys the archimedean
places back.  With `K/ℚ` totally real and unramified at `2`:

* **the local problem at `2` is always solvable unramified.**  `K/ℚ` unramified at `2` makes the
  decomposition group `D₂ ⊆ G` cyclic of `2`-power order `f`.  Its preimage in `G̃` is a central
  extension of a cyclic group by `ℤ/2`, hence abelian, hence either cyclic of order `2f` — solved by
  the unramified extension of that degree — or split, and then the splitting composed with
  `Ẑ ↠ ℤ/f` solves it, again unramified.
* **the local problem at `∞` is trivially solvable**, the decomposition group being trivial.
* **the ramified finite places are unchanged**: `2 · |D_v| ∣ p − 1` is the same Scholz congruence as
  before, with `ℓ = 2`.

So a global solution exists.  The work is in *correcting* it, and there the two things that break
are known precisely.

1. **`RadicalDisjoint` / `NilpotentRadical` are false at `2`.**  `not_surjective_of_radical` rests on
   an automorphism sending `ζ ↦ ζ²`, which for `ℓ = 2` is the identity on `ζ = −1`; and the
   statement itself fails, `2` being a square in the totally real `2`-extension `ℚ(√2)`.  Its one
   use is `Scholz/AuxPrimeChoice.lean:70`, to know that the radicand `m` — a product of primes
   already ramified in `A` — is not an `ℓ`-th power in `A`, so that Chebotarev can find a prime `q`
   splitting completely in `A` with `m` a non-residue.  A ramification argument does *not* rescue
   this: `ℚ(√m)` ramifies exactly where `A` does.  What is true at `2` is sharper and turns it into
   a counting problem: `m` is a square in `A` iff `ℚ(√m) ⊆ A`, so the bad radicands form a subgroup
   of `ℚ^×/(ℚ^×)²` of order `2^{d(G)}`, `d(G)` the minimal number of generators of `G = Gal(A/ℚ)`,
   spanned by the quadratic subfields of `A`.  The correction must choose `m` inside the residue
   span and outside that finite subgroup, which is a dimension count against
   `Scholz/ResidueSpan.lean` rather than a new theorem about radicals.
2. **The correcting characters are short by one dimension at `2` and `∞`.**  Write the defect of a
   solution at a place `v` as a class in `ℚ_v^×/(ℚ_v^×)²`.  The correctors allowed by the Scholz
   condition are `ℚ(√d)` with `d = ± 2^a ∏ pᵢ^{bᵢ} q`, where the `pᵢ` are already ramified and
   `q ≡ 1 mod 2^N` is the new auxiliary prime.  Every odd factor is `≡ 1 mod 8`, hence a square in
   `ℚ₂`, so the class of `d` at `2` is `(−1)^s 2^a` and its sign is `(−1)^s`: the *same* `s`.  The
   pair (class at `2` mod unramified, sign) therefore ranges over an index-two subgroup of
   `(ℤ/2)² × ℤ/2`, and the defect must satisfy the one relation
   `(−1)`-component of the defect at `2` `=` defect at `∞`.

Item 2 is the classical `ℓ = 2` difficulty — the same place where Šafarevič's 1954 argument had its
gap — and is what a formalization has to supply, presumably from Hilbert reciprocity applied to the
defect.  Item 1 is routine.

### Item 2 in the repository's own language: `IsInertiaRankOneAt 2` is false

Item 2 is not a stylistic obstacle; it is a *false hypothesis*, and the repository already names it.
`Scholz/InertiaRankOne.lean` defines

```lean
def IsInertiaRankOneAt (ℓ : ℕ) : Prop := ...   -- at a place over `ℓ`, every homomorphism of order
                                               -- dividing `ℓ` on inertia is a power of one fixed
                                               -- surjective one
```

and `Scholz/FrattiniInertiaBound.lean` proves `isInertiaRankOneAt (hℓ : ℓ.Prime) (hodd : Odd ℓ)`.
The oddness there is *not* removable, because the statement itself fails at `2`.  The abelianized
inertia subgroup of `ℚ₂` is `ℤ₂^×  ≅ ℤ/2 × ℤ₂`, so its quotient by squares is `(ℤ/2)²`: there are
**three** distinct ramified quadratic characters of `ℚ₂`, cut out by `ℚ₂(√−1)`, `ℚ₂(√2)` and
`ℚ₂(√−2)`, and no one of them is a power of another.  Inertia at `2` has rank **two**, not one.
For odd `ℓ` the corresponding group is `ℤ_ℓ^× ≅ ℤ/(ℓ−1) × ℤ_ℓ`, whose quotient by `ℓ`-th powers is
cyclic of order `ℓ`, generated by the cyclotomic character of conductor `ℓ²` — which is exactly the
generator `FrattiniInertiaSmall.lean` produces from a primitive root modulo `ℓ`, and `(ZMod 2)ˣ` is
trivial so there is no primitive root to produce.

This is the same count as item 2, seen locally instead of globally, and it says what the `ℓ = 2`
theorem has to look like.  The correct statement is not rank one at `2`; it is rank one at the pair
of places `{2, ∞}` *jointly*.  The two counts line up exactly:

| | rank of the target | rank of the correctors |
|---|---|---|
| place `2`, mod unramified | `2`  (`{1, −1, 2, −2}`) | |
| place `∞` | `1`  (the sign) | |
| **total** | **3** | **2**  (`−1` and `2`, the sign being tied to the `−1`) |

So the deficiency is exactly one dimension, and the missing input is one relation between the defect
at `2` and the defect at `∞` of a *global* solution.  A purely local lemma cannot supply it; the only
source is reciprocity, and in the standard treatments (Neukirch–Schmidt–Wingberg IX §6) it arrives as
Poitou–Tate duality: the collection of local defects is correctable by a global quadratic character
exactly when it annihilates the dual Selmer group, and the auxiliary prime `q` is chosen to shrink
that dual Selmer group.  What `q` cannot kill are the classes `d` with `ℚ(√d) ⊆ A` — `q` splits
completely in `A`, so such a `d` stays a square at `q` — and those are precisely the classes item 1
also has to avoid.  Items 1 and 2 are therefore two readings of a single dimension count against the
quadratic subfields of `A`.

Poitou–Tate duality is in neither Mathlib nor this repository.  Global reciprocity, on the other
hand, *is* here in the degree-two case that item 2 needs — see §0.17, which turns item 2 into a
theorem.  The same layer is what gap 2 (nilpotent → solvable) needs for Grunwald–Wang, so the two
remaining gaps share their next prerequisite; see §0.10 for how far the idele-class-group side has
got.

---

## 0.17 Status (2026-08-26, later still) — item 2 is a theorem, and it is Hilbert reciprocity

§0.16 item 2 predicted that the correctors allowed by the Scholz condition satisfy **one relation**
between their defect at `2` and their defect at `∞`, and guessed that the relation would have to
come from reciprocity.  Both are now settled, and the reciprocity in question is the ordinary
Hilbert product formula over `ℚ`, which the repository has had since
`InverseGalois/CFT/Global/Reciprocity.lean`.  No Poitou–Tate duality is involved.

The `(−1)`-component of a class in `ℚ₂^×/(ℚ₂^×)²` — the component that the quadratic extension
`ℚ₂(i)` cuts out — is the Hilbert symbol `(−1, ·)₂`, and the defect at `∞` is the sign.  So the
predicted relation is the identity `(−1, d)₂ = sign(d)`, and `Global/NegOneSymbol.lean` proves it
for exactly the integers the Scholz condition produces:

```lean
InverseGalois.CFT.hilbertSymbolAt_neg_one_eq_one_of_one_mod_four {p : Nat.Primes}
    (hp : (p : ℕ) % 4 = 1) {d : ℚ} (hd : d ≠ 0) :
  hilbertSymbolAt p (-1) d = 1

InverseGalois.CFT.hilbertSymbolAt_two_neg_one_intCast {d : ℤ} (hd : d ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ d → p % 4 = 1) :
  hilbertSymbolAt primeTwo (-1) ((d : ℚ)) = if d < 0 then -1 else 1
```

The first is the local input: at a prime congruent to one modulo four, `−1` is a square, so its
symbol against anything is trivial.  The second reads the product formula backwards — the product
of the local symbols of `(−1, d)` over all places is one, every odd place contributes `1`, so the
dyadic symbol is the reciprocal of the real one, which is the sign.  The corollary is item 2 as a
formal statement:

```lean
InverseGalois.CFT.hilbertSymbolAt_two_neg_one_ne_neg_one_of_pos {d : ℤ} (hd : 0 < d)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ d → p % 4 = 1) :
  hilbertSymbolAt primeTwo (-1) ((d : ℚ)) ≠ -1
```

A Scholz-admissible corrector at level `N ≥ 2` is `d = ± 2^a ∏ pᵢ^{bᵢ} q` with every odd factor
congruent to `1` modulo `2^N`, hence to `1` modulo `4`; the hypothesis of the corollary is exactly
that.  So the pair (dyadic defect, real defect) attainable by a corrector is confined to the
index-two subgroup `{(0,+), (α,−), (β,+), (αβ,−)}` of the rank-three target, `α` the class of `−1`
and `β` the class of `2`, precisely as the table in §0.16 predicted.  The prediction is no longer a
count on paper; it is a theorem, and it is sharp.

### The escape, and what it costs

The same product formula says where the missing generator lives.  For an odd prime `q`,

```lean
InverseGalois.CFT.hilbertSymbolAt_two_neg_one_prime_of_three_mod_four {q : ℕ} (hq : q.Prime)
    (hq4 : q % 4 = 3) :
  hilbertSymbolAt primeTwo (-1) ((q : ℚ)) = -1
```

and `q > 0`, so `q` realizes the pair `(α, +)` that no admissible corrector can.  The deficiency is
therefore **caused by the level condition itself**: it is the congruence `q ≡ 1 mod 2^N` on the
auxiliary prime, not anything about the prime `2`, that removes the missing dimension.  Admitting a
single auxiliary prime `q ≡ 3 mod 4` restores it.

That is not free, and the price is worth stating plainly.

* `ℚ(√q)` with `q ≡ 3 mod 4` has discriminant `4q`, so it **ramifies at `2`**.  This is not an
  accident of the choice: `(−1, d)₂ = −1` forces `ℚ₂(√d)/ℚ₂` to be ramified, so *any* corrector that
  moves the dyadic defect ramifies at `2`.  The induction invariant of §0.16 — `K/ℚ` totally real
  and unramified at `2`, which is what buys back the archimedean places in
  `IsCoprimeAtInfinitePlaces` and makes the local problem at `2` solvable unramified — cannot be
  literally preserved across such a correction.  It has to be replaced by a bounded-dyadic-conductor
  invariant.
* `q ≡ 3 mod 4` violates the level congruence at `q` itself, so the next stage of the induction sees
  a ramified prime that is not `≡ 1 mod 2^N`.  The Scholz congruence at a ramified place is what
  makes the *local* embedding problem there solvable, so relaxing it at `q` has to be paid for at
  the following step.

Both costs are about the design of the induction invariant at `ℓ = 2`, not about a missing theorem.
That is a real change of shape in the argument, and it is where the `ℓ = 2` work now sits; but the
arithmetic input that §0.16 identified as the wall — one relation, from reciprocity, tying the
dyadic defect to the real one — is supplied and proved.

---

## 0.18 Status (2026-08-26, night) — Albert–Brauer–Hasse–Noether with **no** condition at infinity

§0.16 located the whole of `Odd ℓ` in one line, at the archimedean places, and gave it a name:
`IsCoprimeAtInfinitePlaces k K n`.  At `n = 2` that predicate says every archimedean place of `K` is
unramified over `k`, i.e. over `ℚ` that `K` is totally real.  §0.17 then showed that the totally
real-and-unramified-at-`2` invariant **cannot** be carried through the correction step: any
corrector that moves the dyadic defect ramifies at `2`, and the corrector that supplies the missing
dimension is `ℚ(√q)` with `q ≡ 3 mod 4`, which ramifies at `2` and breaks the level congruence.

The way out is not to preserve the invariant but to make the theorem not need it.  That is now
done.

### The theorem

```lean
InverseGalois.CFT.exists_isMulCoboundary_of_sq_eq_neg_one
    {K : Type} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K]
    {ι : K} (hι : ι ^ 2 = -1) {n : ℕ} (hn : n ≠ 0)
    {a : Gal(K/ℚ) → Gal(K/ℚ) → ℚˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha  : ∀ x y z, a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal →
              «a is a coboundary in (v.adicCompletion K)ˣ over the decomposition group at v») :
  ∃ b : Gal(K/ℚ) → Kˣ, ∀ g h, g • b h / b (g * h) * b g = Units.map (algebraMap ℚ K) (a g h)
```

No hypothesis at the archimedean places, and **no parity condition on `n`**.  The single price is
`ι ∈ K` with `ι² = −1`.

### How it is proved

Let `Γ = Gal(K/ℚ)` and `N = stabilizer Γ ι`.  Because `σ ι ∈ {ι, −ι}` for every `σ`, `N` is normal
of index two (index exactly two, `ι ∉ ℚ`), and its fixed field `F` contains `ι`, hence is **totally
complex**, hence `IsUnramifiedAtInfinitePlaces F K` holds vacuously — there is no real place of `F`
left to ramify.

1. **Restriction.**  Base change along `AlgEquiv.restrictScalars` from `ℚ` to `F` is definitionally
   free: the action on `HeightOneSpectrum (𝓞 K)`, `adicCompletionAut`, `globalUnitsAut` and
   `smulUnitsAut` all transport by `rfl` (`Units/BaseChangeCocycle.lean`).  So the existing
   Albert–Brauer–Hasse–Noether theorem, applied over `F`, trivialises `a|_{N×N}`.
2. **Inflation.**  A two-cocycle whose restriction to an index-two subgroup is a coboundary equals,
   after twisting by the coboundary of a one-cochain, the *inflation* of a single invariant element
   `c ∈ Kˣ` (`GroupCohomology/IndexTwo.lean`, `exists_twist_eq_indexTwoInflation`; the
   `H¹(N, Kˣ) = 1` input is Hilbert 90 for the subgroup, `SubgroupHilbert90.lean`).  Twisting does
   not disturb the local hypotheses (`Units/LocalCoboundaryTwist.lean`), so the local data descends
   to the inflated cocycle.
3. **Locally a sum of two squares.**  The inflation of `c` is a coboundary over the decomposition
   group at `v` exactly when `c` is a norm from `K_v` for the quadratic subextension cut out by
   `ι`, i.e. when `c` is a **sum of two squares** in the completion of `ℚ` under `v`
   (`Units/LocalSqrtNegOne.lean`).  Being `Γ`-invariant, `c` is a rational number.
4. **Globally a sum of two squares.**  A rational number which is a sum of two squares in every
   `ℚ_p` is a sum of two squares (`Units/RatSumSquares.lean`), by the Hasse norm theorem for
   `ℚ(i)/ℚ` — and the real place costs nothing, a sum of two squares in a single completion being
   already positive.  So `c = x² + y² = N(x + y ι)`, and the inflation of `c` is a coboundary
   globally (`SqrtNegOne.lean`, `isMulCoboundary₂_indexTwoInflation`).
5. Undo the twist.

### Modules

| file | content |
|---|---|
| `CFT/SqrtNegOne.lean` | the stabiliser of a square root of `−1` is normal of index two; its fixed field is totally complex; `σ f · f = x² + y²` |
| `CFT/SubgroupHilbert90.lean` | Hilbert 90 for a subgroup acting on `Kˣ` |
| `CFT/GroupCohomology/Inflation.lean` | inflation of a two-cocycle along a quotient |
| `CFT/GroupCohomology/IndexTwo.lean` | twist, `indexTwoInflation`, and the reduction of an index-two-split cocycle to it |
| `CFT/Units/BaseChangeCocycle.lean` | `restrictScalars` transports every ingredient by `rfl` |
| `CFT/Units/ABHNArchimedean.lean` | the archimedean clause is vacuous over a totally complex base |
| `CFT/Units/LocalSqrtNegOne.lean` | the local coboundary condition ⇔ locally a sum of two squares |
| `CFT/Units/LocalCoboundaryTwist.lean` | twisting preserves local triviality |
| `CFT/Units/RatSumSquares.lean` | everywhere-locally a sum of two squares ⇒ a sum of two squares |
| `CFT/Units/ABHNSqrtNegOne.lean` | the assembly |
| `CFT/Units/ABHNSqrtNegOneRamified.lean` | the same with the ramified places in the form the construction verifies |
| `CFT/Kummer/CentralEmbeddingSqrtNegOne.lean` | the four embedding-problem criteria over such a base, plus a mixed one |

All sorry-free and axiom-free; full build green.

### What this buys, and what it does not

**Buys.**  The induction invariant at `ℓ = 2` no longer has to be *totally real*.  It can be
`ι ∈ K` — an invariant which is preserved by *every* enlargement of `K`, in particular by every
corrector, including `ℚ(√q)` with `q ≡ 3 mod 4`.  The obstruction §0.17 identified as a change of
shape in the argument is removed at the source: the archimedean places are simply no longer part of
the criterion.  Concretely,

```lean
InverseGalois.CFT.exists_surjective_hom_rat_of_forall_ramified_primeResidue
```

is the exact analogue of `exists_surjective_hom_of_forall_ramified_primeResidue` with `Odd n`
deleted and `ι² = −1` in its place.

**Does not buy.**  Requiring `ι ∈ K` makes the place above `2` **ramified**, and at a ramified place
the criterion asks for something.  The residue-characteristic congruence `n · |D_v| ∣ p − 1` is
unsatisfiable at `p = 2`, so the place above `2` has to be discharged the other way — by a
homomorphic lift of `π|_{D_v}` into `G`.  Hence the mixed criterion

```lean
InverseGalois.CFT.exists_surjective_hom_rat_of_forall_ramified_lift_or_primeResidue
```

which asks, at each ramified place, for *either* a lift *or* the congruence.  The Scholz primes
supply the congruence; the place above `2` must supply a lift.

### What the `ℓ = 2` argument now needs

Exactly one arithmetic statement, and it is purely local:

> Let `K/ℚ` be a `2`-extension containing `i`, `v` the place above `2`, `D = D_v ⊆ Gal(K/ℚ)` its
> decomposition group, and `1 → ℤ/2 → G̃ → D → 1` the pullback of the central extension along the
> inclusion.  Then the surjection `G_{ℚ₂} ↠ D` lifts to `G̃`.

Equivalently: the local obstruction in `H²(G_{ℚ₂}, ℤ/2) ≅ Br(ℚ₂)[2] ≅ ℤ/2` vanishes.  It is **not**
automatic — that group is not zero — so this is a genuine condition on the tower, and the right
formulation is a condition on the dyadic behaviour of `K` that the induction can carry (for instance
that `K_v/ℚ₂` be *cyclic*, which makes `G̃_v` abelian and the lift a matter of choosing an
unramified or split extension, as in the second bullet of §0.16).

§0.19 works that condition out, finds that it **fails** in the base case, and concludes that
`ι ∈ K` is not the `ℓ = 2` route after all.  The theorem stands; the route does not.

---

## 0.19 Status (2026-08-26, night, later) — the place `2` is silent when it is unramified, and that is the whole trade

§0.18 built a real theorem and then drew the wrong strategic conclusion from it.  This section
corrects the conclusion, computes the condition §0.18 left open (it is **false** in the smallest
case), and states the one trade that the `ℓ = 2` induction actually faces.

### Three corrections to §0.18

1. **`ℚ(√q)` with `q ≡ 3 mod 4` is real.**  `q > 0`, so that corrector is a real quadratic field and
   does not break total reality.  The two costs §0.17 records are the correct ones: it ramifies at
   `2`, and it violates the level congruence at `q`.
2. **The criterion asks nothing at an unramified place.**  In this repository the local hypothesis
   of Albert–Brauer–Hasse–Noether ranges over the *ramified* finite places only, because
   `exists_sub_add_eq_adicUnits_of_nsmul_eq_zero` (`Units/ABHNTorsion.lean`) discharges every
   unramified finite place for a torsion cocycle, and `exists_sub_add_eq_infiniteUnits_of_coprime`
   discharges the archimedean ones.  So under §0.16's invariant — `K/ℚ` totally real and unramified
   at `2` — the prime `2` costs **nothing at all**.  That is the mechanism behind §0.16's first
   bullet, and it is already a theorem here.
3. **`ι ∈ K` therefore does not remove an obstruction; it creates one.**  Requiring `ι ∈ K` makes
   the place above `2` ramified, and that is the only reason the criterion asks anything there.

### The condition at `2` under `ι ∈ K`, computed

Base case `K = ℚ(i)`, `v | 2`, `D_v = Gal(ℚ₂(i)/ℚ₂)` cyclic of order two, `n = 2`, values in
`{±1}`.  For a cyclic decomposition group the second cohomology of the local units is the invariants
modulo the norms, so the local condition is that `−1` be a norm from `ℚ₂(i)^×`, i.e. a sum of two
squares in `ℚ₂`, i.e. that the Hilbert symbol `(−1, −1)₂` be trivial.  It is not, and the
repository already proves it: `hilbertSymbolAt_two_neg_one_intCast` at `d = −1` (no odd prime
divides `−1`, so the hypothesis is vacuous) gives `hilbertSymbolAt primeTwo (-1) (-1) = -1`.

So at `v | 2` neither the power form, nor the sharper norm form of `Units/ABHNLocalNorm.lean`, nor a
homomorphic lift `D_v →* G` can discharge a cocycle whose value `−1` occurs.  The condition §0.18
posted as "the whole remaining `ℓ = 2` arithmetic" is not merely unproven — it is **false** for the
smallest instance, and it has to be, because the embedding problem `ℤ/4 ↠ ℤ/2 = Gal(ℚ(i)/ℚ)` is
genuinely unsolvable: `ℚ(√d)` lies in a cyclic quartic field exactly when `d` is a sum of two
squares, and `−1` is not.  Its obstruction is the class `(−1, −1)`, ramified at exactly `{2, ∞}`.
Dropping the archimedean condition without adding one at `2` would prove that false statement.

### Why the place `2` cannot simply be omitted

The sum of the local invariants of a class of `Br(K/ℚ)` is zero, so a place may be omitted from the
hypotheses exactly when at most one invariant is left unknown.

| invariant at | `K` totally real | `ι ∈ K` |
|---|---|---|
| `∞` | `0`, the decomposition group being trivial | unknown |
| unramified finite | `0` | `0` |
| Scholz primes | `0`, by the congruence | `0`, by the congruence |
| `2` | ? | ? |

Totally real leaves one unknown and reciprocity determines it.  `ι ∈ K` leaves two unknowns and one
relation, and nothing follows.  This is §0.16's rank count again, read off the Brauer group instead
of off the square classes.

### The trade, stated once

At `ℓ = 2` the induction has exactly two shapes, differing in one bit: whether `2` may ramify.

**(a) `2` unramified** — the §0.16 invariant.  The local–global step needs nothing at `2`.  The
price is the corrector count: the defect has rank three (the dyadic class modulo the unramified one,
rank two; the sign, rank one) and the admissible correctors reach only an index-two subgroup of it
(§0.17, and its local avatar is that `IsInertiaRankOneAt 2` is false).  Deficiency one.  Closing it
needs either a corrector ramified at `2` — which contradicts the invariant — or a relation on the
*defect* matching the one §0.17 proves for the *correctors*.  This is the classical difficulty; its
shape is the special case of Grunwald–Wang at `2`, and it is where Šafarevič's 1954 argument went
wrong.

**(b) `2` allowed to ramify** — invariant: `K/ℚ` Galois, totally real, ramified only at `2` and at
Scholz primes.  Now nothing needs correcting at `2`: `IsInertiaRankOneAt 2` is never invoked, the
rank-three target collapses to the sign alone, and `ℚ(i)`, `ℚ(√2)`, `ℚ(√−2)` become admissible
correctors, so the sign is freely correctable.  Correction at the *odd* ramified primes is the tame
case and is unchanged.  The price is a single missing theorem, and it is a clean one.

> **(T5)**  Let `K/ℚ` be a totally real Galois number field and `a` a two-cocycle of `Gal(K/ℚ)` with
> values in `ℚˣ`, killed by `n`.  If `a` is a coboundary over the decomposition group at every
> ramified finite place **except those above one fixed prime**, then `a` is a coboundary.

Its proof is the reciprocity law for the Brauer group — the sum of the local invariants of a class
split by `K` is zero — together with injectivity of the local invariant on `Br(K_v/ℚ_v)`.  The
repository has the degree-two case over `ℚ`, the Hilbert product formula in
`Global/Reciprocity.lean`, but not the invariant map; that is the next step of the class-field-theory
tower already under construction (§0.10, the second inequality).

**(b) is the better trade.**  (a) asks for exactly the input the classical argument got wrong.  (b)
asks for a standard piece of class field theory which is on the critical path for gap 2 anyway —
Grunwald–Wang, for the nilpotent-to-solvable reduction, needs the same layer.  The recommendation is
to stop trying to move the archimedean place and to build the invariant map.

### What this changes in the repository

Nothing is retracted.  The theorem of §0.18 is true, sorry-free and axiom-free, and it is the right
statement of Albert–Brauer–Hasse–Noether over a base containing `i`; it is simply not the `ℓ = 2`
route.  The sharpening in `Units/ABHNLocalNorm.lean` — at a ramified place with cyclic decomposition
group the local condition is that the values be **norms**, not powers, since the second cohomology
of a cyclic group is its invariants modulo its norms — is the form (T5) will be phrased against, and
it is what makes the computation above a one-line consequence of the Hilbert symbol.

---

## 0.20 Status (2026-08-26, late) — the second inequality is *done*; the wall is reciprocity alone

### What is already in the repository, and was not recorded above

A survey of the class-field-theory layer turns up two theorems that §0.10 and §0.19 still describe
as future work.  They are complete, sorry-free, and in the default build.

* **The second inequality, in every degree.**  `Kummer/CyclotomicDescent.lean` proves
  `index_ideleDiag_sup_ideleNorm_eq_of_prime_degree` — for an extension of prime degree `p`,
  `[J_k : k^× N(J_L)] = p` — by adjoining a `p`-th root of unity to the ambient algebraically closed
  field and descending.  `Kummer/CyclicIndex.lean` then climbs the cyclic tower and lands
  `index_ideleDiag_sup_ideleNorm_eq_card` and `index_ideleDiag_sup_ideleNorm_eq_finrank`: for any
  **cyclic** extension of number fields the idele-class norm index is the degree.
* **The Hasse norm theorem for cyclic extensions.**  `Units/HasseNorm.lean` combines that with the
  first inequality and Hilbert 90 for the idele classes to prove
  `card_tateHm1_ideleClassAut_eq_one` (`Ĥ⁻¹(G, C_K) = 0`) and
  `mem_normSubgroup_of_mem_range_ideleNorm`: an element of `k` which is everywhere locally a norm
  from a cyclic `L/k` is a global norm.

Together with the local computations of `Local/NormIndex.lean` (`card_tateH0_adicUnitsField`,
`subsingleton_tateHm1_adicUnitsField`) this means the **class field axiom is verified in the
repository, locally and globally**: for a cyclic extension, `Ĥ⁰` has order the degree and `Ĥ⁻¹`
vanishes, on the multiplicative group locally and on the idele class group globally.  In Neukirch's
abstract formulation that is the entire input to class field theory *except* the invariant map.

### The single remaining wall

Everything left in the Shafarevich programme funnels through **global Artin reciprocity**, i.e. the
invariant map `inv_v : Br(k_v) → ℚ/ℤ` together with `Σ_v inv_v = 0`:

* gap 1 (`ℓ = 2` Scholz–Reichardt) needs (T5), which *is* `Σ inv_v = 0` plus injectivity of one
  local `inv_v`;
* gap 2 (`ElementaryAbelianKernelEP`) needs Grunwald–Wang, which needs the same layer.

The second inequality is no longer the frontier; it is behind us.

### Four shortcuts to (T5), and why each fails

These were examined and ruled out.  Recording them so they are not re-attempted.

1. **Counting.**  Both available counts fix only the *order* of the relevant subgroup, never which
   subgroup it is.  `|Br(K/k)| = n` against `|⊕_v Br(K_w/k_v)| = ∏ n_v` says the kernel of `Σ inv`
   has order `∏ n_v / n`; `[J : k^× N(J_K)] = n` against `[D_{v₀} : N] = n_{v₀}` says the same thing
   in idele language.  Reciprocity is precisely the identification of the subgroup, so no count can
   replace it.
2. **Correcting by the quaternion class `(−1,−1)_ℚ`.**  That class is ramified exactly at `{2, ∞}`,
   so multiplying by it exchanges an unknown at `2` for an unknown at `∞`: it proves
   `(T5)@2 ⟺ (T5)@∞`, and nothing more.
3. **Quaternion symbols.**  `Σ inv_v = 0` *is* available for symbol classes — that is the Hilbert
   product formula, already proven in `Global/Reciprocity.lean` — and it is additive, so a *product*
   of symbols would suffice.  But this needs `Br(ℚ)[2]` to be generated by quaternion classes, i.e.
   index = exponent over `ℚ` (class field theory) or Merkurjev's theorem (harder), plus
   `Br(ℚ_p)[2] ≅ ℤ/2` (local class field theory).  Circular.
4. **Brauer induction.**  At `p = 2` every subgroup of a `2`-group is "elementary", so induction from
   elementary subgroups says nothing.

Also worth recording: one cannot simply assume local solvability at `2`.  The embedding problem
`ℤ/4 ↠ ℤ/2 = Gal(ℚ₂(i)/ℚ₂)` is genuinely obstructed —
`hilbertSymbolAt primeTwo (-1) (-1) = -1` in the repository — so the local condition at a dyadic
ramified place is a real condition, not a formality.

### Route (c): drop total reality instead, and omit the archimedean place

§0.19 offered two shapes for the `ℓ = 2` induction.  There is a third, and on the corrector side it
is strictly better than both.

> **(c)** Keep the §0.16 invariant that `2` is **unramified**, but **drop** the requirement that `K`
> be totally real, and use (T5) with the **archimedean** place omitted.

Under (a) the corrector deficiency is one because a corrector `d = ± 2^a ∏ pᵢ^{bᵢ} q` has its sign
tied to its `−1`-component: the target has rank three (dyadic class modulo unramified, rank two;
sign, rank one) and the correctors reach only rank two.  Under (c) the sign is no longer part of the
target — the archimedean condition is the one being omitted — so only the rank-two dyadic class must
be corrected, and `{−1, 2, −2}` spans exactly that.  **Deficiency zero.**  The price is (T5) with the
archimedean place omitted rather than a finite one; by shortcut 2 above that is the same theorem.

So all three routes cost exactly one theorem, (T5), and (c) costs nothing else.  The recommendation
of §0.19 is unchanged and reinforced: **build the invariant map**.

### The shape of the remaining work

Global reciprocity over `ℚ` decomposes as:

1. **Local**: `Br(K) ≅ ℚ/ℤ` for a local field, with `Br(K^ur/K)` the whole of it.  The unramified
   half is already done — `Local/UnramifiedInvariant.lean` builds `unramifiedInvariant` and proves
   it bijective.  What is missing is that *every* class is split by an unramified extension.  The
   classical algebraic proof of that goes through the valuation on a central division algebra: the
   residue algebra is a division algebra over a finite field, hence commutative by Wedderburn's
   little theorem (`littleWedderburn`, in Mathlib), and lifting a generator of the residue extension
   produces an unramified maximal subfield.
2. **Cyclotomic approximation**: every class of `Br(ℚ)` is split by a cyclic cyclotomic extension
   with prescribed local degrees.
3. **Reciprocity for cyclotomic extensions**, which is the elementary computation
   `Frob_{(a)} : ζ ↦ ζ^a`.
4. **Assembly of (T5)**, then the `ℓ = 2` Scholz induction under route (c), then Grunwald–Wang for
   gap 2.

Step 1 is the deep one and is the natural next target.

### Bricks landed alongside this survey

* `GroupCohomology/InflationRestriction.lean` — the exactness of `0 → H²(G/N, Mᴺ) → H²(G, M) →
  H²(N, M)` at the middle term, for an **arbitrary** normal subgroup with vanishing `H¹(N, M)`,
  written on cochains.  The index-two case was already in `GroupCohomology/IndexTwo.lean`; the
  general case replaces the two named cosets by a choice of representatives
  (`exists_cosetSection`) and runs the same three corrections.  The packaged consequence,
  `isMulCoboundary₂_of_forall_subgroup_of_forall_inflated`, is the dévissage step: `H²(G, M) = 0`
  follows from `H¹(N, M) = 0`, `H²(N, M) = 0` and the vanishing of `H²` on inflated cocycles.  This
  is what a general-degree second inequality, and Tate's theorem after it, will be built on.
* **The counting half of the *local* first inequality**, i.e. `|Br(L/K)| ≤ [L:K]` for every solvable
  extension of local fields, in five modules:
  * `Brauer/RelativeIndex.lean` — the relative Brauer group of a cyclic extension is `Kˣ/N Lˣ`.
  * `Brauer/SolvableBound.lean` — the dévissage.  It is now stated for a predicate on the *pair*
    `(F, E)` rather than on the top field alone, because the hypothesis actually carried through the
    induction (every automorphism is an isometry) is a property of the pair.  `IsDevissageClosed P`
    accordingly asks for *both* halves of the tower cut out by a subgroup: `P (fixedField C) E` and
    `P F (fixedField C)`.
  * `Brauer/SolvableNormBound.lean` — the same dévissage restated with the cyclic input as a bound
    on the index of the norm subgroup, so that no algebra appears in the hypothesis.
  * `Local/SubfieldValued.lean` — the descent brick.  A subfield of a valued field carries the
    *restricted* valuation `(Valued.v).comap (algebraMap S A)` together with the induced uniformity;
    `IsValuedExtension S A` bundles the two compatibilities, and everything the local computation
    needs (completeness of a closed subfield, the residue characteristic, finiteness of the graded
    pieces) descends along it *unchanged*, because the valuation is restricted and not renormalised.
  * `Local/FixedFieldValued.lean` — the fixed subfield of a group of isometries is closed, hence
    complete; its value group is still nontrivial because `∏_{σ ∈ C} σ π` is fixed and has value
    `(v π)^{|C|}`; and the isometry hypothesis transports both ways, down via
    `AlgEquiv.liftNormal_commutes` and up via `AlgEquiv.restrictScalars`.
  * `Local/CompleteNormIndex.lean`, `Brauer/LocalBrauerBound.lean` — the assembly.
    `IsLocalExtension K A` says `A` carries a complete valuation with a residue characteristic,
    finite graded pieces and a nontrivial value group, preserved by every `K`-automorphism;
    `card_relative_le_finrank_of_isLocalExtension` is the conclusion.
* The local Herbrand chain (`Local/AdicHerbrand.lean`, `Local/AdicUnits.lean`,
  `Local/UnitHerbrandChain.lean`, `Local/UnitValuation.lean`) no longer needs the valuation to be
  *surjective* onto `ℤᵐ⁰`.  A generator `m` of the value group (`IsUnitValGen A m`) and the divided
  map `unitValDiv hm x = unitVal x / m` have the same kernel, surject onto `ℤ`, and are
  `G`-invariant, so a merely **nontrivial** value group suffices.  This is what makes the class of
  local extensions closed under the dévissage: a fixed subfield has a nontrivial value group, but
  its value group is `|C|·ℤ`, not `ℤ`.

The one hypothesis still taken as input rather than proven is that every `K`-automorphism of `A` is
an isometry.  For a complete discretely valued `A` this is automatic — the valuation ring is the
integral closure of that of `K` — but proving it is an independent piece of work, and stating it as
a hypothesis keeps the dévissage usable for the abstract valued fields the Herbrand chain runs on.

### 0.20.1 The restriction map, computed (`Brauer/BaseChangeCentralizer.lean`)

Every use of the invariant map needs `res_{L/K} : Br(K) → Br(L)` evaluated on an explicit algebra,
and the classical formula is the *centralizer* formula: if `L` sits inside a central simple
`K`-algebra `A` and `B = C_A(L)`, then

```
L ⊗_K A  ≅  M_{[L:K]}(B)      as L-algebras,
```

so `res_{L/K} [A] = [C_A(L)]` in `Br(L)`.  `exists_algEquiv_matrix_of_range_eq_centralizer` is that
statement.  It is proved by making `A` a right `B`-module (a left `Bᵐᵒᵖ`-module, `BMod`), letting
`L ⊗_K A` act by right multiplication on the first factor and left multiplication on the second
(`toEndB`), and identifying the target:

* `A ≅ B^{[L:K]}` as `Bᵐᵒᵖ`-modules is *free for free* — `B` is simple (it is the centralizer of a
  simple subalgebra) and `SkolemNoether.nonempty_linearEquiv_of_finrank_eq` upgrades the dimension
  identity `dim_K A = [L:K] · dim_K B` to an isomorphism of modules, with no Wedderburn
  decomposition and no explicit basis;
* `End_{Bᵐᵒᵖ}(B^d) ≅ M_d(End_{Bᵐᵒᵖ} B) ≅ M_d(B)` — the second step is `AlgEquiv.moduleEndSelfOp`,
  and it is `B` rather than `Bᵐᵒᵖ` precisely because the module is a *right* module;
* `L ⊗_K A` is simple, so `toEndB` is injective, and the two sides have the same `L`-dimension.

The statement is phrased with an abstract `B` and an injective `g : B →ₐ[K] A` whose range is the
centralizer, the embedding of `L` being *derived* as `g ∘ (algebraMap L B)`; this avoids having to
put an `Algebra L` structure on the subtype `↥(Subalgebra.centralizer K …)` at the call site.
Taking `B = L` recovers `exists_algEquiv_matrix_of_centralizer_eq_range` of `Brauer/Centralizer.lean`
(a self-centralizing subfield splits), and taking `L = K` gives `K ⊗ A ≅ M_1(A)`.

### 0.20.2 Restriction on crossed products (`Brauer/CrossedProductRestrict.lean`)

§0.20.1 computes `res` in terms of a centralizer; this section computes that centralizer in the one
case every invariant-map argument needs.  Let `E / K` be finite Galois, `f` a multiplicative
`2`-cocycle of `Gal(E/K)` with values in `Eˣ`, and `M` an intermediate field.  Then

```
C_{(E/K, f)}(M) = (E/M, f|_{Gal(E/M) × Gal(E/M)}),
```

and consequently

```
res_{M/K} [E/K, f]  =  [E/M, f|_{Gal(E/M)}]    in Br(M).
```

`baseChangeHom_mk_csa` is that identity; `nonempty_algEquiv_matrix_restrict` is the algebra
statement `M ⊗_K (E/K, f) ≅ M_{[M:K]}((E/M, f|))` it comes from.  On the cohomological side
`restrictCocycle` is literally the restriction of cochains along `Gal(E/M) → Gal(E/K)`, so this says
the diagram

```
H²(Gal(E/K), Eˣ) ──→ Br(K)
      │ res                │ res
      ▼                    ▼
H²(Gal(E/M), Eˣ) ──→ Br(M)
```

commutes — the compatibility that turns `inv_L ∘ res = [L:K] · inv_K` into a computation with
cocycles.

Three points of the Lean encoding are worth recording.

* The centralizer half is a support computation, not an algebra computation.  Writing `y` in the
  basis of symbols, `y · u_c = u_c · y` for `c ∈ M` reads coordinatewise as
  `(g c − c) · y_g = 0` (`toFinsupp_mul_incl` against `toFinsupp_incl_mul`), so every `g` in the
  support of `y` fixes `M` pointwise.  `Finsupp.mapDomain_comapDomain` then rebuilds `y` from the
  smaller crossed product.  `AlgEquiv.ofRingEquiv` is what promotes such a `g` to an element of
  `Gal(E/M)`.
* `CrossedProduct hf'` for the restricted cocycle carries an `Algebra M` structure but **no**
  `Algebra K` structure globally — `M` is not central in `CrossedProduct hf`, so declaring one as an
  instance would be wrong.  It is introduced with `letI` inside the proof of
  `nonempty_algEquiv_matrix_restrict`, via `RingHom.toAlgebra'` on `incl hf' ∘ algebraMap K E`,
  exactly long enough to feed `exists_algEquiv_matrix_of_range_eq_centralizer`.  This is why that
  brick was stated with an abstract `B` and a derived embedding of `L`.
* `AlgEquiv.restrictScalars K : Gal(E/M) → Gal(E/K)` is definitionally the identity on underlying
  maps, so `restrictScalars_one`, `restrictScalars_mul`, `restrictScalars_apply` and
  `restrictScalars_smul_units` are all `rfl` — but `rw` will not close goals by them, and each of
  the multiplicativity proofs needs them spelled out.

### 0.20.3 Route (c) is *free*: Albert–Brauer–Hasse–Noether over `ℚ` with no hypothesis at all

The four preceding sections all end with the same recommendation — build the invariant map, because
(T5) needs reciprocity.  That recommendation is now wrong for gap 1.  Route (c)'s form of (T5) is a
theorem, and its proof does not touch reciprocity.

```lean
InverseGalois.CFT.exists_isMulCoboundary_of_forall_ramified
    {K : Type} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K] {n : ℕ} (hn : n ≠ 0)
    {a : Gal(K/ℚ) → Gal(K/ℚ) → ℚˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z, a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v, ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal → ‹local coboundary at v›) :
  ∃ b : Gal(K/ℚ) → Kˣ, ∀ g h, g • b h / b (g * h) * b g = Units.map (algebraMap ℚ K) (a g h)
```

No parity of `n`, no condition at the archimedean place, no square root of minus one, no total
reality: **a torsion two-cocycle of rational units which is a coboundary at every ramified finite
place is a coboundary.**  That is (T5) with the archimedean place omitted, which §0.20 identified as
exactly what route (c) buys its deficiency-zero corrector count with.

#### Why no reciprocity is needed

§0.18 proved the same statement under the extra hypothesis `ι² = −1` in `K`, and §0.19 concluded
that the hypothesis was fatal because it makes the place above `2` ramified.  It is fatal only if
one insists that `K` be the field the induction carries.  It need not be: the hypothesis can be met
by **enlarging** `K`, and the enlargement never enters the conclusion.

* `K/ℚ` finite Galois is the splitting field of a separable `p ∈ ℚ[X]`
  (`IsGalois.is_separable_splitting_field`).  Put `L := (p · (X² + 1)).SplittingField`.  Then `L/ℚ`
  is finite Galois, contains a root of `X² + 1`, and receives `K` by
  `Polynomial.IsSplittingField.lift`.
* Inflate the cocycle along `AlgEquiv.restrictNormalHom K : Gal(L/ℚ) → Gal(K/ℚ)`.  Cocycle identity
  and `n`-torsion inflate for free.
* The local hypothesis inflates too, and this is the point that §0.19 missed.  A place `w` of `L`
  lies above a place `v` of `K`; the inflated cocycle's local condition at `w` is the image of the
  condition at `v` under the decomposition-group restriction and the map on local units.  It is
  therefore supplied at **every** place `w` of `L`, ramified or not — including the places above `2`
  that the enlargement has just ramified — because it is supplied at every place of `K` that the
  criterion asks about, and the unramified places of `K` are discharged by
  `exists_sub_add_eq_adicUnits_of_nsmul_eq_zero` as always.  Ramification created *by the
  enlargement* costs nothing, because the hypothesis is transported from below rather than checked
  above.
* Apply §0.18 over `L`, and descend: a coboundary whose values are inflated is a coboundary
  downstairs, because `Gal(L/ℚ) ↠ Gal(K/ℚ)` and the cochain can be pushed through Hilbert 90 for
  the kernel.

So the dyadic place, which under `ι ∈ K` was a genuine obstruction *for `K`*, is not one *for `L`*:
the whole content of §0.19's negative computation is that `−1` is not a norm from `ℚ₂(i)`, and the
inflated cocycle never has to be a norm anywhere, only to be a coboundary where it already is one.

#### Modules

* `Units/TowerCoboundary.lean` — a family of units of the base which is a local coboundary at a
  place of a middle field inflates to a local coboundary at every place above it.  The compatibility
  content is `adicCompletionAut_adicCompletionComap_restrict`: the automorphism of the completion
  attached to `σ ∈ D_w` and the one attached to its restriction agree on the completion below, both
  being continuous and agreeing on a dense image.
* `Units/InflationDescent.lean` — `exists_isMulCoboundary_of_restrictNormalHom`: a global coboundary
  for the inflated cocycle descends.
* `Units/ABHNFinite.lean` — the assembly, plus the unramified-place bookkeeping
  (`exists_sub_add_eq_adicUnits_of_pow_eq_one`).

The consumers in `Kummer/CentralEmbeddingSqrtNegOne.lean` lose the hypothesis and are renamed
`exists_surjective_hom_rat_of_forall_ramified{,_lift,_pow,_primeResidue,_lift_or_primeResidue}`.

#### One Lean obstacle, and how it was side-stepped

The natural enlargement is the compositum `K ⊔ ℚ(i)` inside a fixed algebraic closure.  That does
not work: for `S : IntermediateField ℚ Ω` there are several competing `Algebra ℚ ↥S` structures
(`IntermediateField.algebra'`, `DivisionRing.toRatAlgebra`, and the `SMul` coming from
`SubfieldClass`), they are propositionally but not definitionally equal, and for the relative
compositum `supOver A K : IntermediateField ↥K Ω` instance search resolves `Algebra ℚ ↥(supOver A K)`
to `DivisionRing.toRatAlgebra`, so `FiniteDimensional ℚ`, `IsGalois ℚ` and
`IsScalarTower ℚ ↥K ↥(supOver A K)` all fail to synthesize.  `Subsingleton.elim` transports a *Prop*
across the diamond but cannot repair instance search inside a later `haveI`.

For an **abstract** `L` there is no diamond at all — `L` carries one `Algebra ℚ` structure, the one
it was given.  `Polynomial.SplittingField` is abstract, `Normal.of_isSplittingField` and
`NumberField.of_module_finite` supply the two instances, and `IsSplittingField.lift` plus
`IsScalarTower.of_algebraMap_eq fun x => (lift.commutes x).symm` supply the tower.  This is the
pattern of `Mathlib/FieldTheory/PolynomialGaloisGroup.lean`, and it is the recommended shape for any
"enlarge the field" step in this layer.

One tactic note: writing `set q := p * (X ^ 2 + C 1)` makes `rw` rewrite inside `q.SplittingField`
and unfold the construction again.  Introducing `q` by `obtain ⟨q, hqp, hqc⟩ : ∃ q : ℚ[X], _ := …`
keeps it an opaque local, which is what the downstream `letI : Algebra K q.SplittingField` needs.

#### What this changes strategically

| | before | now |
|---|---|---|
| gap 1, `ℓ = 2` Scholz–Reichardt | blocked on (T5), i.e. on the invariant map | **local–global layer complete**; blocked on the induction invariant |
| gap 2, `ElementaryAbelianKernelEP` | blocked on Grunwald–Wang | unchanged — still needs the invariant map |

The invariant map is still worth building, and it is still the only route to gap 2.  It is no longer
on the critical path for gap 1.

#### What `ℓ = 2` still needs

Route (c)'s induction invariant: `K/ℚ` Galois with `Gal(K/ℚ)` a `2`-group, **unramified at `2`**,
every other ramified prime `≡ 1 mod 2^N`, and **no condition at the archimedean places**.  Against
that invariant:

1. **The local–global step.**  Done, by the theorem above; at `ℓ = 2` no cyclotomic base change is
   needed either, since `μ₂ ⊂ ℚ`, so `Scholz/ProperSolution.lean`'s detour through
   `cycSubfield ℓ` collapses.
2. **The dyadic corrector.**  `IsInertiaRankOneAt 2` is false and stays false (§0.16); what replaces
   it is a rank-**two** cancellation at the dyadic place, the two generators being the classes of
   `−1` and `2`.  `{−1, 2, −2}` spans the target exactly: deficiency zero, and the auxiliary prime
   keeps its congruence `q ≡ 1 mod 2^N` (no `q ≡ 3 mod 4` is needed, which is what makes route (c)
   better than §0.17's escape).  *The justification of "deficiency zero" given when this was first
   written was wrong; see §0.21 for the correct one and for what it costs.*
3. **§0.16 item 1**, the radicand.  `RadicalDisjoint`/`NilpotentRadical` are false at `2`; the
   replacement is the dimension count against the quadratic subfields of `A` — the bad radicands
   form a subgroup of `ℚ^×/(ℚ^×)²` of order `2^{d(G)}`, and `Scholz/ResidueSpan.lean` has to be made
   to dodge it.

---

## 0.21 Status (2026-08-27) — the `ℓ = 2` local–global step is *landed*; the dyadic corrector, correctly analysed

### What landed

Three modules, all sorry-free and in the default build.

* **`Scholz/ProperSolutionTwo.lean`** — `hasProperSolution_two`.  A central Frattini embedding
  problem with kernel of order `2`, posed over a field `A` of two-power degree satisfying `(S_{N+1})`,
  is solvable over an extension of `A`.  The proof is the direct application of §0.20.3's
  hypothesis-free ABHN over `ℚ`: `IsPrimitiveRoot (-1 : ℚ) 2` supplies the root of unity, so there is
  **no cyclotomic base change**, and there is **no condition at the archimedean place**.  The local
  hypothesis at each ramified place is `isCyclic_and_exists_hasResidueChar_rat`, which reads Serre's
  condition off the places of `A` directly instead of transporting it to a compositum.
* **`Scholz/CentralStepTwo.lean`** — `exists_surjective_hom_of_isScholz_two` and
  `exists_surjective_hom_of_centralStep_two`.  Same interface as the odd-`ℓ`
  `exists_surjective_hom_of_{isScholz,centralStep}`, with `Odd ℓ` gone and the coprime-index descent
  deleted: the `ρ` that `HasProperSolution` supplies **is** `galRestrictLE`, which is exactly what
  the coercion clause of `HasProperSolution` says.
* **`Scholz/CentralCyclicLift.lean`** — the group-theoretic heart of the dyadic corrector, see below.

One Lean note worth keeping.  `ProperSolutionTwo`'s local lemma is stated for
`{K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]` with **no `[Algebra ℚ K]` binder**.  Adding
one makes the algebra structure an opaque `fvar` which cannot unify with the
`DivisionRing.toRatAlgebra` baked into `IsScholz.isCyclic_stabilizer`,
`mul_card_stabilizer_dvd_sub_one` and `inertia_ne_bot_iff_mem_ramifiedSet`.  For
`A : IntermediateField ℚ (AlgebraicClosure ℚ)` the two candidate instances
`IntermediateField.algebra' A` and `DivisionRing.toRatAlgebra` are equal by `rfl`, so the call site
works; it is only the section variable that breaks it.

### The dyadic corrector: the earlier sketch was right, the earlier *reason* was not

§0.20.3 item 2 asserted that `{−1, 2, −2}` spans the dyadic target exactly, i.e. deficiency zero.
That conclusion stands.  The justification offered there — "the decomposition group at `2` of the
solution field is abelian, so its inertia character is determined by `ℚ₂`" — does **not** work, and
the failure is instructive enough to record.

Write `L₀ ⊇ A` for the solution field, `A` unramified at `2`, `C := ker f ≅ ℤ/2` central.  Then
`I_2(L₀) ⊆ Gal(L₀/A) = C` and `D_2(L₀)/I_2` is cyclic, so `D := D_2(L₀)` really is abelian.  But
abelian is not enough: `D` can be cyclic of order `4` with `I_2 = D²` the subgroup of squares, and
then `Ψ|_{I_2}` — a surjection `I_2 ↠ ℤ/2` — does **not** extend to any character of `D`, so no
comparison with a character of `D` can produce the corrector.  Such a `D` genuinely occurs: by local
class field theory the map `ℚ₂^× → ℤ/4`, `2 ↦ 1`, `−1 ↦ 2`, `1 + 4ℤ₂ ↦ 0`, cuts out a cyclic quartic
extension of `ℚ₂` with `e = 2, f = 2` whose inertia subgroup is the squares.

What *is* true is the same statement one level up, over the absolute Galois group of `ℚ₂` rather
than over `D`:

> Because `2` is unramified in `A`, the local embedding problem at `2` has an **unramified**
> solution: `G_{ℚ₂}` has a procyclic unramified quotient, and Frobenius may be sent to any preimage
> in `G` of the Frobenius image in `H`.  The global solution and the unramified local one differ by
> a genuine character `μ : G_{ℚ₂} → C` (their ratio is a homomorphism because `C` is central), and
> `Ψ|_{I_2} = μ|_{I_2}` because the unramified solution is trivial on inertia.  A quadratic character
> of `ℚ₂` is `χ_c` for `c ∈ ℚ₂^×/(ℚ₂^×)²`, a group of order `8` with representatives
> `±1, ±2, ±5, ±10` of which `5` is the unramified class; so `μ|_{I_2} = χ_d|_{I_2}` for one of the
> four **rational** classes `d ∈ {1, −1, 2, −2}`.

Deficiency zero, confirmed — and the reason is the unramified local solution, not abelianness.

Two consequences worth stating plainly.

* Whether the dyadic place can be removed is **not** an invariant of the solution that a twist can
  change: twisting `Ψ` by a quadratic character `λ` replaces `Ψ|_{I_2}` by `Ψ|_{I_2}·λ|_{I_2}`, and
  `λ|_{I_2}` is always one of the four classes above.  It is a property of the embedding problem,
  and the argument above is what makes it always favourable.
* Allowing the corrector to be `χ_m` for a general rational `m` (rather than `m ∈ {−1, 2, −2}`) buys
  nothing at `2`: `χ_m|_{I_2}` depends only on the class of `m` in `ℚ₂^×/(ℚ₂^×)²` modulo the
  unramified class, i.e. only on `m` mod `⟨5⟩`, i.e. on one of the same four classes.  An auxiliary
  prime `q ≡ 5 mod 8` contributes the unramified class and is invisible on inertia.

### Making the unramified lift finite — `Scholz/CentralCyclicLift.lean`

The argument above lives on `G_{ℚ₂}`, which the repository does not have.  It can be made finite.
The only thing `G_{ℚ₂}` was used for is: *the unramified quotient is procyclic of order divisible by
`exp G`, so Frobenius may be sent anywhere.*  A finite Galois `M/ℚ` has `D/I` cyclic of order the
residue degree at `2`, so it suffices to make the residue degree divisible by `exp G` — and that
costs one elementary enlargement:

> For every `k`, any prime divisor `r` of `2^{2^k} + 1` has `ord_r(2) = 2^{k+1}` exactly
> (`2^{2^k} ≡ −1`, so the order divides `2^{k+1}` and does not divide `2^k`).  Hence in `ℚ(ζ_r)` the
> prime `2` is unramified with residue degree `2^{k+1}`.  Adjoin such an `r` with `2^{k+1} ≥ |G|`.

Inertia upstairs surjects onto inertia downstairs, so a cancellation proved over `M·ℚ(ζ_r)` descends
to `M`; and the enlargement is unramified at `2` and at every prime of the Scholz set, so it costs
the induction invariant nothing except the prime `r`, which is an ordinary correctable prime.

With the residue degree arranged, the group-theoretic step is exactly:

```lean
InverseGalois.CFT.exists_monoidHom_range_le_ker_eqOn
    {D G H : Type*} [Group D] [Group G] [Group H] {I : Subgroup D} [I.Normal]
    (hcyc : IsCyclic (D ⧸ I)) (hexp : ∀ g : G, g ^ Nat.card (D ⧸ I) = 1)
    {f : G →* H} (hZ : f.ker ≤ Subgroup.center G) {θ : D →* G} (hI : ∀ σ ∈ I, θ σ ∈ f.ker) :
  ∃ μ : D →* G, μ.range ≤ f.ker ∧ ∀ σ ∈ I, μ σ = θ σ
```

together with its `Nat.card G ∣ Nat.card (D ⧸ I)` corollary.  The proof picks a generator of `D ⧸ I`
and a preimage `x`, builds the homomorphism `D →* G` killing `I` and sending `x ↦ θ x` (legitimate
because the order of the quotient kills `G`), observes that it agrees with `θ` after composing with
`f` — the two agree on `I` and at `x`, which generate `D` — and takes the pointwise ratio, which is
a homomorphism because `f.ker` is central.  Supporting lemma:
`exists_monoidHom_apply_eq_of_forall_mem_zpowers`, a homomorphism out of a cyclic group prescribed
freely on a generator.

### What the dyadic corrector still needs

1. **(F2), the local Kummer fact — the route is settled and most of its bricks have landed.**
   Let `M/ℚ` be finite Galois, `P | 2`, `D` and `I` the decomposition and inertia groups at `P`,
   `Z` the decomposition field, and `μ : Gal(M/Z) →* ℤ/2` any character.  Then there is
   `d ∈ {1, −1, 2, −2}` with `μ` and `χ_d` agreeing on `I`.  The proof needs **neither** the
   completion `v.adicCompletion ℚ` **nor** the square-class count `[ℚ₂^× : (ℚ₂^×)²] = 8`: it is a
   statement about the place `w` of `Z` under `P`, which has `e(w/2) = f(w/2) = 1`, and the only
   input is that `2` is a uniformizer there and the residue field is `𝔽₂`.
   - *Step A*, `e = f = 1` at the decomposition field: `ramificationIdx_eq_one_of_stabilizer_le`
     (`Scholz/FixedFieldRamification.lean`), with `U := stabilizer Gal(M/ℚ) P`.  **In repo.**
   - *Step B*, the quadratic subextension cut by `μ` is generated by a square root `y` of some
     `β ∈ Z`: Mathlib's `exists_root_adjoin_eq_top_of_isCyclic`.  **In Mathlib.**
   - *Steps C/D*, the square class: **landed** as `Kummer/DyadicSquareClass.lean` (pure valuation
     layer — for a unit `u` exactly one of `(u ± 1)/2` lies in the place, and one of `1, 2` makes
     the exponent of the uniformizer even) and `Kummer/DyadicPlace.lean` (the bridge, reading the
     uniformizer off `e = 1` and the residue field off `f = 1`).
   - *Step E*, a radical whose radicand is congruent to one modulo four is unramified:
     `eq_of_isCongrPow` (`Kummer/InertiaBound.lean`).  **In repo.**
   - *Step F*, the assembly `α := y·√d`: **landed** as `Kummer/DyadicInertiaChar.lean`
     (`exists_sq_intCast_eqOn_inertia`).  Requiring `i, √2 ∈ M` — that is, `ζ₈ ∈ M`, which the
     induction may arrange because `ℚ(ζ₈)/ℚ` is a `2`-extension ramified only at `2` — removes the
     need for any compositum: `√d ∈ M` for all four `d`, so `y·√d` is a radical inside `M` itself.
     The companion `Kummer/QuadraticChar.lean` (`sqrtChar`, `sqrtChar_range_le`,
     `sqrtChar_eq_one_of_mem_inertia`) turns a square root of one of `1, −1, 2, −2` into a genuine
     character of `Gal(M/ℚ)` with values in any subgroup containing a prescribed element of order
     dividing two, and shows it is trivial on inertia at every place away from `2`.
   - *Step G*, extending `θ|_I` to `μ` on `D`: **landed** as `Scholz/DecompositionLift.lean`
     (`exists_monoidHom_stabilizer_eqOn_inertia`), which wires
     `exists_monoidHom_range_le_ker_eqOn_of_card_dvd` (`Scholz/CentralCyclicLift.lean`) to the
     cyclicity of `D/I` and needs `|G| ∣ |D/I| = f(P/2)`.
   - *Step H* = (F1′), making `2^k ∣ f(P/2)` by adjoining `ℚ(ζ_r)` for `r = 2^{2^k}+1`, so that
     `ord_r(2) = 2^{k+1}`: **landed** as `Scholz/DyadicResidueDegree.lean`
     (`pow_dvd_inertiaDeg_two_of_cycSubfield_le`).  Primality of the Fermat number is *not* needed:
     `2^{2^k} ≡ −1 (mod 2^{2^k}+1)` alone pins the order.
   - *The assembly*: **landed** as `Scholz/DyadicCorrector.lean` (`hasCorrectingCharAt_two`).
     Given `|ker f| = 2`, `ζ₈ ∈ M`, `θ` unramified at `P | 2` and `|G| ∣ f(P/2)`, it produces
     `HasCorrectingCharAt M f 2 θ` with `a = −1`.  The one case split is on whether the extension
     `ν` of `θ|_I` to `Gal(M/Z)` is trivial: if it is, `χ := 1` and `a := 0` already work.
     What remains to feed it is arithmetic, not algebra — the induction must arrange `ζ₈ ∈ M` and
     `|G| ∣ f(P/2)`, both by enlarging `M` inside a `2`-extension ramified only at `2`.
2. **(F3), the `θ`-relative refactor of `Scholz/RamificationControl.lean`.  DONE** (commit
   `13eb747`): `HasCorrectingCharAt M f p θ` carries the solution as a parameter.
   Historical note: `HasInertiaCancellation`
   currently quantifies over *all* `θ`; at `2` the cancellation holds only for the solution actually
   in hand.  `HasCorrectingChar` must therefore carry the current solution as a parameter, and
   `exists_twist_ramifiedSet_inter` must re-establish it after each twist.  That is sound — twisting
   at `p` multiplies the solution by a character trivial on inertia at every `q ≠ p`, so the
   restriction to inertia at `q` is unchanged — but `exists_twist_ramifiedSet_sdiff` does not
   currently expose the twisting formula `ψ₁ = ψ · χ^a`, so it needs strengthening first.
3. **`Scholz/UnramifiedSolution.lean`.**  `hodd` and `IsInertiaRankOneAt ℓ` enter
   `exists_galEquiv_ramifiedSet_subset` at exactly two points: the call to
   `exists_galEquiv_of_centralStep` (now replaceable by an `ℓ = 2` analogue built on
   `exists_surjective_hom_of_centralStep_two`), and the call to `hasInertiaCancellation_of_isPGroup`
   at `p = ℓ`.  Away from `ℓ`, cyclic inertia already gives the cancellation for free, so the surgery
   is confined to those two lines plus item 2.
4. **§0.16 item 1**, the radicand, unchanged: `RadicalDisjoint`/`NilpotentRadical` are false at `2`
   and the replacement is the dimension count against the quadratic subfields of `A`.

---

## 1. Scholz–Reichardt

### 1.1 Statement

> **Theorem (Scholz 1937, Reichardt 1937).** *Let ℓ ≠ 2 be a prime. Every finite ℓ-group is a
> Galois group over ℚ. Equivalently, every finite nilpotent group of odd order is a Galois group
> over ℚ.*

Serre, *Topics in Galois Theory* (Harvard 1988, notes by H. Darmon, Jones & Bartlett 1992),
**Theorem 2.1.1**, §2.1 (pp. 9–16). Note the section number: the Scholz–Reichardt material is
§2.**1**, not §2.2; §2.2 is the Frattini subgroup. Malle–Matzat, *Inverse Galois Theory*
(Springer Monographs in Mathematics, 1999) treats embedding problems in **Chapter IV**.

Originals:
* A. Scholz, *Konstruktion algebraischer Zahlkörper mit beliebiger Gruppe von
  Primzahlpotenzordnung I*, Math. Z. **42** (1937), 161–188.
* H. Reichardt, *Konstruktion von Zahlkörpern mit gegebener Galoisgruppe von
  Primzahlpotenzordnung*, J. reine angew. Math. **177** (1937), 1–5.

Serre's remarks after Thm 2.1.1, verbatim in substance:
1. It is a special case of Shafarevich's theorem.
2. If |G| = ℓᴺ the extension can be chosen ramified at **at most N primes**.
3. **The proof does not work for ℓ = 2.**
4. **It is not known whether there is a regular Galois extension of ℚ(T) with Galois group G for
   an arbitrary ℓ-group G.** ← *This kills any attempt to reach ℓ-groups through this
   repository's regular-realization machinery; see §5.*

### 1.2 The Scholz condition

Fix an ℓ-group G and N ≥ 1 with sˡ^ᴺ = 1 for all s ∈ G (i.e. ℓᴺ is a multiple of exp G).

> **Definition 2.1.2 (Serre).** A Galois extension L/ℚ has property **(S_N)** if every prime p
> ramified in L/ℚ satisfies:
> 1. p ≡ 1 (mod ℓᴺ);
> 2. for every place v | p of L, the inertia group I_v equals the decomposition group D_v.
>
> Condition 2 says exactly that L_v/ℚ_p is *totally ramified*, i.e. its residue field is 𝔽_p.

### 1.3 The induction

Every ℓ-group is built from a chain of central extensions with kernel of order ℓ. The theorem is
the following statement applied inductively along such a chain:

> **Theorem 2.1.3 (Serre).** Let L/ℚ be Galois with group G, with property (S_N). Let
> 1 → C_ℓ → G̃ → G → 1 be central with C_ℓ cyclic of order ℓ, and assume ℓᴺ is a multiple of
> exp G̃. Then the embedding problem for L and G̃ has a solution L̃ which again satisfies (S_N)
> and is ramified at **at most one more prime** than L. (Moreover that prime may be taken from
> any set of primes of density one.)

The proof splits into the split case G̃ ≅ G × C_ℓ and the non-split case, the latter in three
stages: (i) solve the embedding problem at all; (ii) modify the solution so it is unramified
outside ram(L/ℚ); (iii) modify further so (S_N) holds, at the cost of one new prime.

There is also a profinite corollary (Serre Thm 2.1.11): every *separable pro-ℓ group of finite
exponent* is a Galois group over ℚ. The finite-exponent hypothesis cannot be dropped
(ℤ_ℓ × ℤ_ℓ is not a Galois group over ℚ).

### 1.4 Arithmetic inputs, step by step — the (a)/(b)/(c)/(d) classification

Legend: **(a)** elementary; **(b)** Dirichlet on primes in AP; **(c)** Chebotarev density;
**(d)** class field theory / reciprocity.

| # | Where | What is needed | Class |
|---|---|---|---|
| 1 | Split case, choice of q | ∃ prime q ≡ 1 (mod ℓᴺ), q split completely in L, each ramified pᵢ an ℓ-th power mod q | **(a)** |
| 2 | Non-split, stage (i) | H²(ℚ, C_ℓ) → ∏_p H²(ℚ_p, C_ℓ) injective (Serre Lemma 2.1.5) | **(d)** |
| 3 | Non-split, stage (i) | Local liftability at unramified p (lift a map from Ẑ) | **(a)** |
| 4 | Non-split, stage (i) | Local liftability at ramified p: structure of the maximal abelian tame exponent-ℓᴺ extension of ℚ_p | **(d)**-lite (local) |
| 5 | Non-split, stage (ii) | Glue local abelian characters into one global Dirichlet character (Serre Lemma 2.1.6) | **(d)**, but = Kronecker–Weber over ℚ |
| 6 | Non-split, stage (iii) | Linear disjointness of L, F, ℚ(μ_ℓ, p^{1/ℓ} : p ∈ S) (Serre Lemma 2.1.9) | **(a)** (group theory + ramification) |
| 7 | Non-split, stage (iii) | ∃ prime q with prescribed *non-trivial* Frobenius | **(c)** as written — reducible, see §1.5 |

Detail on each:

**1. The split case is elementary.** Serre reduces the three conditions on q ("q ≡ 1 mod ℓᴺ",
"q splits completely in L", "each of the finitely many ramified pᵢ is an ℓ-th power in 𝔽_q") to
the *single* condition that q split completely in the field
L(μ_{ℓᴺ}, p₁^{1/ℓ}, …, p_m^{1/ℓ}); one then uses:

> **Lemma 2.1.4 (Serre).** If E/ℚ is a finite extension, there are infinitely many primes that
> split completely in E. (The refinement "every set of density one contains such a prime" needs
> Chebotarev; the bare existence statement does not.)

Serre's elementary proof: take E Galois with primitive element having integral minimal polynomial
f of degree n. If only finitely many primes p₁,…,p_k split completely or ramify, then f(x) is of
the form ±p₁^{m₁}⋯p_k^{m_k} for every x ∈ ℤ. For 1 ≤ x ≤ X, f takes ≥ X/n distinct values, but
the number of integers of that shape up to the relevant size is only a power of log X.
Contradiction. **No L-functions, no density.** This is exactly the flavour of the counting
already in `InverseGalois/NumberTheory/PrimeLowerBound.lean`.

**2. Brauer–Hasse–Noether.** Serre proves Lemma 2.1.5 by passing to K = ℚ(μ_ℓ) (degree prime to
ℓ, so H²(ℚ,C_ℓ) ↪ H²(K,C_ℓ)), identifying H²(K,C_ℓ) ≅ Br(K)[ℓ] via C_ℓ ≅ μ_ℓ over K, and
invoking Albert–Brauer–Hasse–Noether: an element of Br(K) that is locally trivial is trivial.
Since ℓ ≠ 2 the archimedean places can be ignored. **This is irreducibly class field theory**:
it *is* the fundamental exact sequence 0 → Br(K) → ⊕_v Br(K_v) → ℚ/ℤ → 0. The equivalent
formulations (Ш²(ℚ, ℤ/ℓ) = 0, Poitou–Tate) are no cheaper.

**4. Local liftability at ramified p.** Because p ≡ 1 (mod ℓᴺ) we have p ≠ ℓ, so L_v/ℚ_p is
tame; by (S_N) its group D_v = I_v is cyclic. The map G_{ℚ_p} → D_v ⊂ G factors through
Gal(E/ℚ_p) with E the maximal abelian tame extension of ℚ_p of exponent dividing ℓᴺ, and
E = (unramified of degree ℓᴺ)·ℚ_p(p^{1/ℓᴺ}), so Gal(E/ℚ_p) ≅ (ℤ/ℓᴺ)², which is projective in the
category of abelian groups of exponent | ℓᴺ. The preimage of D_v in G̃ is abelian (central
extension of a cyclic group), hence the lift exists. Formally this is local class field theory,
but only the explicit tame/Kummer part of it: it can in principle be done by hand from Kummer
theory (μ_{ℓᴺ} ⊂ ℚ_p) plus the structure of the tame quotient ⟨σ,τ | στσ⁻¹ = τ^p⟩. **Rated
(d)-lite: hard but not the global reciprocity law.**

**5. Gluing local characters — this is Kronecker–Weber.** Serre's Lemma 2.1.6: given continuous
ε_p : Gal(ℚ̄_p/ℚ_p) → C into a finite abelian group, almost all unramified, there is a unique
ε : G_ℚ → C agreeing with each ε_p on inertia I_p. His proof identifies ε_p with a map
ℚ_p^× → C by *local class field theory*, reads off conductors, and builds
ε : (ℤ/Mℤ)^× → C with M = ∏ p^{n_p} and ε(k) = ∏_p ε_p(k^{-1}); the fact that this Dirichlet
character has the required local behaviour is *global* class field theory (equivalently: the
idele decomposition I_ℚ = (∏_p ℤ_p^× × ℝ_+^×) × ℚ^×). **Over ℚ specifically, this is exactly
Kronecker–Weber plus the explicit ramification/Frobenius dictionary for cyclotomic fields**,
which is a strictly smaller target than CFT over a general number field. It is nevertheless
absent from Mathlib.

Proposition 2.1.7 and Corollary 2.1.8 are formal consequences of Lemma 2.1.6 (pure diagram
chasing, class **(a)** once 2.1.6 is granted): a lifting can be prescribed on all inertia groups,
in particular chosen unramified wherever φ is.

**6. Linear disjointness (Lemma 2.1.9).** L and F are linearly disjoint because they ramify at
disjoint sets (F ⊂ ℚ(μ_{ℓᴺ}) is the degree-ℓ^{N−1} part, totally ramified at ℓ). And
ℚ(μ_ℓ, p^{1/ℓ} : p ∈ S) has group V ⋊ 𝔽_ℓ^× over ℚ with V = (ℤ/ℓ)^{|S|} and 𝔽_ℓ^× acting by
scalars; **since ℓ ≠ 2 this group has no quotient of order ℓ**, so it contains no degree-ℓ Galois
subfield and is disjoint from L·F. *This is the only place in the whole argument where ℓ ≠ 2 is
used in an essential, visible way* — and it is pure finite group theory, class **(a)**.

**7. The one genuine Chebotarev use.** At stage (iii) one has, for each p ∈ S (the ramified
primes where the local inertia extension splits), a "defect" c_p ∈ C_ℓ, and one must correct φ̃ by
a Galois character χ : (ℤ/qℤ)^× → C_ℓ with (1) q ≡ 1 mod ℓᴺ, (2) χ(p) = c_p for p ∈ S, (3) q
splits completely in L. Writing S = {p₁,…,p_k} and c_{p_i} = c_{p₁}^{ν_i}, Serre requires a prime
q with

```
Frob_q = 1   in L·F and ℚ(μ_{ℓᴺ});
Frob_q ≠ 1   in ℚ(μ_ℓ, p₁^{1/ℓ});
Frob_q = 1   in ℚ(μ_ℓ, (p₁/p_i^{ν_i})^{1/ℓ}),  i = 2,…,k.
```

and concludes "By the Chebotarev density theorem and Lemma 2.1.9, such a q exists."

### 1.5 How much of (c) is really needed — the important reduction

All but one of the conditions in the display above are *"splits completely in a fixed number
field"*, i.e. Lemma 2.1.4, i.e. class **(a)**. Setting

* A := L · F · ℚ(μ_{ℓᴺ}) · ℚ(μ_ℓ, (p₁/p_i^{ν_i})^{1/ℓ} : i = 2,…,k),
* B := A(p₁^{1/ℓ}),

the whole Chebotarev input of Scholz–Reichardt is exactly:

> **(★)** Let A ⊂ B be number fields, B/ℚ Galois, [B:A] = ℓ. Then infinitely many rational primes
> split completely in A but **not** in B.

And (★) does **not** need Dirichlet's theorem. It follows from nothing more than the *simple pole
of the Dedekind zeta function*: for K/ℚ Galois of degree n,

```
log ζ_K(s) = Σ_{𝔭 of degree 1} N𝔭^{-s} + O(1) = n · Σ_{q splits completely in K} q^{-s} + O(1),
```

so if ζ_K(s) ~ c_K/(s−1) with c_K > 0 as s → 1⁺, then Σ_{q split in K} q^{-s} ~ (1/n)·log(1/(s−1)),
i.e. the Dirichlet density of the completely-split primes of K is 1/[K:ℚ]. Applying this to A and
to B and comparing 1/[A:ℚ] > 1/[B:ℚ] gives (★). **No Dirichlet L-functions, no non-vanishing at
s = 1, no Chebotarev machinery** — only the analytic class number formula, which Mathlib
*already has* as `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`
(`Mathlib/NumberTheory/NumberField/DedekindZeta.lean:75`). The missing piece is the Euler product
for ζ_K over prime ideals; since Mathlib's `dedekindZeta` is defined as the ℕ-indexed L-series of
`n ↦ #{I : absNorm I = n}`, and that coefficient function is multiplicative, this plugs directly
into `ArithmeticFunction.IsMultiplicative.eulerProduct`
(`Mathlib/NumberTheory/EulerProduct/Basic.lean:252`).

**So: the classification for Scholz–Reichardt is (a) + a weak-(c) that is cheaper than (b), plus
two irreducible (d)s (items 2 and 5).** The two (d)s are the blockers, not Chebotarev.

Historical note: Scholz's and Reichardt's original arguments used **ℓ-th power reciprocity** in
ℚ(μ_ℓ) to convert the condition "p_i is an ℓ-th power mod q" into a congruence condition on q
modulo p_i, then applied **Dirichlet's theorem** — i.e. classically item 7 is **(d)+(b)** rather
than (c). Serre's modernization trades reciprocity for Chebotarev. Either way it is item 7 that
is negotiable and items 2 and 5 that are not.

---

## 2. Shafarevich's theorem

### 2.1 Statement and sources

> **Theorem (Shafarevich 1954).** *Let k be a global field and G a finite solvable group. Then
> there is a finite Galois extension K/k with Gal(K/k) ≅ G.*

* I. R. Shafarevich, *Construction of fields of algebraic numbers with given solvable Galois
  group*, Izv. Akad. Nauk SSSR **18** (1954), 525–578; Amer. Math. Soc. Transl. **4** (1956),
  185–237. (Together with the three companion papers Izv. **18** (1954) 261–296, 327–334,
  389–418.)
* I. R. Shafarevich, *Factors of a decreasing central series*, Mat. Zametki **45** (1989),
  114–117 — **the correction**.
* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Grundlehren 323, 2nd ed.,
  **Chapter IX, §6**. (Chapter IX is "The Absolute Galois Group of a Global Field"; its main
  results are Grunwald–Wang and Shafarevich's theorem.)
* A. Schmidt, K. Wingberg, *Šafarevič's theorem on solvable groups as Galois groups*, preprint,
  <https://arxiv.org/abs/math/9809211> — **the complete, self-contained modern proof**, and the
  primary source used below. All theorem numbers "Thm n" in this section refer to it.
* Serre, *Topics in Galois Theory*, remark 1 after Thm 2.1.1 (Serre explicitly flags the gap and
  the correction; the theorem itself is one of the topics he omits, Foreword item (b)).

### 2.2 The reduction from "all solvable groups" to embedding problems

Two steps, both purely group-theoretic (Ore's argument, Duke Math. J. **5** (1939) 431–460):

> **Prop. 16** (Huppert, *Endliche Gruppen I*, III.3.2(b)). If N ⊴ G and N ⊄ Φ(G), then N has a
> proper supplement U ⊊ G, i.e. G = N·U.
>
> **Prop. 17** (Huppert III.4.2(c)). If G ≠ 1 is finite solvable then Φ(G) ⊊ F(G), where F(G) is
> the Fitting subgroup (the composite of all nilpotent normal subgroups).

Combining: F(G) ⊄ Φ(G), so F(G) has a proper supplement U ⊊ G, hence there is a surjection
**F(G) ⋊ U ↠ G**. F(G) is nilpotent and U is a smaller solvable group, realizable by induction on
|G|. So the theorem follows from:

> **Theorem 14.** Let K/k be a finite Galois extension of global fields with group G and
> φ : G_k ↠ G. Then **every split embedding problem with finite nilpotent kernel H**
> ```
> 1 → H → H ⋊ G → G → 1
> ```
> has a **proper** (= surjective) solution.

This is the exact reduction: **split embedding problems with nilpotent kernel**, nothing more.
Because a finite nilpotent group is the direct product of its Sylow subgroups, and every finite
G-operator p-group is a quotient of F(n)/F(n)^(τ) for the free pro-p G-operator group
F(n) = G ⋉ F_n (F_n free pro-p of rank n), it suffices to treat the *generic kernel*.

### 2.3 The filtration and the actual induction

Shafarevich's 1989 correction is precisely a **refinement of the descending p-central series**:

```
P¹ = P,   P^{i+1} = (P^i)^p [P^i, P];        (descending p-central)
P₁ = P,   P_{j+1} = [P_j, P];                (descending central)
P^{(i,j)} := (P^i ∩ P_j) · P^{i+1},   indices (i,j) ordered lexicographically.
```

> **Theorem 15 (sharpened form of Thm 14).** For every prime p, all n and all τ = (i,j) the split
> embedding problem with kernel F(n)/F(n)^(τ) has a proper solution N_n | k; and for p ≠ char k
> the solution can be chosen so that
> (i) all 𝔭 ∈ Ram(K|k) ∪ S_p ∪ S_∞ split completely in N_n|K; and
> (ii) if 𝔭 ramifies in N_n|K then 𝔭 splits completely in K|k and N_{n,𝔓}|k_𝔭 is a **cyclic
> totally ramified** local extension.

Conditions (i)–(ii) are the modern form of the **"Scholz solution"** — the direct descendant of
Serre's (S_N). The induction is on τ, with n arbitrary, in four substeps:
1. show the problem is locally solvable everywhere (after changing the previous solution);
2. deduce global solvability from a local–global principle;
3.–4. modify the global solution back into a Scholz solution so that step τ+1 is again locally
   solvable.

**The shrinking procedure** is the distinctive idea. Obstructions in step τ are genuinely
non-zero. Shafarevich's device: go back and re-do step τ−1 at a much larger level m ≫ n, then
push forward along a surjective G-equivariant φ : F(m) ↠ F(n) chosen so that all the obstructions
die. The combinatorial engine is:

> **Prop. 2.** Let G be finite, M, N finitely generated 𝔽_p[G]-modules, s,t ∈ ℕ. For r large
> enough: given z₁,…,z_t ∈ (⊕_r M)^{⊗s} ⊗ N there is 0 ≠ a ∈ 𝔽_p^r such that
> φ_a : ⊕_r M → M, (x_i) ↦ Σ a_i x_i is a surjective 𝔽_p[G]-map and the induced map kills every z_i.

Its proof is **Chevalley–Warning** (Serre, *A Course in Arithmetic*, Ch. I §2 Thm 3): the
common-zero set of t polynomials of degree s in r > s·t·dim variables over 𝔽_p contains a
non-trivial point. **Fully elementary.** Mathlib has Chevalley–Warning.

### 2.4 Arithmetic inputs

| Input | Where used | Class |
|---|---|---|
| Chebotarev / Dirichlet density of `cs(Λ\|k)` (density-1 sets of primes) | throughout: the sets S = cs(Λ\|k) ∪ T | **(c)** |
| Hasse principle Ш¹(k_S, T, A) = 0 for trivial modules and density-1 T | step 2 of each induction step | **(d)** (NSW VII 13.6) |
| **Poitou–Tate duality** (global) + **local duality** | Lemma 10, Thm 13 | **(d)** |
| **Grunwald–Wang**: coker(k_S,T,A) = 0 for δ(S) = 1, A trivial, T finite **with no prime above 2** | Prop. 11 (properness of solutions) | **(d)** |
| **Kummer theory**, local Frobenius in H¹(K_𝔓, μ_p)/H¹_{nr} | Thm 13 | (a)/(d)-lite |
| H²(G, 𝔽_p[G]ⁿ) = 0 (induced modules are cohomologically trivial) | Prop. 11 | **(a)** |
| cd_p G_k = 1 for p = char k, hence p-projectivity | the function-field case | **(d)** (Serre, *Cohomologie galoisienne* II §2 Prop. 3) |
| **Chevalley–Warning** | shrinking (Prop. 2) | **(a)** |
| Frattini/Fitting group theory (Ore) | final reduction | **(a)** |

Shafarevich's theorem is therefore **strictly harder** than Scholz–Reichardt in arithmetic
prerequisites: it needs everything Scholz–Reichardt needs *plus* Grunwald–Wang *plus* Poitou–Tate
duality. There is no known route around this.

Note also what Shafarevich's method *cannot* do: unlike Neukirch's strengthening of
Scholz–Reichardt (J. Neukirch, *On solvable number fields*, Invent. Math. **53** (1979) 135–164,
which realizes pro-solvable groups of finite exponent prime to #μ(k) with prescribed completions
at finitely many places), the shrinking procedure destroys prescribed local conditions.

### 2.5 Where the 2-group difficulty lies — precisely

The gap is **the "special case" of Grunwald–Wang**. In Schmidt–Wingberg's Prop. 11 the surjectivity
of

```
H¹(k, A) → ∏_{i=1}^r H¹(k_{𝔭_i}, A)
```

— which is what makes the solution of the embedding problem *proper*, i.e. surjective — is exactly
Grunwald–Wang, and it holds only when the finite set T of primes **contains no prime above 2**
(in the number-field case). That restriction is not removable: it is Wang's counterexample. The
cleanest statement of the obstruction: *in a cyclic degree-8 extension K/ℚ the prime 2 cannot be
inert*, i.e. the unramified degree-8 extension of ℚ₂ is not the completion of any cyclic degree-8
extension of ℚ. Equivalently, 16 is an 8th power mod almost every prime but is not an 8th power in
ℚ. Such obstructions occur only when 8 divides the exponent of the group. (Same phenomenon:
Lenstra's smallest abelian counterexample to Noether's problem over ℚ is ℤ/8ℤ — see §3.3.)

Shafarevich's 1954 argument used the descending p-central series and implicitly assumed a
Grunwald-type surjectivity that fails at p = 2. Alexander Schmidt found the gap; Shafarevich
sketched the correction in the notes to his Collected Papers (p. 752) and in the 1989 Mat. Zametki
note. **The correction is the refined filtration P^(i,j) = (P^i ∩ P_j)P^{i+1} of §2.3**: it makes
the induction step small enough that the auxiliary primes can always be chosen away from 2.
Schmidt–Wingberg's footnote 2 says so explicitly: *"This refinement, which was proposed by
Šafarevič in his correction note, is necessary in order to deal with the case p = 2."*

An independent, Serre-style treatment of just the 2-group case:
P. Schmid, *Realizing 2-groups as Galois groups following Shafarevich and Serre*,
Algebra & Number Theory **12** (2018), 2387–2401,
<https://doi.org/10.2140/ant.2018.12.2387> — every finite 2-group is realizable over ℚ with the
number of (tamely) ramified primes bounded by a polynomial in the rank of G (rather than by n as
for odd ℓ).

---

## 0.22 Status (2026-08-27) — the `ℓ = 2` correction has a *hypothesis*, and it is Schmid's

§0.21 item 3 is done: `Scholz/UnramifiedSolutionTwo.lean` proves
`exists_galEquiv_ramifiedSet_subset_two`, the dyadic analogue of
`exists_galEquiv_ramifiedSet_subset`, with **no** `Odd ℓ` and **no** `IsInertiaRankOneAt 2`.  That
is Schmid's Proposition 2.1 for `p = 2`.  The next link, the dyadic analogue of
`isScholzRealizable_of_centralStep`, turns out **not** to be a matter of removing `Odd ℓ` from
`Scholz/ResidueSpan.lean`.  There is a genuine obstruction, it is sharp, and it is exactly the
hypothesis of Schmid's Proposition 4.2.

### The obstruction, derived from the repository's own statements

Let `f : G ↠ H` be the central step, `Z = ker f` of order `2`, `Z ≤ frattini G`; let `A` be the
Scholz field realizing `H`, `S = ramifiedSet A`, and `L ⊇ A` a solution with `ramifiedSet L ⊆ S`.
For `p ∈ S` let `t_p ∈ 𝔽₂` be the Frobenius defect of `Scholz/FrobeniusDefect.lean` — `t_p = 0`
exactly when the residue degree of `p` in `L` is one, i.e. when `L` too is *busy* at `p`.

The correction twists by a character `χ` of conductor `Q`, a product of auxiliary primes `q`.  Every
such `q` must split completely in `L` (that is what makes the twisted homomorphism busy at `q`).
Now let `v = ∏_{p ∈ S'} p` for some `S' ⊆ S` and suppose `√v ∈ L`.  Then `q` splits in `ℚ(√v)`, so
`(v/q) = 1` for every `q ∣ Q`, so `χ(v) = 1`, and therefore

> **`Σ_{p ∈ S'} t_p = 0` is forced** for every `S'` with `√(∏_{p ∈ S'} p) ∈ L.

Because `Z ≤ frattini G`, the quadratic subfields of `L` are exactly those of `A`; and because every
`p ∈ S` is `≡ 1 mod 4` and `2 ∉ S`, the square classes `d` with `ℚ(√d) ⊆ A` are precisely the
`v = ∏_{p ∈ S'} p` (no factor `−1`, `2` or `−2` survives: each would ramify at `2`).  So the
achievable corrections are the vectors of `𝔽₂^S` orthogonal to

```
W  =  span { 1_{ramifiedSet ℚ(√d)}  :  ℚ(√d) ⊆ A quadratic }   ⊆   𝔽₂^S ,
```

a space of dimension `d(H) = dim H/Φ(H)`.  At odd `ℓ` the corresponding `W` is **zero** — that is
precisely `pow_ne_of_isNilpotent` (`Scholz/AuxPrimeChoice.lean:70`), which says a rational number
that is an `ℓ`-th power in an `ℓ`-extension of `ℚ` is already one, true because `ℚ(m^{1/ℓ})` is not
Galois.  At `ℓ = 2` it *is* Galois, `W` is as large as the number of generators, and the twist
simply cannot reach a defect vector with `Σ_{p ∈ S'} t_p = 1`.

**Consequence.**  `residueVectors_span_eq_top` is false at `2` and no reformulation of
`Scholz/ResidueSpan.lean` repairs it.  What must change is the *induction hypothesis*: the Scholz
field has to be built so that the defect is orthogonal to `W` **by construction**.

### This is Schmid's Proposition 4.2, and the fix is his shrinking process

P. Schmid, *Realizing 2-groups as Galois groups following Shafarevich and Serre*, ANT **12** (2018)
2387–2401 (open access) runs exactly this argument and names exactly this hypothesis.  His
vocabulary maps onto the repository's:

| Schmid | repository |
|---|---|
| `q` is *busy* (fleissig) in `K`: `φ(I_q) = φ(D_q)` | `IsSplitInertia` |
| Scholz field w.r.t. `N`: (S1) `Ram(K) ⊆ 1 + p^N ℤ`, (S2) busy | `IsScholz ℓ N` |
| Proposition 2.1 | `exists_galEquiv_ramifiedSet_subset_two` ✅ landed |
| Scholz obstruction `θ_q ∈ Z(H)` | the defect `z` of `exists_mem_ker_mul_mem_map_inertia` |
| Proposition 4.2 hypothesis `θ_i = Σ_{q ∈ Ram(P_i)} θ_q = 0` | `t ⊥ W` above |

The extra structure Schmid carries is the **strong** Scholz field: the socle
`S(K) = K^{Φ(G)} = P_1 ⋯ P_d`, where the `P_i` are quadratic and the sets `Ram(P_i)` are *pairwise
disjoint and of equal cardinality*.  Then `W` is spanned by the `d` block indicators `1_{Ram(P_i)}`
and the hypothesis is one bit per block — `d` conditions, not `|S|`.  Nothing forces those bits to
vanish; they are made to vanish by **shrinking**:

1. Realize, inductively on the `2`-class `c`, the *disposition group* `G_δ^{c−1} = F_δ/λ_c(F_δ)` for
   a much larger rank `δ = r·d`, where `λ` is the lower `2`-central series
   `λ_{n+1} = [λ_n, G]·λ_n²` and `r` is a polynomial in `d`.
2. Solve the central step (Proposition 2.1) to get `E_δ` with group `G_δ^c`, `Ram(E_δ) = Ram(K_δ)`;
   record the block obstructions `θ_{ij} ∈ λ_c(G_δ^c)` for `i ≤ d`, `j ≤ r`.
3. For `α = (a_j) ∈ 𝔽₂^r` let `π(α) : G_δ^c ↠ G_d^c` send `x_{ij} ↦ x_i^{a_j}`.  The induced map
   `α̃` on `λ_c` depends only on `α`, and each coordinate of `a ↦ Σ_j a_j α̃(θ_{ij})` is a
   polynomial in `a` of degree `≤ c + 1` **with zero constant term**.
4. Choose `r > (c+1)·d·dim λ_c(G_d^c)`.  **Chevalley–Warning** (`Mathlib/FieldTheory/
   ChevalleyWarning.lean`) then produces a *nontrivial* common zero `α`, and the corresponding
   subfield `E(α)`, of group `G_d^c`, has all its block obstructions zero.
5. Proposition 4.2 now applies and produces a strong Scholz field with group `G_d^c`; every
   `2`-group of rank `d` and `2`-class `c` is a quotient of it, and normal subfields of Scholz
   fields are Scholz.

No Poitou–Tate, no Grunwald–Wang, no Kronecker–Weber: the arithmetic inputs are Chebotarev,
quadratic reciprocity, Hecke's ramification criterion for `K(√μ)`, Brauer–Hasse–Noether (already
used by Proposition 2.1) and Chevalley–Warning.

### What that costs here, and the two simplifications worth taking

Schmid's Proposition 3.1 (the Lie-module decomposition `Z(G_d^c) = ⨁_{ν=1}^c L_d^ν` with
`dim L_d^ν = (1/ν) Σ_{k∣ν} μ(k) d^{ν/k}`) is the deepest algebraic input, and it is quoted from a
separate paper.  Two observations remove most of it:

* **Only a degree bound is needed, not the grading.**  Chevalley–Warning needs `Σ deg < #vars` and a
  known zero; `a = 0` is a zero because `π(0)` is the trivial map.  Homogeneity is never used.  So
  `deg ≤ c + 1` suffices and the exact dimensions `ℓ_d^ν` are irrelevant — any finite bound on
  `dim λ_c(G_d^c)` will do.
* **`λ_c` may replace `Z`.**  Schmid works with `Z(G_d^c)`, which equals `λ_c(G_d^c)` by his
  Proposition 3.1; but every use is of the kernel of `G_d^c ↠ G_d^{c−1}`, which *is* `λ_c` by
  definition.

What is genuinely required from the group-theory side is then:

* `lowerPCentralSeries`: `λ_1 = ⊤`, `λ_{n+1} = ⁅λ_n, ⊤⁆ ⊔ (λ_n)^p`; normality, `λ_n/λ_{n+1}`
  central and elementary abelian, surjective functoriality, and `λ_{c+1} = ⊥` for some `c` for every
  finite `p`-group;
* the disposition group `G_d^c = F_d/λ_{c+1}(F_d)`: finite, rank `≤ d`, `2`-class `≤ c`, and
  universal for those two invariants;
* `λ_c(G_d^c)` is generated by the images of `[x_{i_1}, …, x_{i_ν}]^{2^{c−ν}}`, `ν ≤ c` — the
  spanning half of Proposition 3.1 (its direct-sum half is what we drop);
* consequently: the induced map on `λ_c` depends only on `α` mod `Φ`, and is polynomial of degree
  `≤ c` in `a`.

and from the arithmetic side, Proposition 4.2 itself: Hecke's criterion, the factorisation
`(μ) = 𝔟²·𝔇·(e)`, the Shafarevich symbol `{μ/q}` and its Legendre-symbol comparison, and the
Chebotarev choice of `p_χ`.  That is a workstream of the same order as the whole odd-`ℓ`
`ResidueSpan`/`AuxPrimeChoice`/`ResidueCorrection` stack, plus a new free-group layer.

**So the `ℓ = 2` wall is no longer unmapped — it is a finite, elementary, and large plan.**

---

## 0.23 The `ℓ = 2` plan, checked line by line against Schmid's text

§0.22 was written from the abstract and the section headings.  The full text has since been read
(`pdftotext -layout` of the open-access PDF), and three of its details change the shape of the
formalization enough to be worth recording.

### Proposition 4.2 is itself an induction with kernels of order two

Its statement is

> Let `θ_i = Σ_{q ∈ Ram(P_i)} θ_q`, and assume `θ_i = 0` for all `i = 1,…,d`.  Then there exist
> infinitely many pairwise disjoint `t`-sets `{p_1,…,p_t}` of rational primes such that
> `Ê = ∏_{ν=1}^t K(√(p_ν e_ν))` is a strong Scholz field with respect to `N` admitting `G_d^c` as
> Galois group over `ℚ` and having `Ram(Ê) = Ram(K) ∪ {p_1,…,p_t}`,

and its proof runs over a basis `{χ_1,…,χ_t}` of `Hom(Z(H), 𝔽₂)`, one quadratic extension
`K_{ν−1} ↦ K_ν = K_{ν−1}(√(p_ν e_ν))` per basis vector.  **Each step has kernel of order two.**

That settles the question left open in §0.22: the repository does **not** need a residue correction
with elementary abelian kernel.  `Scholz/DyadicResidueCorrection.exists_scholz_solution_two`, whose
kernel hypothesis is `Nat.card ↥f.ker = 2`, *is* Schmid's inductive step; Proposition 4.2 is the
`t`-fold iteration of it.  The pairwise-quadratic-residue machinery is still wanted, but for the
base case (Lemmas 2.2/2.3), not for the correction.

The apparent tension — the base field changes at every one of the `t` steps, while the obstruction
`θ_q` was computed over the field at the bottom — is resolved by Schmid himself, twice:

* `R = R(χ)` is an invariant of the cohomology class, so `q ∈ R ⟺ q ∈ R_0`;
* "let `q ∈ Ram(P_i)` and let `q ∈ R_0`.  Using that `q` is busy in the Scholz field `K_0`, the
  restrictions to `E_χ` of `Φ_q` and of the Frobenius `θ_q` introduced above agree."

Business at `q` is exactly `IsSplitInertia`, which the repository already carries in `IsScholz`.

### The block structure survives the climb for free

`IsBlockSpanned` (`Scholz/DyadicSocle.lean`) is the repository's form of "the square classes of the
field are spanned by the block indicators".  `IsBlockSpanned.of_le_of_ker_le_frattini` transports it
up any Frattini subextension, and every step of the climb — central with kernel inside the Frattini
subgroup — is one.  So the blocks never grow even though `Ram` does, and the defect vector `t` stays
indexed by `Ram(A)` of the field at the bottom.  This is what makes the hypothesis `hdefect` of
`exists_scholz_solution_two` stable along the induction.

### The group-theoretic layer is finished

`Solvable/DispositionShrink.lean` supplies all of §5:

* `FreePClass.genPair`, the generators `x_{ij}` of `G_{d·r}^c`;
* `FreePClass.collapse a`, Schmid's `π(α)`;
* `FreePClass.exists_ne_zero_forall_prod_eq_one`, the Chevalley–Warning conclusion: for
  `r > d · charCount · (c+1)` there is `α ≠ 0` with all `d` block products trivial;
* `FreePClass.exists_rankMultiplier`, the choice of `r`.

Both simplifications promised in §0.22 were taken: `lowerPCentralSeries` replaces `Z(G_d^c)`, so
Schmid's Lemma 3.3 (transgression `Hom(Z(H),𝔽₂) ≅ H²(G,𝔽₂)`) and the direct-sum half of his
Proposition 3.1 are never needed.

### What remains, and in what order

| tag | content | status |
|---|---|---|
| F1 | Lemmas 2.2 + 2.3: a chain of primes each `≡ 1 mod 2^N` and mutually quadratic, and the multiquadratic strong Scholz field they cut out | ✅ `Scholz/StepRamification.lean` + `Scholz/MultiquadraticBase.lean` |
| F2 | `IsStrongScholz`: Scholz, plus pairwise disjoint blocks accounting for the square roots | ✅ `Scholz/StrongScholz.lean` |
| F3 | Proposition 2.1 at `p = 2` | ✅ `exists_galEquiv_ramifiedSet_subset_two` |
| F4 | the Scholz obstruction `θ_q` and its invariance under enlarging the base | partly in `FrobeniusDefect`; base-change half open |
| F5 | Proposition 4.2 as the `t`-fold iteration of the order-two step | single step ✅; iteration open |
| F6 | the shrinking: `E(α) = E_δ^{ker(collapse a)}`, `K(α) = E(α) ∩ K_δ`, `Ram(P_i(α)) = ⨆_{j : a_j = 1} Ram(P_{ij})`, and the transport of obstructions along `collapse a` | group half ✅; field half open |
| F7 | the induction on the `2`-class, `∀ G` a finite `2`-group, `∀ N`, `IsScholzRealizable G 2 N`, and the removal of the semiabelian-Sylow-`2` hypothesis from `InverseGalois/Shafarevich.lean` | ✅ skeleton: `Scholz/DyadicInduction.lean` reduces all of it to `IsDyadicClassStepSolvable` |

### The single remaining `ℓ = 2` wall

`InverseGalois.CFT.IsDyadicClassStepSolvable` (`Scholz/DyadicInduction.lean`) is now the *only*
open statement between the repository and the `2`-group case:

```lean
def IsDyadicClassStepSolvable : Prop :=
  ∀ (c d N : ℕ), (∀ δ M, IsStrongScholzRealizable δ c M) → IsStrongScholzRealizable d (c + 1) N
```

Granted it, `isInverseGalois_of_isDyadicClassStepSolvable` realises every finite `2`-group and
`isInverseGalois_of_isNilpotent_of_isDyadicClassStepSolvable` (`InverseGalois/Shafarevich.lean`)
realises every finite nilpotent group with no condition on the Sylow `2`-subgroup.  Its proof is
F4 + F5 + F6: apply `exists_galEquiv_ramifiedSet_subset_elemAbTwo` to
`FreePClass.proj 2 (d * r) c` over the rank-`d·r` realization, read off the block obstructions,
shrink along a Chevalley–Warning `α` from `FreePClass.exists_rankMultiplier`, and iterate
`exists_scholz_solution_two` once per basis vector of the kernel.

`PairwiseResidue.isSquare_natCast_swap` is the brick F1 was missing: `stepPrime` delivers
`(q_j / q) = 1` for the primes already chosen, and reciprocity turns that into `(q / q_j) = 1`
because `q_j ≡ 1 mod 4`.  Putting `ℚ(ζ_{q_j})` into the splitting field, as Schmid does, would give
the same thing at a much higher cost.

---

## 3. What is reachable *without* class field theory

This is the section that matters for this repository.

### 3.1 Ikeda's theorem: split embedding problems with abelian kernel over Hilbertian fields

> **Theorem (Ikeda).** *Let k be a Hilbertian field, L/k a finite Galois extension with group G,
> and A a finite abelian group with a G-action. Then the split embedding problem*
> ```
> G_k ↠ G,      1 → A → A ⋊ G → G → 1
> ```
> *has a proper solution: there is a Galois extension F/k containing L with
> Gal(F/k) ≅ A ⋊ G compatibly.*

References:
* M. D. Fried, M. Jarden, *Field Arithmetic*, 3rd ed., Springer 2008, **§16.4 "Split Embedding
  Problems with Abelian Kernels"** (p. 301), Proposition **16.4.5** (numbered 16.4.4 in some
  printings; §16.3, p. 297, is "Regular Realization of Finite Abelian Groups", and §16.4 is built
  directly on it).
* B. H. Matzat, *Einbettungsprobleme über Hilbertkörpern*, in *Konstruktive Galoistheorie*,
  LNM 1284 (1987), 215–268 (Folg. 1, p. 231).
* Malle–Matzat, *Inverse Galois Theory*, Chapter IV.
* Original: M. Ikeda, *Zur Existenz eigentlicher galoisscher Körper beim Einbettungsproblem für
  galoissche Algebren*, Abh. Math. Sem. Univ. Hamburg **24** (1960), 126–131.
* A modern refinement with local conditions: F. Legrand, *On finite embedding problems with
  abelian kernels*, J. Algebra **595** (2022), 633–659, <https://hal.science/hal-03517543>.

**Exactly what the proof needs.** The whole content is the wreath-product reduction:

1. *Group theory.* Let A₀ be A with its group structure but the G-action forgotten, and let
   Ind_1^G(A₀) = A₀^G be the induced module, so that A₀^G ⋊ G = A ≀ G is the **regular wreath
   product**. The augmentation-type map A₀^G → A, (a_g) ↦ ∏_g g·a_g, is G-equivariant and
   surjective, hence **A ⋊ G is a quotient of A ≀ G**, compatibly over G. So it suffices to solve
   the embedding problem for the wreath product; realizability is closed under quotients, which
   this repository has (`IsInverseGalois.quotient`).
2. *A regular abelian realization over the base.* One needs: for a field k (char 0 suffices) and
   a finite abelian A, **a regular Galois extension of k(t) with group A** — Fried–Jarden §16.3.
   This is where "does it need a regular abelian extension of N(T) for a number field N?" is
   answered: **yes, over the base field k, not merely over ℚ**. For the Ikeda step over ℚ with
   L/ℚ of group G, the construction is carried out over ℚ (or over L) and then descended.
3. *Independent variables + linear disjointness.* Take |G| independent variables (t_g)_{g∈G} with
   G permuting them, and in each variable an A-extension; the compositum has group A^G ⋊ G over
   k(t_g : g). Linear disjointness of the |G| conjugate A-extensions is what makes the group come
   out as the full wreath product; it is arranged by the independence of the variables (or,
   equivalently, by specializing to |G| "independent" values).
4. *Hilbert irreducibility over k.* Specialize the (t_g) to elements of k preserving the Galois
   group. **Hilbertianity of k is needed, not merely Hilbertianity of ℚ** — but for the concrete
   application to ℚ, ℚ is the base and ℚ's Hilbertianity is enough. A multivariable Hilbert
   irreducibility statement is required, though it reduces to the one-variable case by the
   standard reduction (Fried–Jarden §12.1 "Hilbert Sets and Reduction Lemmas").

**No class field theory, no Chebotarev, no Dirichlet, no Brauer groups, no Galois cohomology.**

**Sharpness.** "Split" cannot be dropped: over a field of characteristic ≠ 2, k(√a)/k embeds in a
cyclic degree-4 extension iff a is a sum of two squares in k (Serre, *Topics*, Thm 1.2.4 — cited
in this form by Schmidt–Wingberg §1). In particular ℚ(√−1) does not embed in a ℤ/4-extension of ℚ,
so the non-split embedding problem with kernel ℤ/2 over a Hilbertian field is not always solvable.

### 3.2 The wreath-product route and the class it reaches: semiabelian groups

> **Question.** If H is a Galois group over ℚ and A is finite abelian, is A ≀ H a Galois group
> over ℚ? **Yes** — it is the special case of Ikeda's theorem with the induced module as kernel,
> and it needs exactly items 2–4 above.

Iterating Ikeda and closing under quotients gives a precisely-defined class:

> **Definition (Matzat 1987; Dentzer 1995, Def. 2.1).** The class of **semiabelian** finite groups
> is the smallest non-empty class of finite groups that is closed under quotients and under
> semidirect products with finite abelian kernel (i.e. A ⋊ H is semiabelian whenever H is
> semiabelian and A is finite abelian with an H-action).

Equivalent forms and basic facts (see the Wikipedia entry *Semiabelian group* and the references
there; Dentzer, *On geometric embedding problems and semiabelian groups*, manuscripta math. **86**
(1995) 199–216; M. Stoll, *Construction of semiabelian Galois extensions*, Glasgow Math. J. **37**
(1995) 99–104; D. Neftin, *On semiabelian p-groups*, J. Algebra **344** (2011) 60–69):

* **Dentzer's criterion.** A non-trivial finite G is semiabelian iff there are an abelian normal
  subgroup A and a *proper* semiabelian subgroup H with G = A·H.
* Every semiabelian group is solvable; every abelian group is semiabelian.
* Closed under quotients; **not** closed under subgroups.
* Nilpotent groups of class 2 are semiabelian. A solvable group all of whose Sylow subgroups are
  abelian is semiabelian. An abelian extension of a cyclic group is semiabelian.
* Not every solvable group is semiabelian (Dentzer computes a table of small non-semiabelian
  groups). So this route does **not** give Shafarevich's theorem — it gives a large,
  cleanly-axiomatized proper subclass.

> **Theorem (Ikeda + induction).** *Every finite semiabelian group is a Galois group over every
> Hilbertian field of characteristic 0, in particular over ℚ.*

Moreover Dentzer's paper studies which semiabelian groups have **geometric** (= regular over
ℚ(t)) realizations, via *geometric* embedding problems — directly relevant to this repository's
`IsRegularInverseGalois`.

### 3.3 Noether's problem ⇒ regular realization

Wittenberg, *Park City lecture notes: around the inverse Galois problem*, arXiv:2302.13719,
§1.4–§1.6 (<https://arxiv.org/abs/2302.13719>):

* **Problem 1.9 (Noether).** For G ↪ S_n acting on 𝔸_k^n by permuting coordinates, is 𝔸_k^n/G
  rational over k?
* **Remark 2.2.** If k is infinite and perfect, a positive answer to Noether's problem for (k,G)
  implies a positive answer to the *regular* inverse Galois problem for (k,G) (Jouanolou,
  *Théorèmes de Bertini et applications*, Thm 6.3).

What is known for solvable G:
* **Fischer 1915** (Wittenberg Example 1.11): positive for all abelian G of exponent n over any
  field of characteristic ∤ n containing μ_n. Over ℚ this is useless for us, and in any case this
  repository already realizes every finite abelian group regularly over ℚ(T) by other means.
* **Swan 1969 / Voskresenskiĭ**: negative for ℤ/47ℤ over ℚ.
* **Lenstra 1974** (*Rational functions invariant under a finite abelian group*, Invent. Math.
  **25** (1974), 299–325, <https://eudml.org/doc/142292>): a complete criterion for all finite
  abelian G over all fields. Over ℚ, for cyclic groups (Wittenberg Thm 1.21, citing Lenstra
  [Len80, §3]): for G = ℤ/nℤ acting regularly on 𝔸_ℚ^n, TFAE:
  1. 𝔸_ℚ^n/G is rational;
  2. 𝔸_ℚ^n/G is stably rational;
  3. **8 ∤ n**, and for every prime p | n with s = v_p(n), the ring ℤ[ζ_{(p−1)p^{s−1}}] contains
     an element of norm p or −p.
  The smallest abelian counterexample is **ℤ/8ℤ** — the same 2-adic obstruction as the
  Grunwald–Wang special case (Wittenberg Prop. 1.20).
* **Plans 2017** (Wittenberg Thm 1.22): condition (3) is equivalent to
  n | 2²·3^m·5²·7²·11·13·17·19·23·29·31·37·41·43·61·67·71 for some m ≥ 0. In particular
  Noether's problem is **negative over ℚ for ℤ/pℤ for all but finitely many primes p** (the only
  known affirmative primes are p ≤ 43 together with 61, 67, 71).
* **Non-abelian, over ℂ**: Saltman 1984 and Bogomolov 1988 give counterexamples already over ℂ,
  by the unramified Brauer group ("Bogomolov's formula", Wittenberg Thm 1.23). These are
  p-groups. So Noether's problem is *hopeless* as a general route to solvable groups.

**Verdict: Noether's problem is a dead end for this project.** It fails for ℤ/8, fails for almost
all ℤ/p, and fails for non-abelian p-groups even over ℂ. It is worth knowing only to avoid
spending effort on it.

### 3.4 Other CFT-free theorems of the shape "normal series with factors of type X"

* **Semiabelian groups** (§3.2) — the main one, and the *only* clean "normal-series" class known
  to be realizable by purely Hilbertian methods.
* **Groups with a normal series whose factors are Sₙ / Aₙ / abelian split off**: nothing extra;
  closure of realizability under quotients and the Ikeda step already covers what is available.
* **GAR-realizations** (Malle–Matzat Ch. IV §3.1; Fried–Jarden §16.8): if every finite simple
  group had a GAR-realization over ℚ^ab, the Shafarevich Conjecture (that Gal(ℚ̄/ℚ^ab) is free
  profinite) would follow. This is a *different, much harder* programme; Harbater's survey
  (<https://www2.math.upenn.edu/~harbater/sc1.pdf>) is the reference. Not a route to solvable
  groups over ℚ.
* **Iwasawa's theorem** (NSW Ch. IX): Gal(k_solv/k^ab...) freeness statements — these are CFT-heavy.
* **Neukirch 1979** (*On solvable number fields*, Invent. Math. **53**): pro-solvable groups of
  finite exponent **prime to #μ(k)** with prescribed local behaviour. Scholz–Reichardt-flavoured,
  so still CFT.

---

## 4. Mathlib gap analysis

Roots: Mathlib at `/home/alex_harmonic_fun/InverseGaloisProblem/.lake/packages/mathlib/Mathlib`
(abbreviated `$M`); local project at `/home/alex_harmonic_fun/InverseGaloisProblem/InverseGalois`
(abbreviated `$L`).

### 4.1 Absent, and hard

| Ingredient | Status | Notes |
|---|---|---|
| **Chebotarev density theorem** | **ABSENT** | Zero occurrences of "chebotarev" anywhere in Mathlib. |
| **Dirichlet / natural density of sets of primes** | **ABSENT** | No `dirichletDensity`, `natDensity`, `upperDensity`. `$M/Combinatorics/Schnirelmann.lean` has `schnirelmannDensity`, the wrong notion. `$M/NumberTheory/PrimeCounting.lean` has `Nat.primeCounting` but no asymptotics; no PNT. |
| **Class field theory**: Artin reciprocity, Artin map, ray class groups/fields, Hilbert class field, idele class group | **ABSENT** | Only a comment at `$M/RingTheory/Valuation/Discrete/Basic.lean:61` pointing at the external `mariainesdff/LocalClassFieldTheory` repo. |
| **Kronecker–Weber** | **ABSENT** | Zero hits. |
| **Grunwald–Wang** | **ABSENT** | Zero hits, nothing adjacent (no Ш, no local–global for cyclic extensions). |
| **Poitou–Tate duality / local duality** | **ABSENT** | No profinite group cohomology at all. |
| **Hilbert symbols, power residue symbols, higher reciprocity** | **ABSENT** | Quadratic case is complete (§4.2), everything above degree 2 is missing. |
| **Brauer group** | **PARTIAL — a stub** | `$M/Algebra/BrauerGroup/Defs.lean` is 98 lines: `CSA`, `IsBrauerEquivalent`, `BrauerGroup K := Quotient …`. **There is no group structure on it.** No `Br(K) ≅ H²(Gal, K̄ˣ)`, no local invariants, no Albert–Brauer–Hasse–Noether. |
| **H² ↔ (central) group extensions** | **ABSENT, an explicit TODO** | `$M/GroupTheory/GroupExtension/Defs.lean:51` lists the bijection as future work; `$M/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean:50` lists it too. No `IsCentralExtension` anywhere. |
| **Chief series / elementary abelian factors / composition series of groups** | **ABSENT** | `$M/Order/JordanHolder.lean` has `CompositionSeries` but the only `JordanHolderLattice` instance is `Submodule R M` (`$M/RingTheory/SimpleModule/Basic.lean:544`); **there is no instance for `Subgroup G`**. No `chiefSeries`, no "elementary abelian". |
| **Embedding problems (any formalized notion), free profinite groups** | **ABSENT** | Local substitute: the whole `$L/Rigidity/RET/Pi1/` étale-π₁ development. |
| **Hilbert irreducibility** | **ABSENT in Mathlib** | See §4.3 — the local project has it. |
| **Noether's problem / rationality of fields / Lüroth** | **ABSENT in Mathlib** | No rationality predicate, no Lüroth. Raw material: `$M/FieldTheory/Fixed.lean` (Artin's theorem `finrank (FixedPoints.subfield G F) F = card G`). Local: `$L/Hilbert/Analytic/Luroth.lean`. |
| **Artin–Schreier** | **ABSENT in Mathlib / EXISTS locally** | `$L/Experimental/ArtinSchreier.lean` (`artinSchreier_irreducible`). |

### 4.2 Present and usable

| Ingredient | Status | Where |
|---|---|---|
| **Dirichlet's theorem on primes in AP** | **EXISTS, complete** | `$M/NumberTheory/LSeries/PrimesInAP.lean`: `Nat.infinite_setOf_prime_and_eq_mod` (:475), `Nat.forall_exists_prime_gt_and_eq_mod` (:487), `Nat.forall_exists_prime_gt_and_zmodEq` (:495), `Nat.frequently_atTop_prime_and_modEq` (:512). Supporting: `$M/NumberTheory/DirichletCharacter/*`, `$M/NumberTheory/LSeries/{Dirichlet,Nonvanishing}.lean`. |
| **Dedekind zeta + analytic class number formula** | **EXISTS** | `$M/NumberTheory/NumberField/DedekindZeta.lean`: `NumberField.dedekindZeta` (:47), `dedekindZeta_residue` (:54), `dedekindZeta_residue_pos` (:63), **`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` (:75)** — the simple pole at s = 1. *No Euler product yet.* |
| **Euler product machinery** | **EXISTS (ℕ-indexed)** | `$M/NumberTheory/EulerProduct/Basic.lean`: `eulerProduct` (:209), `ArithmeticFunction.IsMultiplicative.eulerProduct` (:252), `eulerProduct_completely_multiplicative` (:366). |
| **Legendre / Jacobi symbols, quadratic reciprocity** | **EXISTS, complete** | `$M/NumberTheory/LegendreSymbol/Basic.lean:108` `legendreSym` (root namespace, *not* `ZMod.legendreSym`); `.../QuadraticReciprocity.lean:107` `legendreSym.quadratic_reciprocity`; `.../JacobiSymbol.lean:86` `jacobiSym` with full reciprocity. |
| **Dedekind–Kummer factorization** | **EXISTS, two layers** | `$M/NumberTheory/KummerDedekind.lean:103` `KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk`; `$M/NumberTheory/NumberField/Ideal/KummerDedekind.lean:168` `primesOverSpanEquivMonicFactorsMod` with the ramification/inertia dictionary at :210–:252. Local: `$L/Polynomial/DedekindFacts.lean`, `DedekindProof.lean`. |
| **Frobenius element** | **EXISTS** | `$M/RingTheory/Frobenius.lean`: `AlgHom.IsArithFrobAt` (:54), `IsArithFrobAt` (:182), `arithFrobAt R G Q : G` (:253), `isConj_arithFrobAt` (:261) — *the Frobenius conjugacy class map Chebotarev would need*, `IsArithFrobAt.eq_of_isUnramifiedAt` (:163). |
| **Decomposition / inertia** | **PARTIAL, unnamed** | No `Ideal.decompositionGroup` — it is spelled `MulAction.stabilizer G Q`. `Ideal.inertia` at `$M/RingTheory/Ideal/Defs.lean:152` (very general abbrev); `ValuationSubring.{decomposition,inertia}Subgroup` at `$M/RingTheory/Valuation/RamificationGroup.lean:30,50`. Structure theory: `$M/RingTheory/Invariant/Basic.lean` `Ideal.Quotient.stabilizerQuotientInertiaEquiv` (:399) = D/I ≅ Gal(residue). Counting: `$M/NumberTheory/RamificationInertia/Galois.lean` (`ramificationIdxIn`, `inertiaDegIn`, `card_stabilizer_eq` = e·f at :337, fundamental identity at :237). `galRestrict` at `$M/RingTheory/IntegralClosure/IntegralRestrict.lean:178`. |
| **"Splits completely" / unramified** | **PARTIAL** | No named `totallySplit`/`splitsCompletely` predicate anywhere; must be spelled `(primesOver p B).ncard = finrank K L` or e = f = 1. `Algebra.IsUnramifiedAt` at `$M/RingTheory/Unramified/Locus.lean:45`; the bridge `Algebra.isUnramifiedAt_iff_of_isDedekindDomain` at `$M/NumberTheory/RamificationInertia/Unramified.lean:90`. |
| **Group cohomology H¹, H²** | **EXISTS, rich** | `$M/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`: `H1` (:927), `H2` (:1003), `cocycles₁/₂` (:266/:271), `IsMulCocycle₁/₂` (:611/:615). Also `Hilbert90.lean`, `LongExactSequence.lean`, `Shapiro.lean`, `FiniteCyclic.lean`. *Note the path is `RepresentationTheory/Homological/GroupCohomology/`, not `RepresentationTheory/GroupCohomology/`.* |
| **Hilbert 90** | **EXISTS** | `$M/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`: `isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units` (:84), `exists_div_of_norm_eq_one` (:132). |
| **Kummer theory** | **EXISTS, complete** | `$M/FieldTheory/KummerExtension.lean`: irreducibility of Xⁿ − C a (:130–:143), `autEquivZmod` (:411), `isCyclic_of_isSplittingField_X_pow_sub_C` (:431), converse `exists_root_adjoin_eq_top_of_isCyclic` (:464), `isCyclic_tfae` (:542). |
| **`RegularWreathProduct`** | **EXISTS** | `$M/GroupTheory/RegularWreathProduct.lean:45` `structure RegularWreathProduct D Q`, notation `D ≀ᵣ Q` (:51), `Group` instance (:84), `IteratedWreathProduct`, `Sylow.mulEquivIteratedWreathProduct`. **Only the regular wreath product** — no `G ≀_X H` for a general action, and no twisted wreath product. |
| **`SemidirectProduct`** | **EXISTS, full API** | `$M/GroupTheory/SemidirectProduct.lean`, `N ⋊[φ] G`. |
| **Group extensions** | **EXISTS (defs only)** | `$M/GroupTheory/GroupExtension/Defs.lean:74` `structure GroupExtension N E G`, `.Splitting` (:271); `$M/GroupTheory/GroupExtension/Basic.lean:152,178` `semidirectProductToGroupExtensionEquiv`, `semidirectProductMulEquiv` (split ⟹ semidirect). No H² classification, no obstruction theory. |
| **Solvable / nilpotent** | **PARTIAL** | `$M/GroupTheory/Solvable.lean:104` `class IsSolvable` (= derived series terminates) with sub/quotient/product closure (:138–:152); `$M/GroupTheory/Nilpotent.lean:184` `Group.IsNilpotent`. Adjacent: `$M/GroupTheory/{Frattini,SchurZassenhaus,Sylow,PGroup,Transfer,Goursat}.lean`, `$M/GroupTheory/IsSubnormal.lean` (`exists_normal_and_le_and_lt_top_of_ne` :145). **Fitting subgroup: check — not found under that name.** |
| **Chevalley–Warning** | **EXISTS** | `$M/FieldTheory/ChevalleyWarning.lean`. |
| **Class group, adeles** | **EXISTS (thin)** | `$M/RingTheory/ClassGroup.lean:86` `ClassGroup`, finiteness in `$M/NumberTheory/ClassNumber/*`; `$M/NumberTheory/NumberField/AdeleRing.lean:47` `AdeleRing`. **No idele group, no idele class group, no norm/Artin map.** |

### 4.3 The local project's own assets

* **Hilbert irreducibility.** `$L/Hilbert/HilbertIrreducibility.lean` (592 lines):
  `hilbert_irreducibility_monic` (:255), `hilbert_irreducibility_theorem` (:423) — for
  `f : Polynomial (Polynomial ℚ)`, infinitely many **integer** specializations preserving
  irreducibility; `reducibleLocus` (:471), `reducibleLocus_not_univ` (:477). Support:
  `$L/NumberTheory/IntegerPointsSublinear.lean`, `$L/NumberTheory/PrimeLowerBound.lean`
  (elementary π(n) lower bounds — the same technique Serre's Lemma 2.1.4 needs).
  Downstream seam: `$L/Hilbert/RegularExtension.lean:136` `IsInverseGalois.of_regular_family`.
* **Realizability predicates.**
  `$L/Core/Basic.lean:29` `IsInverseGalois G`, with `of_mulEquiv`, `of_surjective`, `quotient`.
  `$L/Rigidity/RET/Statement.lean:66,81,91` `IsRegularGaloisGroupOverBase k F G`,
  `IsRegularGaloisGroupOver K G`, `IsRegularInverseGalois G`.
* **The bridge.** `$L/Rigidity/RET/Specialization.lean:1107`
  `IsRegularInverseGalois.isInverseGalois : IsRegularInverseGalois G → IsInverseGalois G`.
* **Abelian.** `$L/Rigidity/RET/AbelFinale.lean:73`
  `Rigidity.RET.IsRegularInverseGalois.of_commGroup (A) [CommGroup A] [Finite A] :
  IsRegularInverseGalois A`. **Currently hard-wired to base field ℚ** — the multi-radical tower
  in `$L/Rigidity/RET/AbelRegular.lean` is built over `FF = ℚ(T)`. The *geometric* layer below it
  is already parameterized by an arbitrary base field k
  (`$L/Rigidity/RET/ExistenceAbelian.lean:88 exists_cover_of_commGroup`,
  `$L/Rigidity/RET/DeckGroups.lean:93 isDeckGroupOver_of_commGroup`).
* **Rigidity + descent.** `$L/Rigidity/Rigidity.lean:49 rigidity_realizable`;
  `$L/Rigidity/RigidData.lean` (`RigidData`, `StableRigidData`, `RigidityCertificateH`);
  `$L/Rigidity/RET/Descent/` (`exists_regular_numberField_of_orbitRigid`, `Index2`).
* **Catalogue.** `$L/Catalogue.lean` is the index of everything realized.

---

## 5. Recommended roadmap

### 5.0 The strategic conclusion first

*(Read §0 first: the group-theoretic scaffolding this section prices as expensive turned out to be
cheap and is now formalized. The verdicts below concern the arithmetic, and they stand.)*

There are two candidate routes and they are **not** equally good.

**Route A (classical / arithmetic): Scholz–Reichardt, then Shafarevich.** Requires
Brauer–Hasse–Noether, Kronecker–Weber (or full CFT), Grunwald–Wang, Poitou–Tate. Every one of
these is absent from Mathlib and each is, by itself, a multi-year formalization. Mathlib does not
even have a *density* of a set of primes. **Do not start here.**

**Route B (Hilbertian / geometric): Ikeda ⇒ semiabelian groups.** Requires exactly two things,
both of which this repository already has in usable form: (i) regular realizations of finite
abelian groups over a base field, and (ii) Hilbert irreducibility over ℚ. It reaches a large,
crisply-defined subclass of the solvable groups (all nilpotent of class 2, all solvable with
abelian Sylows, all abelian-by-cyclic, all iterated wreath products, closed under quotients).
**Start here.** It is also the route that composes with everything already in the Catalogue: for
any H already realized (Sₙ, Aₙ, dihedral, PGL₂(𝔽_p), Mathieu…), Ikeda immediately yields A ⋊ H
and A ≀ H for every finite abelian A with an H-action.

The honest headline: **Shafarevich's theorem itself is a multi-year, probably multi-person
project that is gated on class field theory in Mathlib, and should not be attempted directly.
Semiabelian groups are a genuine, publishable, achievable target that captures a large slice of
the solvable world.**

Effort units below: **S** ≈ days, **M** ≈ 1–3 weeks, **L** ≈ 1–3 months, **XL** ≈ 6–18 months,
**XXL** ≈ multi-year.

### Milestone 1 — Regular abelian realization over an arbitrary number field. **[M–L]**

Generalize `Rigidity.RET.IsRegularInverseGalois.of_commGroup` from ℚ to an arbitrary base field
k of characteristic 0 (at minimum, an arbitrary number field N):

```
IsRegularGaloisGroupOver N A     for every number field N and finite abelian A
```

The geometric layer (`ExistenceAbelian`, `DeckGroups`, `KummerAbelian`) is already
base-parameterized; the work is in the arithmetic layer `AbelRegular.lean`, where `FF = ℚ(T)`,
`EE n`, `GG n`, `KK n` are all built over ℚ. The obstacle is the μ_n-descent bookkeeping
(the `Φ`-exponent twisted-Kummer recipe) over a base that may already contain roots of unity.

*Value:* prerequisite for everything downstream, and independently strengthens the Catalogue.
*Risk:* low. This is engineering, not mathematics.

### Milestone 2 — The regular wreath-product construction. **[L]**

Given a finite group H with `IsRegularGaloisGroupOver k H` (or just a Galois L/k with group H)
and a finite abelian A, build a regular Galois extension of k(t_h : h ∈ H) with group A ≀ᵣ H,
using `RegularWreathProduct` (`$M/GroupTheory/RegularWreathProduct.lean`).

Sub-tasks:
* (2a) **[S]** The group-theoretic surjection `A ≀ᵣ H ↠ A ⋊[φ] H` for any H-action φ on A, over H.
  Pure Mathlib group theory; combines `RegularWreathProduct` and `SemidirectProduct`.
* (2b) **[M]** Linear disjointness of the |H| conjugate A-extensions in independent variables;
  the deck group of the compositum is the wreath product. The repo already has the compositum /
  product machinery: `$L/Rigidity/RET/{Product,ProductTranslate,ProductGeometric}.lean`
  (`IsAffineDeckGroup.prod`, `IsGeometricGaloisCover.prod`). This is the closest existing analogue
  and should be reusable — beware, `Product.lean` is the repo's most expensive file.
* (2c) **[M]** Descent of the compositum to k(t_h) with the H-permutation action on the variables.

*Value:* high — this is the whole engine.
*Risk:* medium. The linear-disjointness bookkeeping is where these proofs always bloat.

### Milestone 3 — Multivariable Hilbert irreducibility over ℚ. **[M]**

`$L/Hilbert/HilbertIrreducibility.lean` gives the one-variable statement with integer
specializations. Ikeda needs |H| variables. The standard reduction (Fried–Jarden §12.1) is:
specialize one variable at a time, keeping the others generic. Formalizing "ℚ(t₂,…,t_n) is
Hilbertian because ℚ is" in the generality of Fried–Jarden Ch. 13 is **[L]**; formalizing only
the *concrete* iterated specialization needed for the wreath product is **[M]**.

*Value:* high; also unblocks other multivariable constructions.
*Risk:* medium — the interaction between the existing `specialize`/`reducibleLocus` API and a
tower of specializations may need the whole file re-architected.

### Milestone 4 — Ikeda's theorem. **[M, given 1–3]**

```
theorem ikeda (k Hilbertian, char 0) (L/k Galois with group H) (A finite abelian, H-action) :
  ∃ F/k Galois, Gal(F/k) ≃* A ⋊[φ] H,  compatibly with L
```
Assemble: Milestone 2 gives A ≀ᵣ H regularly over k(t_h); Milestone 3 specializes; (2a) plus
`IsInverseGalois.quotient` cuts down to A ⋊ H. State it in the repo's `IsInverseGalois` /
`IsRegularGaloisGroupOverBase` vocabulary so it plugs into the Catalogue.

*Value:* **highest value/effort ratio in this document.**

### Milestone 5 — Semiabelian groups. **[M, given 4]**

* (5a) **[S]** Define `IsSemiabelian : Type* → Prop` inductively (Dentzer Def. 2.1: closed under
  quotients and A ⋊ H).
* (5b) **[S–M]** `IsSemiabelian G → IsInverseGalois G` by induction, using Milestone 4 and
  `IsInverseGalois.quotient`.
* (5c) **[M]** Concrete corollaries worth stating in `Catalogue.lean`: every finite nilpotent
  group of class ≤ 2 is semiabelian; every finite solvable group with abelian Sylow subgroups is
  semiabelian; every iterated wreath product of abelian groups. Each needs the corresponding
  group-theoretic lemma, none of which is in Mathlib.

*Value:* this is the deliverable. It is the largest new family of solvable groups over ℚ that is
reachable at all with current Mathlib.

### Milestone 6 (optional, high value elsewhere) — Split-density of primes. **[M–L]** — **DONE**, see §0

Prove: *for K/ℚ Galois of degree n, the set of rational primes splitting completely in K has
Dirichlet density 1/n; in particular, for A ⊊ B with B/ℚ Galois, infinitely many primes split
completely in A but not in B* (statement (★) of §1.5).

Path: (6a) prove `n ↦ #{I ⊴ 𝒪_K : absNorm I = n}` is multiplicative, apply
`ArithmeticFunction.IsMultiplicative.eulerProduct` to get the Euler product for
`NumberField.dedekindZeta`; (6b) combine with
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` to get
`Σ_{q split in K} q^{-s} ~ (1/n) log(1/(s-1))`; (6c) conclude.

*Value:* this is the **only** ingredient of Chebotarev that Scholz–Reichardt actually needs, it is
the natural first step toward a real Chebotarev in Mathlib, and it would be a genuine Mathlib
contribution independent of this project. It also subsumes Serre's Lemma 2.1.4 (existence of
completely split primes) as a corollary.
*Risk:* low-to-medium; the analytic scaffolding is all present.

### Milestone 7 — Serre's Lemma 2.1.4, elementary version. **[S–M]** — **DONE**, see §0

*"For a finite extension E/ℚ there are infinitely many primes splitting completely in E,"* by
Serre's counting argument (values of f, smooth-number counting). Independent of Milestone 6 and
much cheaper. Uses the same style of estimate as `$L/NumberTheory/PrimeLowerBound.lean`.

*Value:* moderate on its own; it is the split case of Scholz–Reichardt (item 1 of §1.4) and a
useful standalone lemma.

### Milestone 8 — Kronecker–Weber. **[XL]**

Needed for Serre's Lemma 2.1.6 (item 5 of §1.4), i.e. for *any* progress on the non-split case of
Scholz–Reichardt. Absent from Mathlib. There is a known Lean-community interest in this but no
landed formalization. **6–18 months.** Consider only as a Mathlib contribution in its own right,
not as a step in this project.

### Milestone 9 — Brauer group with its group law, local invariants, and Albert–Brauer–Hasse–Noether. **[XXL]**

Needed for Serre's Lemma 2.1.5 (item 2 of §1.4). Mathlib's `BrauerGroup` is a bare quotient type
with **no multiplication**. To get to ABHN one needs: the group law, `Br(K) ≅ H²(Gal, K̄ˣ)`
(which needs the H²-↔-crossed-product dictionary, itself absent), `Br(ℚ_p) ≅ ℚ/ℤ` (local CFT), and
the global exact sequence (global CFT). **Multi-year.**

**Update (2026-08-21): the first two are done**, see §0.1 — the group law, Skolem–Noether, the
double centralizer theorem, Wedderburn in the split case, Galois descent, the crossed product, and
`Br(L/K) ≅ H²(Gal(L/K), Lˣ)` for every finite Galois `L/K`, together with the cyclic case
`Br(L/K) ≅ Kˣ/N(Lˣ)` and `Br(ℂ/ℝ) ≅ ℤ/2`. What remains of this milestone is exactly the arithmetic:
`Br(ℚ_p) ≅ ℚ/ℤ` and the global exact sequence. Note that Mathlib cannot yet even state the first —
`IsNonarchimedeanLocalField` has no instances, so `ℚ_[p]` must first be equipped with
`ValuativeRel`, `IsValuativeTopology` and `LocallyCompactSpace`.

### Milestone 10 — Scholz–Reichardt. **[XXL, gated on 8 and 9]**

Only meaningful after 6/7 + 8 + 9. Then the remaining work (the (S_N) induction, the linear
disjointness Lemma 2.1.9, the local liftability analysis, the character-correction bookkeeping) is
itself an **[L]**–**[XL]** project. Realistically 2+ years from today.

### Milestone 11 — Shafarevich. **[XXL, gated on 10 + Grunwald–Wang + Poitou–Tate]**

Adds Grunwald–Wang (**[XXL]**, needs CFT), Poitou–Tate duality (**[XXL]**, needs profinite group
cohomology which Mathlib entirely lacks), the (i,j)-filtration and shrinking machinery
(**[L]**, mostly elementary — Chevalley–Warning is already in Mathlib), and the Frattini/Fitting
reduction (**[M]**; the Fitting subgroup does not appear to exist in Mathlib and would need
defining). **Not attemptable this decade without a Mathlib class field theory project.**

### Recommended ordering

```
1 → 2 → 3 → 4 → 5        (the deliverable: semiabelian groups over ℚ)
        ⌐ 7              (cheap, independent, useful)
        ⌐ 6              (Mathlib contribution; the only Chebotarev SR needs)
                8, 9, 10, 11   ← do not start
```

Realistic total for Milestones 1–5: **3–6 months** of concentrated work, with Milestone 2 the
likely bottleneck. Milestones 6–7 add **1 month** and are separable.

### A warning about the regular route

Serre's Remark 4 after Theorem 2.1.1 is worth repeating: **it is not known whether an arbitrary
ℓ-group is the Galois group of a regular extension of ℚ(T).** So the repository's
`IsRegularInverseGalois` predicate — the backbone of everything in `Catalogue.lean` — *cannot*
be the target for solvable groups; there is no theorem to formalize. Ikeda's theorem lands in
`IsInverseGalois`, not `IsRegularInverseGalois`, and the wreath-product construction of
Milestone 2 is regular only over the multivariable base k(t_h : h ∈ H), not over k(T). Any
milestone plan that tries to route solvable groups through `IsRegularInverseGalois` is attempting
an open problem. (Dentzer's paper studies exactly which semiabelian groups *do* have geometric
realizations — that is the correct reference if a regular statement is ever wanted.)

---

## Sources

* J.-P. Serre, *Topics in Galois Theory*, Harvard 1988, notes by H. Darmon —
  <https://www.ms.uky.edu/~sohum/ma561/notes/workspace/books/serre_galois_theory.pdf>
  (§2.1 Thm 2.1.1, Def. 2.1.2, Thm 2.1.3, Lemmas 2.1.4–2.1.9, Thm 2.1.11).
* A. Schmidt, K. Wingberg, *Šafarevič's theorem on solvable groups as Galois groups* —
  <https://arxiv.org/abs/math/9809211> (Thms 1, 13, 14, 15; Props 2, 11, 16, 17).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren 323,
  Ch. IX §6 — <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>.
* G. Malle, B. H. Matzat, *Inverse Galois Theory*, Springer Monographs in Mathematics, 1999,
  Ch. IV "Embedding Problems" — <https://link.springer.com/chapter/10.1007/978-3-662-12123-8_4>.
* M. D. Fried, M. Jarden, *Field Arithmetic*, 3rd ed., Springer 2008, §§12.1, 13.7, 16.3, 16.4,
  16.8 — <https://link.springer.com/book/10.1007/978-3-540-77270-5>.
* O. Wittenberg, *Park City lecture notes: around the inverse Galois problem*, arXiv:2302.13719 —
  <https://arxiv.org/abs/2302.13719> (Problems 1.1, 1.9, 2.1; Examples 1.10–1.12; Thms 1.21, 1.22,
  1.23; Remark 2.2).
* H. W. Lenstra, Jr., *Rational functions invariant under a finite abelian group*, Invent. Math.
  **25** (1974), 299–325 — <https://eudml.org/doc/142292>.
* R. Dentzer, *On geometric embedding problems and semiabelian groups*, manuscripta math. **86**
  (1995), 199–216 — <https://link.springer.com/article/10.1007/BF02567989>.
* F. Legrand, *On finite embedding problems with abelian kernels*, J. Algebra **595** (2022),
  633–659 — <https://hal.science/hal-03517543v1>.
* P. Schmid, *Realizing 2-groups as Galois groups following Shafarevich and Serre*,
  Algebra & Number Theory **12** (2018), 2387–2401 — <https://projecteuclid.org/euclid.ant/1550113226>.
* D. Harbater, *The Shafarevich Conjecture in inverse Galois theory* —
  <https://www2.math.upenn.edu/~harbater/sc1.pdf>.
* Wikipedia, *Shafarevich's theorem on solvable Galois groups* —
  <https://en.wikipedia.org/wiki/Shafarevich%27s_theorem_on_solvable_Galois_groups>;
  *Semiabelian group* — <https://en.wikipedia.org/wiki/Semiabelian_group>.
