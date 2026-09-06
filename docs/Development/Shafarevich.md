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
   input.  *(Superseded in part by §0.24: the power-class form of Grunwald–Wang, squarefree
   exponent, is now in the repo; the character form and Poitou–Tate are not.)*

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
| F4 | the Scholz obstruction `θ_q` and its invariance under enlarging the base | ✅ `Scholz/CanonicalDefect.lean` + `Scholz/BlockDefect.lean` + `Scholz/CoverInertia.lean` + `Scholz/CentralDefect.lean` + `Scholz/CoverObstruction.lean` |
| F5 | Proposition 4.2 as the `t`-fold iteration of the order-two step | ✅ `Scholz/DyadicStage.lean` (`ClimbStage`, `nonempty_realization`) |
| F6 | the shrinking: `E(α) = E_δ^{ker(collapse a)}`, `K(α) = E(α) ∩ K_δ`, `Ram(P_i(α)) = ⨆_{j : a_j = 1} Ram(P_{ij})`, and the transport of obstructions along `collapse a` | ✅ `Solvable/DispositionShrink.lean` + `Scholz/DyadicShrink.lean` + `Scholz/ClassStepData.lean` |
| F7 | the induction on the `2`-class, `∀ G` a finite `2`-group, `∀ N`, `IsScholzRealizable G 2 N`, and the removal of the semiabelian-Sylow-`2` hypothesis from `InverseGalois/Shafarevich.lean` | ✅ `Scholz/DyadicInduction.lean` + `Scholz/DyadicInitialStage.lean` |

### The `ℓ = 2` wall is closed

`InverseGalois.CFT.isDyadicClassStepSolvable` (`Scholz/DyadicInitialStage.lean`) is a theorem:

```lean
def IsDyadicClassStepSolvable : Prop :=
  ∀ (c d N : ℕ), 1 ≤ c → (∀ δ M, IsStrongScholzRealizable δ c M) →
    IsStrongScholzRealizable d (c + 1) N

theorem isDyadicClassStepSolvable : IsDyadicClassStepSolvable
```

so `InverseGalois.isInverseGalois_of_isPGroup_two` realises every finite `2`-group and
`IsInverseGalois.of_isNilpotent` (`InverseGalois/Shafarevich.lean`) realises every finite nilpotent
group with no condition on the Sylow `2`-subgroup.  Both depend on `propext`, `Classical.choice`
and `Quot.sound` only.

The proof is F4 + F5 + F6 assembled as follows.  `StrongScholzRealization.exists_centralPart`
(`Scholz/CoverObstruction.lean`) reads, for each prime `q` of each block, a pair `(x, θ)` in
`G_{d·r}^{c+1}` — a generator of the inertia subgroup at `q` and the central part of an arithmetic
Frobenius above it — such that for *every* normal `W`, the obstruction of `q` in the subfield `W`
cuts out vanishes exactly when `θ ∈ ⟨x⟩ ⊔ W`.  The `θ`'s of a row multiply to one element per copy,
`FreePClass.exists_rankMultiplier` supplies a Chevalley–Warning `α` killing the collapse of the
selected products, and `ClassStepData.shrink α` merges the copies.  For the shrunken data the same
reading holds through `V ↦ (collapse α)⁻¹(V)` (`cutField_comap_comp`, `mem_sup_comap_iff`), and
`FreePClass.zpowers_inf_ker_proj` cuts the collapsed inertia subgroup down to `⟨z_i⟩`: a hyperplane
missing `z_i` joins it to the whole kernel, so nothing is obstructed, and a hyperplane containing
`z_i` reads the obstruction of the row as the character of the collapsed product, which `α` made
trivial.  That is exactly the `defect` field of `ClimbStage`, and `ClimbStage.nonempty_realization`
iterates `exists_scholz_solution_two` once per basis vector of the kernel.

`PairwiseResidue.isSquare_natCast_swap` is the brick F1 was missing: `stepPrime` delivers
`(q_j / q) = 1` for the primes already chosen, and reciprocity turns that into `(q / q_j) = 1`
because `q_j ≡ 1 mod 4`.  Putting `ℚ(ζ_{q_j})` into the splitting field, as Schmid does, would give
the same thing at a much higher cost.

---

## 0.24 Status (2026-08-28) — **Grunwald–Wang is landed** for a squarefree exponent

`InverseGalois/CFT/GrunwaldWang.lean`, sorry-free and axiom-free (`#print axioms` gives
`[propext, Classical.choice, Quot.sound]` on all seven results). §4's gap table listed
Grunwald–Wang as **ABSENT** with "zero hits, nothing adjacent"; that row is now out of date.

### What is proved

Let `K` be a number field, `n` an exponent, `S` a finite set of finite places.

| statement | name |
|---|---|
| prescribed classes mod `n`-th powers at finitely many finite places are matched by some `b ∈ Kˣ` | `exists_ne_zero_forall_pow_mul_eq_adicCompletion` |
| … by a `b` that is *not* a global `n`-th power, one prescribed class being no local one | `exists_ne_zero_not_exists_pow_eq_forall_pow_mul_eq_adicCompletion` |
| a radical extension whose radicand is a local `p`-th power outside `S` is trivial | `subsingleton_gal_of_forall_localPow_outside` |
| **Wang, prime exponent, `ζ_p ∈ K`** | `exists_pow_eq_of_forall_localPow_outside` |
| **Wang, prime exponent, arbitrary `K`** | `exists_pow_eq_of_forall_localPow_outside_of_prime` |
| **Grunwald–Wang, `n` squarefree** | `exists_pow_eq_of_forall_localPow_outside_of_squarefree` |
| the same as a Hasse principle, both directions | `exists_pow_eq_iff_forall_localPow_outside_of_squarefree` |

```lean
theorem exists_pow_eq_iff_forall_localPow_outside_of_squarefree {n : ℕ} (hn : Squarefree n)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) {b : K} :
    (∃ y : K, y ^ n = b) ↔ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∃ c : v.adicCompletion K, c ^ n = algebraMap K (v.adicCompletion K) b
```

### How it dodges the existence theorem

The surjectivity half was already here (`Approximation/PowClass.lean`, weak approximation). The
content is Wang's theorem, and the route uses **only the first inequality**, never reciprocity,
never the Artin map, never the existence theorem:

1. *Prime `p`, with `ζ_p ∈ K`.* If `b` is not a `p`-th power, `X^p − b` is irreducible, its
   splitting field is cyclic of degree `p` and generated by a radical `β`. `Kummer/LocalPower.lean`
   says the decomposition group at a place fixes `β` exactly when the radicand is a local `p`-th
   power there. So the hypothesis makes every place outside a finite set split completely, and
   `Units/SplitOutside.lean` — a solvable extension in which almost every place splits completely
   is trivial, which rests on the first inequality alone — forces `p = 1`.
2. *Removing `ζ_p`.* `K(ζ_p)/K` has degree `d` prime to `p`; transport the local hypothesis up
   (`Units/PlaceComap.lean`), get `y` with `y^p = b` upstairs, take norms to get `N(y)^p = b^d`,
   and read `ud + vp = 1` to get a `p`-th root in `Kˣ`.
3. *Squarefree `n`.* Each prime factor `q ∣ n` inherits the local hypothesis from `c^n =
   (c^{n/q})^q`, and roots of coprime exponents combine by Bezout.

**No case is lost to squarefreeness.** Wang's counterexample — `16` is an `8`-th power in almost
every completion of `ℚ` but not in `ℚ` — needs `8 ∣ n`, and `8 ∣ n` is incompatible with `n`
squarefree; `K` is `s`-special only for `s ≥ 3`, since `K(ζ_4)/K` is always cyclic. §2.5's
description of the obstruction is thereby confirmed from the formal side.

### What this does *not* yet unlock

Honest accounting against §2.4. The Shafarevich application needs

```
H¹(k, A) → ∏_{i=1}^r H¹(k_{𝔭_i}, A)
```

surjective for a **trivial** module `A = 𝔽_p^m`. When `ζ_p ∈ k` that group *is* `k^×/(k^×)^p` and
this is exactly the file's prescription half; over a general base `H¹(k, ℤ/p) = Hom(G_k, ℤ/p)` is
the group of cyclic degree-`p` *characters*, and prescribing those locally is the character form of
Grunwald–Wang. Getting the character form from the power form over a general base is an eigenspace
descent through `k(ζ_p)` — plausible, not written. So:

* the **power-class** Grunwald–Wang for squarefree exponent: **done**;
* the **character** form over a base without `ζ_p`: **not done** (needs the descent, or the
  existence theorem);
* the **special case** (`8 ∣ n`): **not done**, and it is genuinely false without the extra
  hypotheses;
* **Poitou–Tate duality** and the **Ш¹ Hasse principle** of §2.4: **untouched**.

Grunwald–Wang was one of three arithmetic blockers for gap 2 (`ElementaryAbelianKernelEP`), not the
only one. The nilpotent case of Shafarevich (§0.21, §0.22) remains what is actually proved
end-to-end; nilpotent → solvable is still open here.

---

## 0.25 Status (2026-08-28, later) — Ikeda is a theorem, and the Schmidt–Wingberg tower, re-costed

Three things happened after §0.24: the split half of the reduction stopped being a hypothesis, the
Schmidt–Wingberg paper was read end to end, and two of its proof devices turned out to be avoidable.

### The reduction, as it now stands

| statement | status |
|---|---|
| `Shafarevich.cyclicWreathEP` | **theorem** (`Ikeda.lean`, `e81f957`, `ce5e2bb`) |
| `Shafarevich.primeWreathEP` | **theorem** |
| `Shafarevich.splitAbelianEP` — Ikeda | **theorem** |
| `Shafarevich.FrattiniKernelEP` | **the one remaining hypothesis** |

`Shafarevich.isInverseGalois_of_isSolvable_of_frattiniKernelEP` now realizes every finite solvable
group over `ℚ` from `FrattiniKernelEP` alone. Upstream of it the chain is Ore → `SplitNilpotentEP`
→ `SplitPrimePowerEP` → `AbelianKernelEP` → `ElementaryAbelianKernelEP` → `FrattiniKernelEP`.

`Shafarevich/Generic.lean` (`8ddc8d7`) adds the first piece of Schmidt–Wingberg's own reduction: the
relatively free operator group `Generic U n S = FreeGroup (Fin n × U) / ⋂ ker(f : · →* S)` with the
`U`-action induced by left translation on the second coordinate, together with

```lean
theorem splitPrimePowerEP_of_genericSplitEP (h : ∀ ℓ : ℕ, GenericSplitEP ℓ) : SplitPrimePowerEP
theorem genericSplitEP_of_splitPrimePowerEP (hℓ : ℓ.Prime) (h : SplitPrimePowerEP) : GenericSplitEP ℓ
```

so the split `p`-group case is *equivalent* to the case of a generic kernel. Forward: the orbit map
`Generic U (Nat.card P) P ↠ P` is `U`-equivariant and surjective, so `Generic ⋊ U ↠ P ⋊[φ] U`.
Backward: `Generic U n S` is itself a finite `ℓ`-group when `S` is.

### The Schmidt–Wingberg dependency map

Schmidt–Wingberg, *Extensions of profinite duality groups* (arXiv `math/9809211`), Theorem 14: every
split embedding problem with finite nilpotent kernel has a proper solution; Theorem 15 is the same
with Scholz conditions attached. The proof is an induction on a two-index filtration `τ = (i,j)`,
each step of which is a *central* embedding problem with elementary abelian kernel
`E(n,τ) = F(n)^{(τ)}/F(n)^{(τ+1)}`, and it has four steps:

1. local split embedding problems at `Ram ∪ S_p ∪ S_∞` — Prop 6 with `T = Ind_{G_𝔭}^G 𝔽_p`;
2. global solvability: the obstruction lives in `Ш²(k, E(n,τ))` and is killed by Prop 6 with
   `T = Hom(μ_p, ℤ/p)`, after a Claim that needs **Tate–Poitou** `Ш²(k,A) ≅ Ш¹(k,A′)^∨`;
3. properness and Scholz condition (i) — Neukirch's principal homogeneous space over
   `H¹(G_k, E(n,τ))`, Lemma 10's injection `coker ↪ Ш¹`, and Prop 7(i);
4. Scholz condition (ii) — Theorem 13 applied to `N_n`, plus Prop 7(ii).

Underneath sit the shrinking propositions: Prop 2 (Chevalley–Warning), Prop 5 (the surjection
`(P/P²)^{⊗j} ↠ P^{(τ)}/P^{(τ+1)}`), Prop 6 and Prop 7 (shrinking in cohomology).

### The induced-module shortcut does **not** work

It is tempting to hope that `E(n,τ)` is an *induced* `𝔽_p[G]`-module, since `F(n)/F(n)²` is
`𝔽_p[G]^n` and Brauer–Hasse–Noether — which this repository has — gives `Ш²(K, 𝔽_p) = 0`, hence
`Ш²(k, Ind_{1}^{G} 𝔽_p) = 0` by Shapiro; that would delete Tate–Poitou from step 2. It fails. The
graded layers of a free (restricted) Lie algebra on a free `𝔽_p[U]`-module are not free: from
`Λ²(A ⊕ B) = Λ²A ⊕ (A ⊗ B) ⊕ Λ²B` the cross term `A ⊗ B` is free, but `Λ²(𝔽_p[U])` is a sum of
modules induced from subgroups of order ≤ 2, and is not free as soon as `U` has an involution. So
`Ш²(k, E(n,τ))` need not vanish and **Tate–Poitou is genuinely required**.

The Hochschild–Serre route is no substitute either: `Ш²(k,A) ⊆ ker(H²(G_k,A) → H²(G_K,A))` does hold
(because `Ш²(K,𝔽_p) = Ш(Br K)[p] = 0`), but inflation only gives
`H²(G,A) → ker → H¹(G, H¹(G_K,A))`, not a surjection onto `Ш²`.

### Two devices that *can* be dropped

**(a) Tate cohomology and dimension shifting are not needed for Props 6 and 7.** Schmidt–Wingberg
prove Prop 6 for `Ĥ^k(G, E(m,τ) ⊗ T)` by shifting down to `k = −1`, where a class is represented by
a module element and Prop 2 applies directly. But the shrinking map `ψ_a` is `G`-equivariant, so it
acts on *cochains*, and a class dies as soon as one representing cochain is annihilated. For a
**finite** `G` a `k`-cochain is a family of `#G^k` module elements, so Prop 2 with `t·#G^k` targets
kills all of them at once — no complete resolution, no dimension shifting, no `Ĥ`. The two indices
actually used are `k = 2` (ordinary cohomology, `2`-cocycles) and `k = −2`, and for a finite group
`Ĥ^{−2}(G,A) = H_1(G,A)` is ordinary group homology, whose `1`-cycles are again finitely many module
elements. Prop 7's group `F(m)/F(m)^{(τ)} ⋊ G` does grow with `m`, which is exactly why it needs its
own argument; but that argument only ever applies the trick to `H_1(G, −)` and to
`H_1(F(n)/τ, E ⊗ T) ≅ F(n)/F(n)² ⊗ E(n,τ) ⊗ T` (universal coefficients, a module), both fine.
What remains needed from homological algebra is therefore: functoriality of `H²` and `H₁` in the
coefficients, and the five-term Hochschild–Serre sequence in homology for a semidirect product.

**(b) The refined `(i,j)` filtration — and with it Lemma 4(ii) and Witt's theorem — can be
dropped.** The refinement `P^{(i,j)} = (P^i ∩ P_j)P^{i+1}` exists to make each graded layer a
quotient of a *single* tensor power, so that `a ↦ ψ_a(z)` is a *homogeneous* form of degree `j`.
Proving that the layer is exactly the length-`j` part is what forces Lemma 4(ii), and Lemma 4(ii) is
Witt's theorem that `F_j/F_{j+1}` is a free `ℤ_p`-module — which Mathlib does not have. But
Chevalley–Warning never asks for homogeneity: it asks for a bound on the total degree and for
vanishing at the origin. On the coarse layer `P^i/P^{i+1}` the class of
`[x_{α₁},…,x_{α_j}]^{p^{i−j}}` transforms by the monomial `a_{k₁}⋯a_{k_j}`, so `a ↦ ψ_a(z)` is a
polynomial with all monomials of degree between `1` and `i`; it vanishes at `a = 0` and has total
degree `≤ i`. That is exactly the hypothesis of `exists_ne_zero_forall_eval_eq_zero`. Only the
*spanning* statement is then needed — `P^i/P^{i+1}` is generated by the images of the
`[x_{α₁},…,x_{α_j}]^{p^{i−j}}`, `1 ≤ j ≤ i` — and spanning follows by induction from the definition
`P^{i+1} = (P^i)^p[P^i,P]` and elementary commutator calculus (Lemma 4(i)), with no freeness input.

### What has landed

* `Shafarevich/Shrink.lean` (`49e31dc`) — Prop 2. `exists_ne_zero_forall_eval_eq_zero`: finitely
  many polynomials over a finite field, vanishing at the origin, with total degrees summing to less
  than the number of variables, have a common nonzero root (Chevalley–Warning plus the observation
  that the solution count is a positive multiple of the characteristic).
  `exists_ne_zero_forall_sum_prod_smul_eq_zero` is the homogeneous form actually quoted by
  Schmidt–Wingberg, stated without `PiTensorProduct` by using the canonical decomposition
  `⨂^s(⊕_r M) ⊗ N ≅ ⊕_{I ∈ (Fin r)^s} (M^{⊗s} ⊗ N)`, under which `ψ_a` is
  `(w_I) ↦ ∑_I a_{I₁}⋯a_{I_s} • w_I`. `sumSmul_surjective` is the accompanying fact that a nonzero
  coefficient vector combines `r` copies of a module onto it.
* `Shafarevich/PCentral.lean` (`82f4176`) — the descending `p`-central series `pCentral p P n`
  (indexed so `pCentral p P 0 = ⊤`), its characteristicity, naturality (`map_pCentral_le`, and
  `map_pCentral`: a surjection carries the series *onto* the series — this is what lets operators
  act on the layers), the two membership rules, monotonicity, and
  `map_pCentral_le_center`: each layer is central in the corresponding quotient.

### What remains

Group-theoretic: the spanning statement for `pCentral` (the coarse Prop 5), and the polynomiality
of `a ↦ ψ_a(z)` on the layer. Homological: functoriality of `H²`/`H₁` in the coefficients and
Hochschild–Serre in homology for `F/τ ⋊ G`, then Props 6 and 7. Arithmetic, and this is the wall:
Hoechsmann's obstruction criterion, Neukirch's principal homogeneous space, Lemma 10, Theorem 13,
and **Tate–Poitou duality with the `Ш` groups** — none of which is in this repository or in Mathlib.

---

## 0.26 Status (2026-08-28, later still) — §2 of Schmidt–Wingberg is complete, and the wall is narrowed to Tate–Nakayama

### The shrinking propositions are all theorems

Everything Schmidt–Wingberg put in their §2 — the part of Theorem 15 that is pure algebra — is now
in the repository, sorry- and axiom-free.

| Schmidt–Wingberg | repository |
|---|---|
| Prop 2 (Chevalley–Warning) | `Shafarevich/Shrink.lean` |
| Prop 5 (layers spanned by tensor powers) | `Shafarevich/PCentralSpan.lean`, `LayerWord.lean` |
| Prop 6 (shrinking in `Ĥ^k(G, E ⊗ T)`) | `Shafarevich/LayerCohomology.lean`, `LayerHomology.lean` |
| Prop 6, arbitrary acting group and tensor coefficients | `Shafarevich/GenericCohomology.lean` |
| Prop 7 (shrinking in `H¹(F(m)/ν ⋊ G, E ⊗ T)`) | `Shafarevich/GenericHomology.lean` |
| `[1] chap. 13 th. 2` (`σ*(ε_n) = π*(ε_m)`) | `CFT/GroupCohomology/ExtensionMap.lean` |

`GenericCohomology.lean` is the form Step 1 needs: the classes to be killed belong to a finite
group *mapping into* the operator group — the decomposition subgroup of a place — and the
coefficients are a layer tensored with a fixed representation. It subsumes the `T = Ind_{G_𝔭}^G 𝔽_p`
formulation without going through Shapiro, because the count never inspects the acting group; it
solves one scalar equation per value taken by the finitely many cocycles, and a cocycle of a finite
group takes `#H^c` values.

`ExtensionMap.lean` is the compatibility that makes the shrinking usable at all: a morphism of
extensions with abelian kernels identifies the class of the upper extension pushed forward along
the map of kernels with the class of the lower one pulled back along the map of quotients, the
trivialising cochain being the comparison of a transported section with a section below.

### The arithmetic wall, located exactly

Step 2 of Theorem 15 needs precisely one thing, its "Claim":

> there is a surjection `Ĥ^{-2}(G, E(-1)) ↠ Ш²(k, E)`, `G = Gal(K|k)`, `E(-1) = E ⊗ μ_p^∨`.

Schmidt–Wingberg get it from `Ш²(k,E) ≅ Ш¹(k,E′)^∨` (Tate–Poitou) together with `Ш¹(K,E′) = 0`,
which forces `Ш¹(k,E′) ⊆ H¹(G,E′)`; dualising and using `H¹(G,M)^∨ ≅ H₁(G,M^∨)` and
`E′^∨ = E(-1)` gives the Claim. Of the three inputs only the first is out of reach:

* `Ш¹(K,E′) = 0` for a **trivial** module is elementary — a cyclic extension in which every prime
  splits is trivial, which is `subsingleton_gal_of_isSolvable_of_splits_outside` in this
  repository. No Chebotarev density is needed.
* `H¹(G,M)^∨ ≅ H₁(G,M^∨)` over `𝔽_p` is finite-group duality, and `Ĥ^{-2} = H₁` is the
  identification already used throughout `Shafarevich/GenericHomology.lean`.

### Narrowing the wall: Tate–Nakayama in place of the nine-term sequence

The Claim does not need the whole Poitou–Tate machine. Unwinding it with Kummer theory:

1. `Ш²(k,E) ⊆ ker(H²(k,E) → H²(K,E))`, because `Ш²(K,E) = Ш(Br K)[p]^d = 0` by
   Albert–Brauer–Hasse–Noether, which this repository has.
2. Hochschild–Serre sends that kernel into `H¹(G, H¹(K,E))`, and Kummer theory rewrites the
   coefficients as `H¹(K,E) ≅ (K^×/K^{×p}) ⊗ E(-1)`.
3. Localisation embeds `(K^×/K^{×p}) ⊗ E(-1)` into `(∏_w K_w^×/K_w^{×p}) ⊗ E(-1)` — injectively,
   by Grunwald–Wang for a squarefree exponent, which is `CFT/GrunwaldWang.lean` — and semi-local
   Shapiro identifies the right-hand `H¹(G, −)` with `∏_𝔭 H¹(G_𝔭, −)`.
4. So the locally trivial classes are the image of the connecting map from `H⁰(G, C ⊗ E(-1))`,
   where `C` is the idele class group modulo `p`-th powers.
5. **Tate–Nakayama** — cup product with the fundamental class — turns `Ĥ⁰(G, C ⊗ E(-1))` into
   `Ĥ^{-2}(G, E(-1))`, which is exactly Schmidt–Wingberg's group.

That is a genuinely smaller target than the nine-term sequence: it needs Tate's theorem for the
*global* class formation, not local Tate duality and not the compact-discrete duality of restricted
products.

### What the repository's class field theory already supplies for that route

| ingredient | status |
|---|---|
| the idele group and the idele class group | `CFT/Units/Idele*.lean` |
| `H¹(Gal(K/k), C_K) = 0`, no hypothesis on the group | `Units/IdeleClassH1Full.lean` |
| first inequality (`#Ĥ⁰(G,C_K) = [K:k]` for cyclic `G`) | `Units/IdeleClassIndex.lean` |
| second inequality | `Kummer/SecondInequality.lean` |
| Hasse norm theorem, Albert–Brauer–Hasse–Noether | `Units/HasseNorm.lean`, `Units/ABHN.lean` |
| Tate cohomology of finite groups, Herbrand, Shapiro, hexagon | `CFT/Tate/` (57 modules) |
| **cup products in group cohomology** | absent |
| **the fundamental class of a class formation** | absent |
| **Tate's cohomological triviality theorem** | absent |
| **Tate–Nakayama** | absent |

The first six rows are the axioms of a class formation, so the missing four are a self-contained
project rather than a new theory: cup products (Mathlib has none for `groupCohomology`), then
Tate's theorem, then the fundamental class, then Tate–Nakayama.

### Two more shortcuts that do not work

* **Inflating the obstruction from a large finite quotient of `G_k`.** One might hope to replace
  `G_k` by a finite quotient `G̃` through which the obstruction is inflated, and then shrink with
  Prop 6 applied to `G̃`. The shrinking bound is `(j+1) · t · #G̃^c · dim(layer ⊗ T) < r`, so the
  rank `r`, hence `m = r·n`, grows with `#G̃`; but the quotient through which a class in `H²(G_k, E(m,ν))`
  is inflated depends on `m`. The argument is circular. This is exactly why Schmidt–Wingberg need a
  source for `Ш²` that lives on the *fixed* finite group `G`.
* **Making the layers induced or projective.** Already refuted in §0.25 for `Λ²`; three further
  attempts fail for the same reason. A free product over a free `G`-set has unordered-pair
  stabilisers of order 2; `Map(G,P) ↠ P` is not equivariant for nonabelian `P`, so
  Kaloujnine–Krasner only embeds; and `𝔽_p[U]` is semisimple only when `p ∤ #U`, a case the
  reduction cannot be steered into.

---

## 0.27 Status (2026-08-29) — three of the four missing rows are theorems; Tate–Nakayama is unconditional for flat coefficients

The four rows marked *absent* in the table of §0.26 have been reduced to one and a half.

### Cup products: bypassed, not built

Mathlib has no cup product for `groupCohomology`, and none was written. Instead of cupping with a
2-cocycle, dimension-shift once and cup with a **1-cocycle**, which is nothing but an extension:
`TateCohomology/CocycleExtension.lean` builds `cocycleObj A b` with carrier `A.V × k` and action
`ρ τ (m,c) = (A.ρ τ m + c · b τ, c)`, sitting in a short exact sequence `0 → A → cocycleObj → k → 0`
whose connecting map sends the canonical generator of `Ĥ⁰(H,ℤ)` to the class of `b`. Every use of a
cup product in Tate's theorem and in Tate–Nakayama goes through that extension instead.

### Tate's theorem and cohomological triviality

* `TateCohomology/SylowTrivial.lean`: `isZero_tateModule_of_sylow` — vanishing in **two consecutive
  degrees on a Sylow subgroup for every prime** forces vanishing in every degree. This is Tate's
  cohomological-triviality theorem; the `p`-group core is `CohomTrivial.lean` + `TorsionFree.lean` +
  `PTorsionTrivial.lean` + `PGroupTrivial.lean`.
* `TateCohomology/TateTheorem.lean`: `IsTateClass H A b` (the classical hypotheses in degrees zero
  and one on the restriction) on every Sylow gives `tateTheoremEquiv : Ĥⁿ(G,ℤ) ≅ Ĥⁿ⁺¹(G,A)`.
* `TateCohomology/TateDegreeTwo.lean`: the classical degree-two form, `IsTateClassTwo H A α` and
  `tateTheoremTwoEquiv : Ĥⁿ(G,ℤ) ≅ Ĥⁿ⁺²(G,A)`.

### Tate–Nakayama

`TateCohomology/TateNakayama.lean` gives `tateNakayamaEquiv : Ĥⁿ(G,M) ≅ Ĥⁿ⁺²(G, A ⊗ M)` under the
single hypothesis that the splitting extension stays cohomologically trivial after tensoring with
`M`. `TateCohomology/TensorFunctor.lean` and `TateCohomology/TensorTrivial.lean` discharge that
hypothesis whenever `M` is **flat over ℤ**:

* multiplication by a natural number commutes with tensoring, so the reduction sequence modulo `p`
  stays short exact after tensoring with a flat module;
* the reduction of a cohomologically trivial representation is killed by `p` and has no first
  cohomology, hence is the functions on the group, and those stay acyclic after tensoring
  (projection formula);
* the torsion hypothesis is removed by covering with a free induced representation, whose kernel is
  automatically torsion-free;
* restriction commutes with tensoring, so the argument runs on the Sylow subgroups.

The upshot is `tateNakayamaFlatEquiv`: for `M` flat over ℤ, **no hypothesis is left over**.

### The remaining half-row, stated exactly

Let `E` be cohomologically trivial with `pd_{ℤ[G]} E ≤ 1` and `0 → P₁ → P₀ → E → 0` a projective
resolution. Tensoring over ℤ with `M` gives `Ĥⁿ(E ⊗ M) ≅ Ĥⁿ⁺²(Tor₁^ℤ(E,M))`, so

> `E ⊗ M` is cohomologically trivial **iff** `Tor₁^ℤ(E,M)` is.

That is why the classical statement assumes `M` torsion-free, and it is what the flat case above
proves. Step 5 of the route in §0.26 applies Tate–Nakayama with `M = E(-1)`, which is **finite
`p`-torsion**, so `Tor₁(C_K, M) = C_K[p] ≠ 0` and the flat theorem does not apply. Two outs, neither
explored:

* only a **surjection** `Ĥ^{-2}(G,E(-1)) ↠ Ĥ⁰(G, C ⊗ E(-1))` is needed, and by the long exact
  sequence that needs only the single vanishing `Ĥ²(Tor₁(C_K,M)) = 0`;
* prove Serre's `cohomologically trivial ⟺ pd ≤ 1` and run the argument on a ℤ-free lift of `E(-1)`.

### Next target

The **fundamental class of the global class formation**: `Ĥ¹(H,C_K) = 0` is in
`Units/IdeleClassH1Full.lean`, and what is missing is that `Ĥ²(H,C_K)` is cyclic of order `#H`
generated by the restriction of a global class — that is, the invariant map. The repository has
`Local/UnramifiedInvariant.lean` (the unramified cyclic case), `Units/ABHN.lean`,
`Units/HasseNorm.lean`, `Units/FirstInequality.lean`, `Kummer/SecondInequality.lean` and the 43
modules of `Brauer/`. Once `IsTateClassTwo` is verified for `C_K`, `tateNakayamaFlatEquiv` applies
verbatim to every lattice of coefficients.

---

## 0.28 Status (2026-08-29, later) — Tate–Nakayama for `p`-torsion coefficients, and the reason it cannot be made unconditional

§0.27 left the flat case as the only reachable one. It is not: the *opposite* extreme — coefficients
killed by a prime, which is exactly what step 5 of the §0.26 route needs — is now also a theorem,
`InverseGalois/CFT/TateCohomology/TensorPTorsion.lean`, modulo **one** concrete vanishing.

### What landed

* `nsmul_tensorObj_eq_zero`, `nsmul_tensorObj_eq_zero'` — a tensor product one of whose factors is
  killed by `m` is killed by `m` (the number moves onto that factor).
* `isZero_tateModule_of_nsmul_eq_zero_coprime` — a representation killed by `m` with
  `gcd(m, #G) = 1` has no complete cohomology: `#G` annihilates every degree too, and Bézout
  finishes. So for coefficients killed by `p`, only the Sylow `p`-subgroup can carry anything.
* `isoOfBijective`, `bijective_tensorHomLeft_nsmulSeq_g`, `tensorModNsmulIso` — **reduction modulo
  `m` becomes an isomorphism after tensoring with a representation killed by `m`**: right exactness
  keeps it surjective, and its kernel is the image of multiplication by `m`, which is zero on the
  tensor product. So `E ⊗ M ≅ (E/mE) ⊗ M` whenever `mM = 0`.
* `isZero_tateModule_tensorObj_of_nsmul` — a representation `N` killed by `p` whose restriction to
  a Sylow `p`-subgroup has `H¹ = 0` satisfies: `N ⊗ M` is cohomologically trivial **for every** `M`.
  (`p`-Sylow: `N` is the functions on the group, and the projection formula; other Sylows: coprime
  orders.)
* `isZero_tateModule_tensorObj_of_nsmul_eq_zero` — combining the two: if `Ĥ¹(P, E/pE) = 0` for a
  Sylow `p`-subgroup `P`, then `E ⊗ M` is cohomologically trivial for every `M` killed by `p`.
* `isZero_tateModule_tensorObj_of_torsionFree_nsmul` — when `p` acts on `E` without torsion the
  hypothesis is automatic: `0 → E →ᵖ E → E/pE → 0` is short exact, so `E` cohomologically trivial
  forces `Ĥ¹(E/pE) = 0`.
* `tateNakayamaPTorsionEquiv` — **Tate–Nakayama for coefficients killed by a prime**, with the
  single hypothesis `Ĥ¹(P, Ê/pÊ) = 0` on the splitting module `Ê = cocycleObj (shiftObj A) b`.

### The hypothesis is genuine — an explicit counterexample

It is tempting to hope that `E` cohomologically trivial already forces `E/pE` cohomologically
trivial, which would make Tate–Nakayama unconditional for `p`-torsion coefficients. **It does not.**

Take `G = ℤ/2 = ⟨σ⟩`, `R = ℤ[G]`, and `r = 1 + 3σ`. Multiplication by `r` on `R` has matrix
`[[1,3],[3,1]]` in the basis `1, σ`, of determinant `-8 ≠ 0`, so it is injective, and

```
0 → R --·r--> R → E → 0,      E := R/rR
```

is a projective resolution of length 1. Hence `Ĥⁿ(H,E) = 0` for every `H ≤ G` and every `n`: `E` is
cohomologically trivial. Smith normal form gives `E ≅ ℤ/8` as an abelian group, with `σ` acting by
multiplication by `5` (from `x + 3σx = 0` and `3⁻¹ = 3` mod `8`). Checked directly: `E^G = 2ℤ/8`,
`N E = 6·ℤ/8 = 2ℤ/8`, so `Ĥ⁰ = 0`; `ker N = {0,4} = (σ-1)E`, so `Ĥ¹ = 0`.

But `E/2E = R/(r,2) = 𝔽₂[σ]/(1+σ) ≅ 𝔽₂` with **trivial** action (`5 ≡ 1` mod `2`), and
`Ĥ⁰(ℤ/2, 𝔽₂) = 𝔽₂/N𝔽₂ = 𝔽₂ ≠ 0`. So `E/2E` is *not* cohomologically trivial.

Consequences:

* out (b) of §0.27 is dead in its naive form: no lifting trick will remove the hypothesis, because
  the statement it would prove is false;
* the classical Tor hypothesis in Tate–Nakayama is not an artefact of the classical proof;
* what remains for step 5 of §0.26 is therefore an honest arithmetic question, and it is now a
  *single* one: `Ĥ¹(P, Ê/pÊ) = 0` for `Ê` the splitting module of the global fundamental class.
  Equivalently (dimension shift) `Ĥ³(P, Ê[p]) = 0`, and `Ê[p]` is a shift of `C_K[p]`.

### Next target, unchanged

Still the **fundamental class of the global class formation** (§0.27). Everything downstream of it
is now in place for both flat and `p`-torsion coefficients.

---

## 0.29 Status (2026-08-29, later still) — Tate's hypotheses reduced to a count, and a map of the remaining arithmetic

### What landed

`InverseGalois/CFT/TateCohomology/TateClassCount.lean` — the *abstract* half of the fundamental
class. It removes every mention of the restricted class from the hypotheses of Tate's theorem:

| name | statement |
| --- | --- |
| `exists_zsmul_of_card_eq` | an element of a finite commutative group annihilated by exactly the multiples of `Nat.card M` generates `M` |
| `dvd_of_zsmul_tateRes_eq_zero` | if `m • α = 0 ⟹ #G ∣ m`, then `m • res_H α = 0 ⟹ #H ∣ m` |
| `isTateClassTwo_of_card` | `IsTateClassTwo H A α` from `Ĥ¹(H,A) = 0`, `#Ĥ²(H,A) = #H` (finite), and `m • α = 0 ⟹ #G ∣ m` |
| `tateTheoremTwoEquivOfCard` | Tate's theorem from that count |
| `tateNakayamaFlatEquivOfCard` | Tate–Nakayama (flat coefficients) from that count |

The order transfer in `dvd_of_zsmul_tateRes_eq_zero` needs **no** Sylow-specific input, only that
`tateRes` is linear and that `cor ∘ res = ·[G:H]`: from `m • res α = 0` one gets
`res (m • α) = 0`, hence `[G:H] • (m • α) = 0` by `index_smul_eq_zero_of_tateRes_eq_zero`, hence
`#G ∣ [G:H]·m`, and `#H · [G:H] = #G` cancels the index. So the hypothesis of Tate's theorem on
*every* subgroup at once follows from one global order statement plus one count per subgroup.

That is exactly the shape in which a class formation presents its fundamental class, so what is
left of §0.27 is now a purely arithmetic list:

1. `Ĥ¹(H, C_K) = 0` — **the repo has this** (`eq_zero_H1_res_subgroup`,
   `eq_zero_H1_ideleClassRep_general`, `subsingleton_H1_ideleClassRep_general`), modulo the
   transport `resObj H (ideleClassRep k K) ↔ ideleClassRep (fixedField H) K`, whose pattern is
   already written out inside `eq_zero_H1_res_subgroup`.
2. `#Ĥ²(H, C_K) = #H` — **missing**.
3. a global `α ∈ Ĥ²(Gal(K/k), C_K)` annihilated only by multiples of `#Gal(K/k)` — **missing**.

Both missing items are the **invariant map**, and nothing weaker will do: see below.

### Counting cannot replace the invariant map

It is tempting to hope that `#Ĥ²(H,C_K) = #H` plus Sylow bookkeeping gives cyclicity for free.
It does not. Two observations, both negative:

* For a Sylow `p`-subgroup `P ≤ G` with `#Ĥ²(H,C) = #H` for all `H`, restriction *is* an
  isomorphism `Ĥ²(G,C)(p) ≅ Ĥ²(P,C)` (because `cor ∘ res` is multiplication by an index prime to
  `p`), and a global `α` of order `#G` restricts to an element of order `#P` (the other primary
  parts restrict to zero). So the global statement and the Sylow statements are equivalent — but
  that is a *transfer*, not a *proof*: something still has to produce cyclicity somewhere.
* Cyclicity of `Ĥ²(P,C_K)` itself does not follow from counting. Inflation–restriction on a chain
  `1 ◁ P' ◁ P` only exhibits `Ĥ²(P,C)` as an extension of `ℤ/#P'` by `ℤ/p`; every group of order
  `p²` is such an extension. One genuinely needs a homomorphism `Ĥ²(P,C) → (1/#P)ℤ/ℤ` that is
  injective, i.e. the **invariant map**.

### The one local brick that is missing

The invariant map is built from the local ones, and the repo's local half is already substantial:

* `unramifiedInvariant`, `unramifiedInvariant_surjective/_injective`, `unramifiedInvariantEquiv`
  (`CFT/Local/UnramifiedInvariant.lean`) — the invariant on the *unramified* part;
* `subsingleton_tateH0_kerUnitValAut`, `subsingleton_tateHm1_kerUnitValAut`
  (`CFT/Local/UnramifiedUnits.lean`), `herbrand_kerUnitValAut_eq_one`,
  `herbrand_smulUnitsAut_eq_card` (`CFT/Local/UnitHerbrandChain.lean`),
  `index_normSubgroup_eq_finrank_of_complete` (`CFT/Local/CompleteNormIndex.lean`) — the local norm
  index and the Herbrand quotient of the units;
* `brauerHom`, `brauerHom_injective` (`CFT/Brauer/H2Brauer.lean`), `cyclicBrauerHom`,
  `mem_ker_cyclicBrauerHom_iff` (`CFT/Brauer/CyclicBrauer.lean`),
  `exists_intermediateField_mem_relative`, `iSup_relative_eq_top`
  (`CFT/Brauer/MaximalSubfield.lean`), `card_relative_le_finrank_of_isLocalExtension`
  (`CFT/Brauer/LocalBrauerBound.lean`) — the Brauer-group dictionary.

The brick that is absent, and on which the whole invariant map rests, is:

> **every Brauer class over a complete discretely valued field with finite residue field is split
> by an unramified extension.**

The classical proof is by division algebras: extend the valuation of the base to a central division
algebra `D`, observe that the residue division ring is finite hence a field by Wedderburn, deduce
`e = f = d` for `d² = dim D`, and conclude that an unramified maximal subfield splits `D`. That is
a self-contained project of a few files, and it is the *only* remaining input for item 2 above; the
global invariant then follows from `⊕_v Br(K_w/k_v)` with semi-local Shapiro,
`exists_sub_add_eq_globalUnits` (ABHN, `CFT/Units/ABHN.lean`) and Hilbert reciprocity, plus the
surjection `H²(G, I_K) ↠ H²(G, C_K)`.

### A re-analysis of §0.26 step 5 — and why "out (a)" is *not* free

Two structural findings about the Schmidt–Wingberg argument, recorded so they are not rediscovered.

**(i) Steps 3–5 can be run entirely over `𝔽_p`.** The sequence

```
0 → K^× / p → I_K / p → C_K / p → 0
```

is exact — left exactness is precisely Grunwald–Wang, which the repo already has in power-class
form (`CFT/GrunwaldWang.lean`). All three terms are `𝔽_p`-vector spaces, so `⊗_{𝔽_p} E(-1)` is
exact on it, and one gets `Ш²(k, E) ⊆ im δ` with `δ` the connecting map out of
`Ĥ⁰(G, C_K ⊗ E(-1))`. No integral bookkeeping is needed anywhere in steps 3–5.

**(ii) The lattice-presentation route needs only the *flat* Tate–Nakayama — but it does not close.**
Choose a free presentation of `𝔽_p[G]`-modules over `ℤ[G]`,

```
0 → N → ℤ[G]^r → E(-1) → 0,
```

with `N` a lattice. Dimension shifting gives `Ĥ^{-2}(G, E(-1)) ≅ Ĥ^{-1}(G, N)`, and since
`ℤ[G]^r ⊗ C_K` is induced hence acyclic, `Ĥ⁰(G, E(-1) ⊗ C_K) ≅ Ĥ¹(G, Q)` where
`Q = ker(ℤ[G]^r ⊗ C_K → E(-1) ⊗ C_K)`. Surjectivity of `Ĥ¹(N ⊗ C_K) → Ĥ¹(Q)` — which is what the
Claim of §0.26 asks for — would then need only

```
Ĥ²(G, T) = 0,   T = Tor₁^ℤ(E(-1), C_K).
```

Every module in sight is a lattice, so this route uses **only** `tateNakayamaFlatEquiv` (§0.27) and
never the `p`-torsion version of §0.28. That is the good news. The bad news is that the required
vanishing is generally **false**:

```
T ≅ C_K[p] ⊗_{𝔽_p} E(-1),      C_K[p] ≅ (∏_v μ_p(K_v)) / μ_p(K)
```

(the term `ker(K^× / p → 𝔸^× / p)` dies by Grunwald–Wang), and
`∏_v μ_p(K_v) = ∏_𝔭 Ind_{G_𝔭}^G μ_p`, so by Shapiro

```
Ĥ²(G, C_K[p] ⊗ E(-1)) = ∏_𝔭 Ĥ²(G_𝔭, E)   (up to the μ_p(K) correction),
```

which is a product of *local* `Ĥ²`'s and is nonzero in general. **So "out (a)" of §0.26 is not
free**, and the lattice route does not shortcut Poitou–Tate.

**(iii) The Claim really is Poitou–Tate.** The statement `Ĥ^{-2}(G, E(-1)) ↠ Ш²(k, E)` is exactly
the dual of the inclusion `Ш¹(k, E′) ⊆ H¹(G, E′)`. There is no cheaper reformulation hiding in it;
the nine-term Poitou–Tate sequence (or at least the `Ш¹`–`Ш²` duality inside it) is a genuine
prerequisite for Schmidt–Wingberg Theorem 15, and is a separate project from the fundamental class.

### Consequence for the plan

The dependency graph for the last hypothesis (`FrattiniKernelEP` ≡ SW Thm 14/15) is therefore:

```
                       local: unramified splitting of a Brauer class   [MISSING, ~few files]
                                          ↓
                       invariant map → #Ĥ²(H,C_K) = #H, α of order #G
                                          ↓  (TateClassCount.lean — DONE)
                       fundamental class = IsTateClassTwo on every Sylow
                                          ↓  (TensorTrivial / TensorPTorsion — DONE)
                       Tate–Nakayama for the coefficient modules of SW §2
                                          ↓
     Poitou–Tate / Ш¹⊆H¹ duality  [MISSING, separate project]  →  SW Thm 13 → Thm 15
```

Two independent missing bricks, both classical, neither small. The abstract cohomological
machinery between and after them is now complete and unconditional.

---

## 0.30 Status (2026-08-29, night) — **the degree-two count is done**: two of the three class-formation conditions are unconditional

Item 2 of §0.29 — `#Ĥ²(H, C_K) ≤ #H` for **every** subgroup `H ≤ Gal(K/k)` and **every** Galois
extension of number fields — is now a theorem, sorry- and axiom-free. Note that the *inequality* is
all that `isTateClassTwo_of_card_le` wants: the reverse inequality comes for free from a class `α`
of order `#G`, whose multiples already fill `#G` elements. So §0.29's list now reads

1. `Ĥ¹(H, C_K) = 0` — **done** (`isZero_tateModule_resObj_ideleClassRep_one`);
2. `#Ĥ²(H, C_K) ≤ #H` — **done** (`card_tateModule_resObj_ideleClassRep_two_le`);
3. a global `α ∈ Ĥ²(Gal(K/k), C_K)` annihilated only by multiples of `#Gal(K/k)` — **missing**, and
   still exactly the invariant map, resting on the one local brick of §0.29.

`isTateClassTwo_ideleClassRep`, `tateIdeleClassEquiv` and `tateNakayamaIdeleClass`
(`CFT/Units/IdeleClassTate.lean`) therefore now carry **`hα` as their only hypothesis**.

### The two dévissages

Everything is bootstrapped from the cyclic count `#Ĥ²(C_K) = #Gal(K/k)`
(`card_H2_ideleClassRep_cyclic`, §0.24 era) by two reductions, each split into an abstract module
and its arithmetic instance.

| module | content |
| --- | --- |
| `CFT/GroupCohomology/H2Transport.lean` | `H²` transported along `e : G ≃* G'` compatible with `φ : A ≃+ B`; gives `card_H2_eq_of_addEquiv`, `finite_H2_of_addEquiv` (and the `Rep k G` universe-polymorphic versions) |
| `CFT/GroupCohomology/H2Devissage.lean` | counting inflation–restriction: `finite_and_card_H2_le_of_devissage` — for `π : G ↠ G'` with `B ↪ A` identifying `B` with `A^{ker π}`, and `Ĥ¹(ker π, A) = 0`, one has `#H²(G,A) ≤ #H²(G',B) · #H²(ker π, A)` |
| `CFT/GroupCohomology/H2Sylow.lean` | `finite_and_card_H2_le_of_sylow` — `H²(G,A) ↪ ∏_p H²(P_p, A)` by `eq_zero_of_forall_prime_res`, and `∏_p #P_p = #G` |
| `CFT/Units/IdeleClassH2Tower.lean` | the arithmetic instance of the dévissage: `galRestrictKerEquiv` identifies `Gal(K/F)` with `ker(Gal(K/k) ↠ Gal(F/k))`, `ideleClassComapLin` identifies `C_F` with `C_K^{Gal(K/F)}`, giving `finite_and_card_H2_ideleClassRep_of_tower` |
| `CFT/Units/IdeleClassH2Full.lean` | the induction: prime-power degree by `Sylow.exists_subgroup_card_pow_prime` + `Subgroup.normal_of_index_eq_minFac_card` (cyclic degree `p` at the bottom, `p^n` on top, and `p · p^n = p^{n+1}` is *exact*, so no slack accumulates), then the general case by Sylow, since `Ĥ²` restricted to `S` is `Ĥ²` over `fixedField S` |

The shape deliberately mirrors the degree-one story of §0.24 (`H1Transport` / `IdeleClassTower` /
`IdeleClassH1Full`); the only genuinely new ingredient is that the tower step now needs the
*vanishing* of `Ĥ¹` over the middle field as an input, which is exactly what the degree-one story
delivers.

### Two Lean gotchas worth keeping

* **`Rep.ρ` vs `Action.ρ`.** Writing the type `((Action.res _ S.subtype).obj A).ρ s a` makes `.ρ`
  resolve to `Action.ρ`, whose value is a `CategoryTheory.End` and is *not* a function. The fix used
  throughout is a `noncomputable abbrev` whose **declared type** is `Rep ℤ ↥S` (`ideleClassRepRes`,
  `ideleClassRepKer`); being an `abbrev` it still unifies with the unfolded form.
* **`Module ℤ` diamonds.** Relating a `Rep ℤ` carrier to an invariants submodule through `≃ₗ[ℤ]`
  produces mismatched `Module ℤ` instances; stating the transport with `≃+` and converting via
  `AddEquiv.toIntLinearEquiv` (whose `Module ℤ` argument is implicit) avoids it.

---

## 0.31 Status (2026-08-29, later) — the local brick is closed, and the route to `α` is re-planned (one claim of §0.29 was wrong)

### What landed

| module | content |
| --- | --- |
| `CFT/Local/NormValued.lean` | **going up.** `normValuation K L` is the valuation `y ↦ v(N_{L/K} y)`; carried on `spectralNorm.uniformSpace K L` it is a *topological* valuation (`normValued`), so a finite extension of a complete, discretely valued, locally compact field is again one. Plus: `valued_algEquiv_of_norm` (automorphisms preserve it, free from `Algebra.norm_eq_of_algEquiv`), `hasResidueChar_of_norm`, `isUnramifiedValued_of_norm`, and `finite_gradedAdd_of_properSpace` — the graded pieces are finite because `valAddSubgroup` is a **closed ball** (compact by `ProperSpace`) whose next step is **open**, so the quotient is discrete and compact. The old `GradedFinite.finite_gradedAdd` is unusable here: it wants a uniformizer of value exactly `exp(-1)`, and the norm valuation's value group is a proper subgroup of `ℤ`. The package is `exists_valued_of_spectralNorm`. |
| `CFT/Brauer/LocalBrauerOrder.lean` | `card_relative_eq_finrank_of_spectralNorm`, `exists_cyclic_relative_card_eq_finrank`, `..._adicCompletion`: **every Brauer class over a complete, discretely valued, locally compact field lies in a relative Brauer group of exactly the order of the degree.** |

So the node §0.29 called *"local: unramified splitting of a Brauer class"* is closed: the splitting
field exists (`exists_cyclic_unramified_mem_relative`, §0.29 era) **and** it is a local field again
with `#Br(L/K) = [L:K]`.

### The base field is `ℚ`, and that is a large simplification

Every hypothesis in the reduction chain is stated over `ℚ`: `GenericSplitEP`, `SplitPrimePowerEP`,
`ElementaryAbelianKernelEP`, `FrattiniKernelEP` all quantify over `IsInverseGalois` (Galois group
**over `ℚ`**). And `isTateClassTwo_ideleClassRep` takes `hα` **only for the full group** — the
subgroup conditions are derived from the counting. So the single missing statement is

> `∃ α ∈ Ĥ²(Gal(K/ℚ), C_K)` with `∀ m : ℤ, m • α = 0 → ([K:ℚ] : ℤ) ∣ m`, for every Galois `K/ℚ`,

equivalently `Ĥ²(Gal(K/ℚ), C_K) ≅ ℤ/[K:ℚ]` (the order is already `≤ [K:ℚ]`). Consequently the
**local invariant maps that are needed are only `inv_p : Br(ℚ_p) → ℚ/ℤ` and `inv_∞ : Br(ℝ) → ℚ/ℤ`**
— not local class field theory over an arbitrary local field. Over `ℚ_p` the unramified extensions
are `ℚ_p(ζ_m)`, `p ∤ m`, with Frobenius `ζ ↦ ζ^p`, and every abelian extension of `ℚ` is cyclotomic
(`CFT/KroneckerWeber.lean`), so the whole invariant/reciprocity layer can be kept cyclotomic.

### A correction to §0.29: `Ĥ²(G, I_K) ↠ Ĥ²(G, C_K)` is **false** in general

§0.29 lists "plus the surjection `H²(G, I_K) ↠ H²(G, C_K)`" as if it were free. It is not, and it is
not even true. From `1 → K^× → I_K → C_K → 1` the cokernel of that map injects into
`H³(G, K^×)`, and `H³(G, I_K) = ⊕_v H³(G_w, K_w^×) = 0` (local duality: `Ĥ³ ≅ Ĥ¹(G_w, ℤ) = 0`), so

```
coker( Ĥ²(G, I_K) → Ĥ²(G, C_K) )  ≅  H³(G, K^×)  ≅  ℤ/(n/m),   m = lcm_v [K_w : k_v].
```

**Counterexample.** `K = ℚ(√5, √41)`, `G = (ℤ/2)²`, `n = 4`. Both `5` and `41` are `≡ 1 mod 4`, and
`41 ≡ 1 mod 5` makes `41` a square mod `5` (hence `5` a square mod `41`), so at `5` and at `41`
only one of the two quadratic subfields ramifies and the decomposition group has order `2`; at `2`
and at `∞` the extension is unramified/split. So every `n_v ≤ 2`, `m = 2 < 4 = n`, and the map is
not onto. The fundamental class of such a `K/ℚ` genuinely does **not** come from ideles at level
`K`.

It *is* onto when `G` is **cyclic**, since then `H³(G, K^×) ≅ Ĥ¹(G, K^×) = 0` by Hilbert 90 and
two-periodicity. That is the only case in which the idele-theoretic description may be used
directly.

### The corrected route to `α`

Write `Inv : Ĥ²(G_ℚ, C) → ℚ/ℤ` for the map induced by `Σ_p inv_p` on ideles. The two properties to
prove are **well-definedness (reciprocity)** and **injectivity**, and then everything follows
formally:

* `inv_K ∘ res^{G_ℚ}_{G_K} = [K:ℚ] · Inv` (from `inv_w ∘ res = [K_w:k_v] · inv_v` locally);
* pick `x` with `Inv x = 1/n`; then `inv_K(res_K x) = 0`, so `res_K x = 0` by injectivity over `K`,
  i.e. `x ∈ H²(K/ℚ) = Ĥ²(Gal(K/ℚ), C_K)` (inflation is injective because `Ĥ¹ = 0`);
* `x` has order `n` because `Inv` is injective. **That is `α`.**

Injectivity can be bought by **counting** rather than by the Hasse principle: for a *cyclic* `L/F`
of degree `d`, `#Ĥ²(Gal(L/F), C_L) = d` exactly — the second inequality gives `≤` and the **first
inequality is already in the repo** (`CFT/Units/FirstInequality.lean`:
`herbrand_ideleClassAut_eq_degree`, `first_inequality`, plus two-periodicity `CFT/Tate/Hexagon.lean`)
gives `≥`. Since `Ĥ²(G, I_L) ↠ Ĥ²(G, C_L)` in the cyclic case and `Inv` is onto `(1/m)ℤ/ℤ`, a place
of full local degree forces `Inv` to be an isomorphism on `Ĥ²(Gal(L/F), C_L)`, hence injective
there. Every element of `Ĥ²(G_ℚ, C)` is split by a cyclic cyclotomic extension, which is where
`CFT/Cyclotomic/Chebotarev.lean` (cyclotomic Chebotarev over `ℚ`) and the classical device
"`ord_{p^r}(ℓ) → ∞`, so the cyclic degree-`p^r` subfield of `ℚ(ζ_{p^{r+1}})` has large local degree
at any fixed finite set of primes" come in.

So **ABHN is not needed for `α`**; reciprocity is. There is no way around reciprocity: the
statement "`a ∈ ℚ^×` is a local norm from a cyclic `K` at every place but one, hence at that one
too" is equivalent to it, and it is exactly what makes `C_ℚ / N C_K` *cyclic* rather than merely of
order `n` (see §0.29's two negative observations).

### Next targets, in order

1. `inv_p : Br(ℚ_p) → ℚ/ℤ`, built on the unramified tower `ℚ_p(ζ_{p^n-1})` with its Frobenius
   normalization, together with `inv ∘ res = f · inv`; and `inv_∞` on `Br(ℝ) = ℤ/2`.
2. Reciprocity `Σ_v inv_v = 0` on `Br(ℚ)`, by Kronecker–Weber: every class is a cyclotomic cyclic
   algebra, and the product formula for the cyclotomic norm-residue symbol is explicit.
3. The assembly above, giving `hα` and therefore the class formation.
4. Poitou–Tate / `Ш¹ ⊆ H¹` duality — still a separate project.

---

## 0.32 Status (2026-08-29) — the Frobenius normalization: what landed and what is left

Target 1 of §0.31 needs a **canonical** generator of `Gal(L/K)` for an unramified local extension:
`brauerInvariant hσ₀ hur hm` depends on the chosen generator `σ₀`, and replacing `σ₀` by `σ₀^k`
rescales the invariant.  (`normQuotientValInvariant : Kˣ/N(Lˣ) ≅ (1/n)ℤ/ℤ` is already canonical,
so the whole canonicity gap is the choice of `σ₀`.)  This section records the reduction.

### The local formalism to work in

There are two parallel local layers in the repo.  The Brauer-invariant layer lives in the **normed**
one — `[NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]`, `divisionNorm`,
`spectralNorm` — and *unramifiedness* there is the statement produced by the splitting theory of
division algebras,

```
hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖
```

("every absolute value is already the absolute value of a scalar", i.e. `e = 1`).
`Brauer/AdicUnramified.lean` bridges this to the `Valued A ℤᵐ⁰` layer.  The Teichmüller lift is
`Brauer/DivisionTeichmuller.lean`'s `exists_rootOfUnity_pow_divisionNorm_sub_lt_one`, in the normed
layer already — a duplicate in the `Valued` layer is not needed.

### Landed

* `Brauer/UnramifiedAdjoin.lean`
  * `isDivisionUniformizer_algebraMap` — under `hur` a uniformizer of `K` **is** a uniformizer of
    `L`.  (This is the whole force of `e = 1`: an element of absolute value `< 1` has the absolute
    value of a scalar of absolute value `< 1`.)
  * `exists_adjoin_rootOfUnity_eq_top_of_unramified` — **`L = K(ζ)`** for the Teichmüller root of
    unity `ζ` of order `N := #𝓀_L − 1`.  Proof: the powers of `ζ` cover every residue, so
    `finrank_le_mul_of_divisionNorm_eq_pow` (`Brauer/DivisionMaximal.lean`, which needs **no**
    centrality) applies to the subalgebra `M = K[ζ]` with `m = 1`, giving `[L:K] ≤ [M:K]`.
  * `algEquiv_eq_of_apply_eq_of_adjoin_eq_top` — an automorphism is determined by its value on `ζ`.
* `Brauer/UnramifiedAut.lean`
  * `exists_isPrimitiveRoot_adjoin_eq_top_of_unramified`, and `autToPow_injective`: the Mathlib
    monoid hom `IsPrimitiveRoot.autToPow K hζ : (L ≃ₐ[K] L) →* (ZMod N)ˣ` is **injective**.
  * `mul_comm_algEquiv_of_unramified` — the automorphism group of an unramified local extension is
    **commutative**.
  * `isCyclic_algEquiv_of_unramified` — it is in fact **cyclic**.  This one is a two-line corollary:
    `Brauer/DivisionCyclic.lean` already had the residue functor and the faithfulness of the action
    on the residue field (`divisionResidueHom`, `divisionResidueHom_comp`, `divisionResidueAut`,
    `divisionResidueAut_injective`, `isCyclic_algEquiv_of_rootOfUnity`,
    `norm_natCast_card_divisionResidue_sub_one`), and was missing only the input `L = K(ζ)`.
    ⚠️ Do **not** re-derive the residue functor: a from-scratch `Brauer/DivisionResidueAut.lean`
    written on 2026-08-29 was an exact duplicate of `DivisionCyclic.lean:126-190` and was deleted.

So `Gal(L/K) ↪ (ℤ/N)ˣ` canonically (the exponent `a(σ)` with `σζ = ζ^{a(σ)}` does not depend on the
choice of the generator `ζ` of `μ_N`), and the Frobenius is *by definition* the element with
`a(σ₀) = q`, where `q := #𝓀_K`.

### The one remaining input

That `σ₀` **generates** `Gal(L/K)`, equivalently the fundamental identity in the unramified case

```
f := [𝓀_L : 𝓀_K] = [L : K] =: n      (given e = 1)
```

Two half-arguments are available and neither is free:

* `n ≤ f`.  `divisionResidueAut_injective` already gives `Gal(L/K) ↪ RingAut 𝓀_L`, whose order is
  `f' := log_p #𝓀_L`; that only yields `n ≤ f'`.  Sharpening to `n ≤ f` needs the *relative*
  statement, i.e. a `𝓀_K`-algebra structure on `DivisionResidue K L` coming from
  `DivisionResidue K K → DivisionResidue K L`, plus `Gal(𝓀_L/𝓀_K) ≅ ℤ/f`.
* `f ≤ n`.  `𝓀_L = 𝓀_K[z]` and `z` kills the reduction of `minpoly K ζ`, whose coefficients are
  integral because `spectralNorm = spectralValue (minpoly K ·)`.

An alternative that avoids the residue-field functor: Mathlib's
`Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`
(`Mathlib/NumberTheory/RamificationInertia/Basic.lean:966`) is exactly `e · f = n` for a local
`S`, but it wants `IsDedekindDomain`, `IsIntegralClosure S R L` and `Module.Finite R S` — i.e. the
DVR packaging of `𝒪_K ⊆ 𝒪_L`, which is a comparable amount of plumbing in the *other* formalism.

Note that canonicity does **not** actually need `f = n`: `Gal(L/K) ↪ (ℤ/N)ˣ` already pins every
element down, and the unique preimage of `Frob_q^{f/n}` is a canonical generator.  What `f = n`
buys is that this generator is the *Frobenius*, which is what makes `inv ∘ res = f · inv` come out
right on a tower.

---

## 0.33 Status (2026-08-29, night) — `f = n` is a theorem, the Frobenius is canonical, and the normalized invariant exists

§0.32's "one remaining input" is **closed**, and the normalization it was blocking is landed.

### Landed

* `Brauer/DivisionResidueBase.lean` — `divisionResidueBase D : DivisionResidue K K →+* DivisionResidue K D`
  and its injectivity.  This is the `𝓀_K`-algebra structure on `𝓀_L` that §0.32 said was missing.
* `Brauer/ResidueDegree.lean` — `linearIndependent_of_linearIndependent_divisionResidue` (rescale a
  relation so its coefficients are integers and one of them is a unit, then reduce) and hence
  `card_divisionResidue_le_pow_finrank : #𝓀_L ≤ #𝓀_K ^ [L:K]`, i.e. **`f ≤ n`** for an arbitrary
  finite extension.
* `Brauer/ResidueGalois.lean` — the other half.  `isCyclotomicExtension_of_unramified` and
  `isGalois_of_unramified` (an unramified extension is `K(ζ_N)`, hence cyclotomic, hence Galois);
  `residueAlgAut` (the action on `𝓀_L` **over `𝓀_K`**) and `card_algEquiv_le_finrank_divisionResidue`
  give `n ≤ f`.  Together: `card_divisionResidue_of_unramified` and
  `finrank_divisionResidue_of_unramified` — **`f = n`** — and then
  `exists_frobenius_of_unramified`: there is a `σ` with `zpowers σ = ⊤` raising every residue to
  the `q`-th power.
* `Brauer/Frobenius.lean` — `IsDivisionFrobenius σ` as a predicate, `eq_of_isDivisionFrobenius`
  (**uniqueness**, via `divisionResidueAut_injective`), the choice-based `divisionFrobenius K L hur`
  with `divisionFrobenius_zpowers`, `forall_mem_zpowers_divisionFrobenius` (exactly the shape
  `brauerInvariant`'s `hσ₀` wants) and `eq_divisionFrobenius`.
* `Brauer/FrobeniusTower.lean` — for `K ⊆ L ⊆ L'`: `divisionNorm_algebraMap_tower` (both sides are
  the spectral norm, which is `spectralValue ∘ minpoly K`, and `minpoly.algebraMap_eq` says the
  minimal polynomial does not change — Mathlib even has `spectralNorm.eq_of_tower` outright);
  `unramified_of_unramified_tower`; `divisionIntegersTower`, `divisionResidueTower` and its
  injectivity; and the payoff `restrictNormal_divisionFrobenius`:
  **`(Frob_{L'/K}).restrictNormal L = Frob_{L/K}`.**
* `Brauer/LocalInvariant.lean` — `localInvariant K L hur hm : Br(L/K) →* Multiplicative (ℚ/ℤ)`,
  the invariant taken with respect to `divisionFrobenius`, with
  `localInvariant_apply_cyclicBrauerHom`, `exists_localInvariant_eq` (**it attains `1/n`**) and
  `localInvariant_tower` (**independent of the level of the unramified tower**, assembled from
  `brauerInvariant_tower` + `restrictNormal_divisionFrobenius` + a `brauerInvariant_congr_apply`
  that transports the implicit generator).

### What target 1 of §0.31 still needs

`localInvariant` is a map on `Br(L/K)` for **one** unramified `L`.  To get `inv_K : Br(K) → ℚ/ℤ`
one needs well-definedness across splitting fields: if `x ∈ Br(L₁/K) ∩ Br(L₂/K)` with both `Lᵢ/K`
unramified, the two invariants agree.  `localInvariant_tower` settles this **as soon as `L₁` and
`L₂` both embed in a common unramified `L₃`**, because `Br(Lᵢ/K) ≤ Br(L₃/K)` by
`BrauerGroup.relative_le_relative`.  So the remaining brick is the *standard unramified tower*:

* the extension `K_n := K(ζ_{q^n−1})` inside a fixed algebraic closure, and `K_n ⊆ K_m` for `n ∣ m`;
* `K_n/K` is **unramified** — this is the direction the repo does *not* have.  It needs a Hensel
  lift of a root of unity from `𝓀_K` (equivalently `f ≥ n` for `K(ζ_m)`, `m` prime to `p`);
  `exists_adjoin_rootOfUnity_eq_top_of_unramified` is the converse and does not help.
* transport of `localInvariant` along a `K`-isomorphism of splitting fields (Frobenius goes to
  Frobenius, so this should be routine once stated).

### The route to `α`, re-examined — what does *not* work

`hα` (`Units/IdeleClassTate.lean:89`) is exactly "`Ĥ²(Gal(K/ℚ), C_K)` has an element of order `n`";
the `≤ n` half and `Ĥ¹ = 0` are already in the repo.  Four shortcuts were checked and all fail:

1. **Sylow restriction on the `p`-parts.**  Gives an element of order the `p`-part in
   `Ĥ²(Gal(K/K^{S_p}), ·)`, not in `Ĥ²(Gal(K/ℚ), ·)`.
2. **Corestriction from a cyclic subgroup `H ≤ G`.**  `cor ∘ res = [G:H]`, so the class produced
   has order `|H|`, not `n`.
3. **"An element of order `d` for every `d ∣ n` ⇒ cyclic of order `n`."**  False: `(ℤ/2)²` has an
   element of order `d` for every `d ∣ 2`.
4. **"Pick a place of full local degree."**  Circular: knowing the local factor injects into
   `Ĥ²(G, C)` is what reciprocity provides, and `n_v = n` forces `G_v = G`, hence `G` cyclic.
   A place of full local degree exists only when `G` is cyclic.

Two positive facts worth keeping:

* **An elementary special case.**  For `E ⊆ ℚ(ζ_q)` the cyclic degree-`n` subfield with `q ≡ 1
  (mod n)` prime, `E/ℚ` is ramified only at `q`, and totally (tamely) ramified there.  Using
  `I_ℚ = ℚ^× × (ℝ_{>0} × ∏_p ℤ_p^×)` (valid because ℚ has class number one and
  `ℚ^× ∩ (ℝ_{>0} × ∏ ℤ_p^×) = 1`), the map `θ : C_ℚ → (ℤ/q)^×`, `(r,(u_p)) ↦ ∏_{p ∣ q} [u_p]^{-1}`,
  kills `ℚ^×` *by construction*, restricts at an unramified `p` to `Frob_p^{v_p}`, and at `∞` to
  complex conjugation.  It kills local norms at `∞` and at unramified `p` (because `Frob_p^{f_w} =
  1`), and at `q` because in a totally ramified extension all conjugates of a unit are congruent
  mod the maximal ideal, so `N(u) ≡ ū^n`, while `N(π) = q`.  Hence `C_ℚ/N C_E ≅ ℤ/n` for these `E`
  with no reciprocity input at all.
* **An inflation–restriction bootstrap.**  For `ℚ ⊆ K ⊆ L` Galois, `H¹(Gal(L/K), C_L) = 0` makes
  `0 → H²(K/ℚ) → H²(L/ℚ) → H²(L/K)` exact, so
  `|H²(K/ℚ)| ≥ |H²(L/ℚ)| / |H²(L/K)| ≥ [L:ℚ]/[L:K] = [K:ℚ]`.
  Hence **it suffices to find, for each Galois `K/ℚ`, one Galois `L ⊇ K` with `H²(L/ℚ)` cyclic of
  order `[L:ℚ]`** — cyclicity of `H²(K/ℚ)` then comes for free, being a subgroup of a cyclic group.

What is *not* avoidable: `C_ℚ ⊄ N_{L/K} C_L` place by place (already at an unramified `v` with
`e(w/v) = 1`, `ℚ_v^× ⊆ N_{L_W/K_w}` fails), even though the global Artin map does kill `C_ℚ`.  So
the everywhere-local-norm test only works on a cleverly chosen representative, and the general case
genuinely needs the invariants `inv_v` together with `Σ_v inv_v = 0`.

---

## 0.34 Status (2026-08-29, late) — **target 1 of §0.31 is done: the invariant map `inv_K : Br(K) → ℚ/ℤ` exists**

Both bricks §0.33 listed as missing turned out to be cheaper than advertised, and one of its claims
was wrong.

### §0.33's "this is the direction the repo does *not* have" was wrong

§0.33 said unramifiedness of `K(ζ_m)` "needs a Hensel lift of a root of unity".  It does not.  The
`f ≤ n` bound of §0.33 is already an equality-forcing device: if the residue field is *as large as
the degree allows* then the extension is unramified, and the residue field of `K(ζ_m)` is large
enough for purely multiplicative reasons.  Landed as commit `b271a34`:

* `Brauer/ResidueDegree.lean` — `divisionNorm_eq_one_of_divisionResidue_ne_zero`,
  `exists_divisionNorm_sum_eq` and **`unramified_of_card_divisionResidue`**: an extension with
  `#𝓀_L = #𝓀_K ^ [L:K]` is unramified.  (A basis of `𝓀_L` over `𝓀_K` lifts to integers whose
  `𝓀_K`-combinations exhaust every value of the norm; each such combination has norm `‖c‖` for a
  scalar `c`.)
* `Brauer/ResidueGalois.lean` — **`unramified_of_rootOfUnity`** and
  **`unramified_of_isCyclotomicExtension`**: a Galois extension generated by a root of unity whose
  order is invertible in `𝓀_K` has residue degree `n`, hence is unramified.  No Hensel lift.
* `Brauer/UnramifiedCompositum.lean` (new) — `norm_natCast_lcm_eq_one` (`gcd · lcm = a · b` plus
  `‖ℕ‖ ≤ 1`) and **`unramified_sup`**: each `L_i` is `K(ζ_{q_i−1})` by the *converse* direction, the
  compositum is cyclotomic of order `lcm(q₁−1, q₂−1)` via Mathlib's
  `IntermediateField.isCyclotomicExtension_lcm_sup`, and that order is still invertible.  **The
  compositum of two unramified extensions is unramified.**

So the standard unramified tower `K(ζ_{qⁿ−1})` never has to be constructed at all: *directedness*
is all that well-definedness needs, and `unramified_sup` gives it for the unramified subfields of a
fixed algebraic closure, ordered by inclusion.

### Transport along an isomorphism is free

§0.33's third bullet ("transport of `localInvariant` along a `K`-isomorphism … routine once
stated") needs **no new machinery at all**: `localInvariant_tower` already covers *isomorphisms as
degenerate towers of height one*.  Given `e : L ≃ₐ[K] L'`, make `L'` an `L`-algebra via `e`; then
`IsScalarTower K L L'` holds by `e.commutes`, and `divisionNorm_algebraMap_tower` transports
unramifiedness (`unramified_of_algEquiv`) while `localInvariant_tower` transports the invariant.
This collapses what looked like a separate `brauerInvariant`-congruence project.

### Landed: `Brauer/InvariantMap.lean`

* `unramified_of_algEquiv` — an extension isomorphic to an unramified one is unramified.
* `UnramifiedSubfield K` — a finite unramified `IntermediateField K (AlgebraicClosure K)`, bundled
  with its finiteness and unramifiedness; `isGalois` instance; `sup` (via `unramified_sup`).
* `UnramifiedSubfield.invariant` = `localInvariant` at that level; `invariant_mono` (a bigger
  unramified subfield computes the same invariant — one line from `localInvariant_tower`, using
  definitional proof irrelevance for the two unramifiedness proofs) and hence **`invariant_eq`**:
  two unramified splitting fields give the same invariant, because both sit in their compositum.
* **`exists_unramifiedSubfield_mem_relative`** — every class is split by one of these.  Take the
  cyclic unramified splitting field of `exists_cyclic_unramified_mem_relative`, embed it by
  `IsAlgClosed.lift`, and move unramifiedness across `AlgEquiv.ofInjectiveField`.
* **`localInvariantMap K hm`** and **`localInvariantHom K hm : Br(K) →* Multiplicative (ℚ/ℤ)`**,
  with `localInvariantMap_eq` (it is computed by *any* unramified splitting field) and
  **`localInvariantHom_apply_of_unramified`**: it agrees with `localInvariant K L hur hm` for every
  unramified `L`, whether or not `L` sits in the chosen algebraic closure.

Two Lean notes worth keeping.  `BrauerGroup` has **two** universe parameters and
`BrauerGroup.relative` pins only the first, so a binder `(x : BrauerGroup K)` whose type does not
otherwise pin the second auto-binds a fresh universe and every later instance search runs on the
wrong type — write `BrauerGroup.{0, 0} K`.  And `exact map_mul f ⟨x, hx⟩ ⟨y, hy⟩` elaborated
*against the goal* diverges (deterministic timeout at whnf even at 10⁶ heartbeats) while the same
term with an explicit type ascription elaborates in milliseconds; state it as a `have` and finish
with `rw`.

### What target 1 still does not give

`localInvariantHom` is a homomorphism, but nothing yet says it is **injective on `Br(L/K)` with
image `(1/n)ℤ/ℤ`**.  That is the next step and both halves are in hand:
`card_relative_eq_finrank_of_spectralNorm` (`|Br(L/K)| = [L:K]`) plus `exists_localInvariant_eq`
(the invariant attains `1/n`) force the map `Br(L/K) → (1/n)ℤ/ℤ` to be a bijection between two sets
of size `n`.  Then `inv ∘ res = f · inv` from `finrank_divisionResidue_of_unramified` +
`localInvariant_tower`, then reciprocity `Σ_v inv_v = 0` over ℚ, then the assembly giving `hα`.

---

## 0.35 Status (2026-08-30) — **the fundamental class is reachable without reciprocity**: the cyclotomic-auxiliary route

The chain at the end of §0.34 ("… then reciprocity `Σ_v inv_v = 0` over ℚ, then the assembly giving
`hα`") is **no longer the plan**.  A survey of what the repository already owns turned up a route to
`hα` that never mentions the Brauer group, never mentions the Artin map, and needs neither
Kronecker–Weber, nor Chebotarev, nor local class field theory, nor the *ramified* local restriction
formula.  It costs one genuinely number-theoretic argument (step 6 below) and a stack of plumbing.

### The wall, restated

`InverseGalois/CFT/Units/IdeleClassTate.lean:89`:

```lean
theorem isTateClassTwo_ideleClassRep {α : tateModule (ideleClassRep k K) 2} (S : Subgroup Gal(K/k))
    (hα : ∀ m : ℤ, m • α = 0 → (Nat.card Gal(K/k) : ℤ) ∣ m) :
    IsTateClassTwo S (ideleClassRep k K) α
```

Everything else in Tate–Nakayama for the idele class group is landed: `Ĥ¹ = 0` for every subgroup
(`Units/IdeleClassH1Full.lean`), `|Ĥ²(S)| ≤ |S|` for every subgroup
(`Units/IdeleClassH2Full.lean`), and `isTateClassTwo_of_card_le` turns "`α` has order exactly `n`"
into the Tate class.  So the *only* missing input is an element of order `|Gal(K/ℚ)|` in
`H²(Gal(K/ℚ), C_K)` — the fundamental class.

### Why counting cannot do it

Recorded so nobody re-tries it.  `Ĥ¹(S) = 0` together with `|Ĥ²(S)| ≤ |S|` for *all* subgroups `S`
does **not** force an element of order `|G|`: for `G = (ℤ/2)²` the data `Ĥ²(G) = (ℤ/2)²`,
`Ĥ²(S) = ℤ/2` for each of the three subgroups of order two, satisfies every inequality and has
exponent `2 < 4`.  Two related tricks also fail:

* "`|ker(res : Ĥ²(K'/ℚ) → Ĥ²(K'/K))| ≥ n` for a big enough `K'`" needs a `K' ⊇ K` carrying a place
  of full local degree, which forces `Gal(K'/ℚ)` solvable — no good for general `K`.
* `K ⊆ K'` with `K'/ℚ` cyclic forces `K/ℚ` cyclic, so one cannot simply enlarge to a cyclic field.

Some genuine arithmetic input is required.  The route below is the cheapest one found.

### The route

Let `K/ℚ` be finite Galois, `n = [K : ℚ]`.

1. **Auxiliary prime `q`.**  Pick a prime `q ≡ 1 (mod 2n)` with `q ∤ disc K`.  Available:
   `Nat.exists_prime_gt_and_pow_dvd_sub_one` (`Cyclotomic/CyclicSubfield.lean`).
2. **Auxiliary cyclic field `L`.**  `L` = the degree-`n` subfield of `ℚ(ζ_q)`.  It is cyclic,
   totally ramified at `q`, unramified everywhere else, and **totally real** (`n ∣ (q−1)/2` forces
   `−1` into the index-`n` subgroup `H ≤ (ℤ/q)ˣ`, and `H` is exactly the `n`-th powers).  Available:
   `exists_cyclic_totallyRamified`, `exists_intermediateField_cyclic_totallyRamified`
   (`Cyclotomic/TotallyRamified.lean`), `Subgroup.exists_index_eq_of_isCyclic`,
   `IsCyclic.exists_intermediateField_finrank_eq` (`Cyclotomic/CyclicSubfield.lean`).
3. **Auxiliary prime `p`.**  Pick `p ∤ disc K`, `p ≠ q`, with `p mod q` a primitive root of
   `(ℤ/q)ˣ`; then `Frob_p` generates `Gal(L/ℚ) ≅ (ℤ/q)ˣ / H ≅ ℤ/n`, i.e. `p` is inert in `L`.
   Needs Dirichlet on primes in arithmetic progressions — Mathlib
   `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`.
4. **Linear disjointness is automatic.**  `K ∩ ℚ(ζ_q) = ℚ`, because `ℚ(ζ_q)/ℚ` is totally ramified
   at `q` while `K` is unramified at `q`.  Hence `Gal(KL/K) ≅ Gal(L/ℚ) = Δ`, cyclic of order `n`.
5. **The two quotients have order `n`.**  `Q_ℚ := I_ℚ / (ℚˣ ⊔ N_{L/ℚ} I_L)` and
   `Q_K := I_K / (Kˣ ⊔ N_{KL/K} I_{KL})` both have order exactly `n`, from
   `card_H2_ideleClassRep_of_generator` (`Units/IdeleClassH2.lean`) transported by
   `ideleQuotEquivTateH0` (`Units/IdeleClassIndex.lean:175`) and `tateH0AddEquivH2`
   (`GroupCohomology/CyclicTate.lean:229`).
6. **(α) The idele `j` has order exactly `n` in `Q_ℚ`.**  Here `j` is `p` at the place `p` and `1`
   everywhere else.  *Proof by relation-chasing.*  Suppose `j^d = r · N(y)` with `r ∈ ℚˣ`,
   `y ∈ I_L`.  Compare place by place:
   * at `ℓ ∉ {p, q}`: `f_ℓ ∣ v_ℓ(r)`, because `v_ℓ` of a local norm lies in `f_ℓ ℤ`;
   * at `p`: `d ≡ v_p(r) (mod f_p = n)`, because `p` is inert in `L`;
   * at `q`: `r = N(y_w)^{-1}`, and `N(L_w^×) ⊆ ⟨q⟩ · U_H` where `U_H` = the units whose residue
     lies in `H` (`L_w/ℚ_q` is totally ramified of degree `n`, so `N(u) ≡ ū^n mod q`).

   Reducing the `q`-unit part of `r` mod `q` gives
   `sign(r) · ∏_{ℓ ≠ q} (ℓ mod q)^{v_ℓ(r)} ∈ H`.  Since `−1 ∈ H` (totally real!) and
   `(ℓ mod q)^{f_ℓ} ∈ H`, all the terms with `ℓ ≠ p` die, leaving `Frob_p^{v_p(r)} = 1` in
   `(ℤ/q)ˣ/H`, i.e. `n ∣ v_p(r) ≡ d`.  ∎
7. **(β) `[u_q^p] = [j]^{-1}` in `Q_ℚ`**, where `u_q^p` is `p` at the place `q` and `1` elsewhere.
   Indeed `j · u_q^p · (diag p)^{-1}` is `p^{-1}` outside `{p, q}` and `1` at `p, q`; every such
   place is unramified in `L` (or is `∞`, where `L_u = ℝ` and the norm is the identity), and units
   are norms in unramified local extensions.
8. **The norm map `N_{K/ℚ} : Q_K → Q_ℚ` is an isomorphism.**  Well defined because
   `N_{K/ℚ} ∘ N_{KL/K} = N_{KL/ℚ} = N_{L/ℚ} ∘ N_{KL/L}`.  **Surjective** because at the place `q`
   the extension `K_w/ℚ_q` is unramified, so the norm is onto the units (`exists_normHom_kerUnitVal`,
   `Local/UnramifiedUnits.lean`), and hitting `u = p` produces `[j]^{-1}`, a generator by (α)+(β).
   Equal finite orders `n` then give injectivity.
9. **`[j_K] = 0` in `Q_K`.**  `N_{K/ℚ}([j_K]) = [j]^n = 0` by `ideleNorm ∘ ideleComap = (·)^{[K:ℚ]}`,
   and `N_{K/ℚ}` is injective by step 8.
10. **Translate to cohomology.**  The class `x ∈ H²(Δ, C_L)` matching `[j]` has order `n`;
    `res(inf x) ∈ H²(Gal(KL/K), C_{KL})` matches `[j_K] = 0`.
11. **Inflation–restriction in degree two** (legitimate here because `Ĥ¹` of the idele class group
    vanishes — already proven) produces a unique `α ∈ H²(Gal(K/ℚ), C_K)` with `inf α = inf x`, of
    order `n`.  That is exactly `hα`.

### What this retires

* **Artin reciprocity in general form is off the critical path.**  Cyclicity of `C_ℚ / N C_L` is
  *equivalent* to reciprocity, but the elementary cyclotomic construction above supplies the one
  instance of it that is needed, directly.
* **The ramified local restriction formula `inv_L ∘ res = [L:K] · inv_K` is not needed.**  Because
  the auxiliary prime `p` is chosen unramified in `K`, only the already-landed unramified case
  (`localInvariant_baseChange`, `Brauer/LocalInvariantRestrict.lean`) would ever be used — and in
  fact the route above does not use the Brauer group at all.  §0.31's "next targets, in order" is
  superseded from its reciprocity bullet onward.
* Kronecker–Weber, Chebotarev density and local class field theory are all unnecessary; the only
  analytic input is Dirichlet's theorem, which Mathlib has.

### Bricks to build, in order

1. Local: `N(u) ≡ ū^n (mod 𝔪)` for a totally ramified extension of degree `n`, and hence
   `N(L_w^×) ⊆ ⟨π⟩ · U_H` once a uniformizer with `N(π_L) = π` is known.  Globally
   `π_L = N_{ℚ(ζ_q)/L}(1 − ζ_q)` has `N_{L/ℚ}(π_L) = q`.
2. Local: `v(N_{L_w/k_v}(y)) = f · v_w(y)` in the unramified case — check whether
   `valued_algebraMap_norm` (`Local/UnramifiedNormValue.lean`) already covers it.
3. The reduction identity for `r ∈ ℚˣ`:
   `r · q^{−v_q(r)} mod q = sign(r) · ∏_{ℓ ≠ q} (ℓ mod q)^{v_ℓ(r)}` — reuse whatever generation of
   `ℚˣ` by `−1` and the primes `Global/Reciprocity.lean` / `RationalSquareClasses.lean` used.
4. `f_ℓ(L/ℚ)` = order of `ℓ mod q` in `(ℤ/q)ˣ / H`, from `orderOf_arithFrobAt`
   (`Cyclotomic/Frobenius.lean`) plus the subfield dictionary.
5. Statement (α): `j^d ∈ ℚˣ ⊔ N I_L → n ∣ d`.
6. Statement (β): `[u_q^p] = [j]^{-1}`.
7. Bijectivity of `N_{K/ℚ} : Q_K → Q_ℚ`, and `[j_K] = 0`.
8. Cohomological plumbing: naturality of `tateH0ToH2` along a compatible pair (group homomorphism
   plus equivariant coefficient map), and inflation–restriction exactness in degree two for the
   idele class representation.  Check `Units/InflationDescent.lean`,
   `Units/IdeleClassH2Tower.lean`, `Units/IdeleClassTower.lean` first.

### Inventory of the repository assets this route uses

`card_H2_ideleClassRep_of_generator`, `card_H2_ideleClassRep_cyclic` (`Units/IdeleClassH2.lean`);
`tateH0AddEquivH2`, `card_H2_eq_card_tateH0`, `tateH0ToH2`, `ker_tateH0ToH2`
(`GroupCohomology/CyclicTate.lean`); `ideleQuotEquivTateH0`, `toTateH0`, `first_inequality_index`,
`mem_ker_toTateH0_iff`, `toTateH0_surjective` (`Units/IdeleClassIndex.lean`);
`finite_and_card_H2_res_subgroup` (`Units/IdeleClassH2Full.lean`); `eq_zero_H1_res_subgroup`
(`Units/IdeleClassH1Full.lean`); `exists_normHom_kerUnitVal` (`Local/UnramifiedUnits.lean`);
`unramifiedInvariantUnits_surjective`, `valued_algebraMap_norm` (`Local/UnramifiedNormValue.lean`);
`exists_cyclic_totallyRamified` (`Cyclotomic/TotallyRamified.lean`); `orderOf_arithFrobAt`,
`galEquivZMod_arithFrobAt` (`Cyclotomic/Frobenius.lean`);
`Nat.exists_prime_gt_and_pow_dvd_sub_one`, `exists_prime_and_cyclic_intermediateField`
(`Cyclotomic/CyclicSubfield.lean`); `hilbert_reciprocity`, `exists_sub_sq_iff_forall_local`
(`Global/Reciprocity.lean`, `Global/HasseNorm.lean` — quadratic reciprocity and the quadratic Hasse
norm theorem over ℚ are already done, and are the `n = 2` shadow of exactly this argument).

### Landed since §0.31

`84303e3`, `7e65083`, `bb7e06e`, `f859ac7`, `4126374`, `7f47e58` (the last being the base change of
a cyclic algebra along a compositum: `Brauer/CyclicCompositum.lean` +
`Brauer/InvariantCompositum.lean`, giving `brauerInvariant_baseChange_compositum` — the invariant is
multiplied by the ratio of the two valuations).

---

## 0.36 Status (2026-08-30) — the class formation is **done**, §2 of Schmidt–Wingberg is **done**, and the two remaining walls are *global duality* and *Chebotarev*

Three things happened since §0.35.  A fourth, an attempt to remove Poitou–Tate from step 2, was
tried and **refuted**; the refutation is in (c) and is worth keeping, because the argument is
seductive.

### (a) The class formation over `ℚ` is unconditional; `GlobalTate.lean` has landed

`InverseGalois/CFT/Units/GlobalFundamental.lean` supplies the third class-formation condition
(`exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_global`) for **every** Galois extension of `ℚ`, and
`InverseGalois/CFT/Units/GlobalTate.lean` names the fundamental class and derives, with no
hypotheses at all,

* `globalFundamentalClass` and `isTateClassTwo_globalFundamentalClass`,
* `globalTateEquiv` — Tate's theorem, `Ĥⁿ(G, ℤ) ≅ Ĥⁿ⁺²(G, C_K)`,
* `globalReciprocityEquiv` — the case `n = -2`, i.e. reciprocity,
* `globalTateNakayamaEquiv` — Tate–Nakayama for coefficients flat over `ℤ`.

Note for the future: **only the construction of the auxiliary cyclic field is specific to the base
`ℚ`.** `Units/IdeleClassTate.lean` already states conditions (1) and (2) for an arbitrary number
field base `k`, and `exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep` (the core of
`Units/RatFundamentalClass.lean`) is already general in `k`; `Units/CompositumEmbed.lean` is
base-agnostic except for the literal `ℚ`.  A general base needs only:

* the compositum `k·F₀` of `k` with a cyclic totally real `F₀ ⊂ ℚ(ζ_q)` of degree `n`, with `q`
  chosen to split completely in the Galois closure of `K/ℚ` and `≡ 1 mod 2n`;
* that this compositum is cyclic of degree `n` over `k` (every nontrivial subfield of `ℚ(ζ_q)` is
  ramified at `q`, while `q` is unramified in `k`), totally ramified at the places above `q`,
  unramified elsewhere, and archimedean-trivial (because `F₀` is totally real).

That is a bounded, mechanical project, and it is what a Chebotarev-over-`K` statement would need.

### (b) §2 of Schmidt–Wingberg is complete in Lean

The group-theoretic half of the Schmidt–Wingberg proof (arXiv `math/9809211`, = NSW ch. IX §6) is
already formalized:

| SW | Lean |
| --- | --- |
| Prop 2 (Chevalley–Warning shrinking) | `Shafarevich/Shrink.lean`, `exists_ne_zero_forall_sum_prod_smul_eq_zero` |
| Def 3 (`p`-central series, `P^{(i,j)}`) | `Shafarevich/PCentral.lean` |
| Prop 5 (`θ_τ` surjective, `G`-invariant) | `Shafarevich/PCentralSpan.lean`, `Shafarevich/Layer.lean` |
| Prop 6 (shrinking in `Ĥ^k(G, E(m,τ) ⊗ T)`) | `Shafarevich/GenericCohomology.lean`, `exists_operatorHom_res_cohomology_eq_zero` |
| Prop 7 (Ishanov, the `k = -2` variant) | `Shafarevich/GenericHomology.lean`, `exists_operatorHom_h1_eq_zero` |

Hoechsmann's criterion ([3] Satz 1.1 in SW) is *also* already there, at finite level:
`GroupExtension.exists_lift_iff_cohomologyClass_pullback_eq_zero`
(`CFT/GroupCohomology/Pullback.lean`), together with the whole `H²`-classifies-extensions
dictionary (`Classification.lean`, `OfCocycle.lean`, `ToCocycle.lean`, `ExtensionMap.lean`).

### (c) §0.29(iii) stands: **Poitou–Tate *is* needed for step 2 of SW Theorem 15**

An earlier revision of this section claimed the Claim could be bypassed by running the
Chevalley–Warning count directly against `Ш²(k, E(n,τ))`.  That is **wrong**; §0.29(iii)
("the Claim really is Poitou–Tate; there is no cheaper reformulation hiding in it") was right.
The refutation is worth recording, because the tempting argument looks correct from a distance.

SW's step 2 needs to kill an obstruction class living in `Ш²(k, E(n,τ))`.  Their Claim produces a
commutative square with **surjective** horizontals

```
Ĥ^{-2}(G, E(m,τ)(-1))  ↠  Ш²(k, E(m,τ))
        ↓                        ↓
Ĥ^{-2}(G, E(n,τ)(-1))  ↠  Ш²(k, E(n,τ))
```

so that Prop 6 (applied to the *left* column, a Tate cohomology group of the **finite** group `G`)
can be used to shrink.  Getting the horizontals costs Tate–Poitou duality
`Ш²(k,E) ≅ Ш¹(k,E′)^∨`, the Hasse principle, and "the dual of cohomology is homology".

The tempting shortcut: `Ш²(k, −)` is an `𝔽_p`-linear subfunctor of `H²(G_k, −)` and
`θ_a : E(m,τ) → E(n,τ)` is homogeneous of degree `j` in `a`, so why not apply the count with
`Ш²(k, E(n,τ))` itself as the target?

**Why it fails.**  The homogeneity of `θ_a` in `a` is *not* a statement about the map `θ_a`; it is
a statement about its pullback along the fixed surjection `θ_τ(m) : (P_m/P_m²)^{⊗j} ↠ E(m,τ)` of
Prop 5:

```
φ_a^{⊗j} = Σ_{i₁…i_j} a_{i₁}···a_{i_j} · (proj_{i₁} ⊗ ⋯ ⊗ proj_{i_j}),
θ_a ∘ θ_τ(m) = θ_τ(n) ∘ φ_a^{⊗j}.
```

The individual monomial maps `proj_{i₁} ⊗ ⋯ ⊗ proj_{i_j}` do **not** descend to `E(m,τ)` — only
their `a`-weighted sum does — so there is no decomposition `θ_a = Σ_μ a^μ c_μ` with `c_μ` maps of
`G`-modules, and hence no way to make `Ш²(k, θ_a)` polynomial in `a` at the level of `Ш²`.
Polynomiality is only visible on *elements* of `E(m,τ)` lying in the image of pure tensors.  Every
correct application of the count therefore has the shape

> represent the class to be killed by **boundedly many elements of `E(m,τ)`**, kill those, conclude

— and "boundedly" means *independently of `m`*, since `m = r·n` is chosen only after the count
demands `r > d · t · dim W`.  This is exactly what the repo's counting core
`Shafarevich.exists_ne_zero_forall_apply_eq_zero` (`Shafarevich/LayerTensor.lean`) already
formalizes: it takes a spanning family `u` of the **source** with `Φ a (u ω) = (monomial) • u' ω`.

For `Ĥ^k(G, −)` with `G = Gal(K|k)` finite and fixed, a class is represented by a cochain with
`|G|^k` values: bounded, so the count applies (that is Prop 6, and it is how step 1 works).  For
`Ш²(k, −) ⊆ H²(G_k, −)`, a class is represented by a cocycle on `Gal(M|k)` for some finite `M`
containing the field cut out by the extension in question — and that field grows with `m`.  The
requirement is circular, and the shortcut collapses.

One might hope to escape by *inflating*: is `Ш²(k, E) ⊆ inf H²(Gal(K|k), E)`?  Local triviality
does restrict to `K`, and `Ш²(K, E) = 0` for a `G_K`-trivial `E` (see (d)), so
`Ш²(k,E) ⊆ ker(res : H²(G_k,E) → H²(G_K,E)) = F¹H²`.  But Hochschild–Serre only gives
`F¹/F² ↪ H¹(G, H¹(G_K, E))` with `F² = inf H²(G, E)`, and `H¹(G_K, E) = Hom(G_K, E)` is enormous.
Cutting `F¹` down to `F²` is precisely the content of the duality theorem; there is no free lunch.

### (d) What of (c) survives, and where the duality actually enters

Three of the four ingredients of the Claim are duality-free and (almost) already in the repo:

* **Hasse principle ⇒ `Ш¹(k, E′) ↪ H¹(Gal(K|k), E′)`.**  A class of `Ш¹(k, E′)` restricts into
  `Ш¹(K, E′)`, which is `0` because a solvable extension in which every place splits completely is
  trivial — `CFT/Units/SplitNorm.lean`, `subsingleton_gal_of_isSolvable_of_free`.  In degree one
  inflation–restriction is exact on the left, so `Ш¹(k, E′) ⊆ inf H¹(G, E′)`.  (Note the contrast
  with degree two above: this is *why* SW dualize into degree one.)
* **Dualizing.**  `H¹(G, E′)^∨ ↠ Ш¹(k, E′)^∨`, and `H¹(G, E′)^∨ ≅ Ĥ^{-2}(G, E′^∨)` — the repo has
  `h1DualEquiv` (`CFT/GroupCohomology/Duality.lean`) and `h1TwistEquiv`,
  `exists_h1Twist_surjective` (`CFT/GroupCohomology/TateTwist.lean`).
* **Prop 6 / Prop 7** on the resulting finite-group Tate cohomology: done
  (`Shafarevich/GenericCohomology.lean`, `Shafarevich/GenericHomology.lean`).

The **single** genuinely missing input is the global duality isomorphism

```
Ш²(k, A) ≅ Ш¹(k, A′)^∨,   A′ = Hom(A, μ_∞)
```

i.e. Poitou–Tate.  That, not a generalized Chevalley–Warning, is the wall in step 2.

The finiteness observation from the discarded argument is still true and still useful in its own
right: for a `G_K`-trivial `E ≅ (ℤ/p)^d` with `μ_p ⊆ K`, `Ш²(K, ℤ/p) ≅ Ш²(K, μ_p) ≅ Ш(Br K)[p] = 0`
by Albert–Brauer–Hasse–Noether (needs `μ_p ⊆ K`, Hilbert 90, `H¹(G, C_K) = 0` — all present in the
repo).  This is what makes `Ш²(k, E)` finite, and it will be needed anyway.

And the two caveats established by re-reading the paper line by line remain:

* **Step 4 needs duality too.**  SW Theorem 13 (the existence of algebraic numbers with
  prescribed local behaviour) uses Chebotarev's density theorem, local Tate duality
  (Serre, *Galois Cohomology* II §5.2, §5.5), the exactness of the lower line of the long
  Tate–Poitou sequence, a pigeonhole argument, and the Hilbert-symbol product formula
  `∏_{P ∈ S(K)} (a, b)_P = 1`.  The `p = 2` case additionally runs the combinatorial three-element
  construction of Serre's *Topics* ch. 5 §3.
* **Lemma 10** (`0 → Ш¹(k_S, A′) → Ш¹(k_S, S∖T, A′) → coker(k_S, T, A)^∨ → 0`) also quotes the
  local and global duality theorems.

### (e) Chebotarev is the gateway, and Mathlib's analytic floor is further along than expected

Every route to Shafarevich in the literature (Shafarevich 1954; NSW ch. IX §6 = Schmidt–Wingberg;
Ishkhanov–Lur'e–Faddeev) passes through Chebotarev's density theorem over a general number field —
it is not an artefact of one write-up.  The two uses in SW Theorem 13 are, precisely:

* odd `p`: "choose a prime `P_{n+1} ∈ S ∖ T_n(K)` such that the image of `ξ` in
  `H¹(k_{T_n}|K, ℤ/p)^∨` equals `Frob_{P_n}`" — ray-class Chebotarev for the maximal abelian
  exponent-`p` extension of `K` unramified outside `T_n`;
* `p = 2`: "there is a prime `Q ∉ T(K)` of `O_{K,S_∞}` with `Q^σ ≠ Q` and `Q = A·(x)`" — every
  `S`-ideal class of `K` contains infinitely many primes.

Both are *abelian* Chebotarev, i.e. **Dirichlet's theorem for ray classes of a number field**.
Over `ℚ` this is Dirichlet + Kronecker–Weber, which the repo already has; over `K` it is not.

Mathlib v4.28 turns out to supply a surprising amount of the analytic floor:

* `Mathlib/NumberTheory/NumberField/DedekindZeta.lean` — `NumberField.dedekindZeta`,
  `dedekindZeta_residue`, and `tendsto_sub_one_mul_dedekindZeta_nhdsGT`, i.e. **Dirichlet's
  analytic class number formula**;
* `Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean` —
  `NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop`: **the count of ideals of bounded norm in
  a fixed class of the class group**;
* `Mathlib/NumberTheory/LSeries/` — `Dirichlet.lean`, `Nonvanishing.lean`, `PrimesInAP.lean`,
  `SumCoeff.lean`, `Positivity.lean`, `Convergence.lean`.

What is missing: ray-class groups with their `L`-functions, an *error term* in the ideal count
(`tendsto_norm_le_and_mk_eq_div_atTop` is a bare limit, and analytic continuation of `L(s,χ)` past
`Re s = 1` needs `A(x) = O(x^{1-1/d})`), Landau's theorem for Dirichlet series with non-negative
coefficients, non-vanishing at `s = 1`, and a density notion.  Also absent: any Chebotarev
statement, `groupCohomology` inflation as a named map, and an `H²`-classification of group
extensions (`Mathlib/GroupTheory/GroupExtension/` has only a docstring TODO).

### The remaining arithmetic, with costs

| # | Missing piece | Notes |
| --- | --- | --- |
| 1 | ~~`H^i(G_k, A)` for finite discrete `A`, as a filtered colimit `colim_M H^i(Gal(M/k), A)` over finite Galois `M ⊇ K`, with localization maps and `Ш^i`~~ | **DONE** — `InverseGalois/CFT/Profinite/`: `SmoothH1`/`SmoothH2` with `galInflH1`/`galInflH2`, `resH1`/`resH2`, and `sha1`/`sha2` (see §0.37) |
| 2 | ~~`Ш¹(k, A) ↪ H¹(Gal(K\|k), A)` from the Hasse principle, and its dual~~ | **DONE** — `CFT/Units/HasseInflation.lean`: `exists_galInflH1_eq_of_forall_level` and `exists_galInflH1_eq_of_forall_level_outside`, and — with the glue of §0.40 — `CFT/Units/HasseDecomposition.lean`: `exists_galInflH1_eq_of_finiteDecomposition(Outside)`, stated at the genuine decomposition subgroups of `G_k` |
| 3 | ~~Finiteness of `Ш²(k, E)` via ABHN + Hochschild–Serre~~ | **DONE** — `CFT/Units/HasseTwo.lean`: `eq_one_of_forall_isLocallySplitLevel`, the vanishing of the everywhere locally trivial classes of `H²` with `μ_n` coefficients, valid at `p = 2` (see §0.38).  The degree-one glue is §0.40; the degree-two glue is §0.42 — `CFT/Units/HasseTwoDecomposition.lean`: `eq_one_of_mem_sha2`, stated at `sha2 M (decompositionSubgroups k Ω)`, the genuine decomposition subgroups of `G_k` |
| 4 | ~~Local Tate duality for finite modules over a local field~~ | **DONE** — `CFT/Local/CyclicNormIndex.lean` (the norm index of *any* cyclic extension of a local field is its degree), `CFT/Local/KummerNonNorm.lean` (nondegeneracy of the `q`-th power norm residue symbol), see §0.39; `inv_M ∘ res = [M:K] · inv_K` is `localInvariantHom_baseChange` (`CFT/Brauer/InvariantBaseChange.lean`); and `CFT/Brauer/CyclicNormResidue.lean` assembles the norm residue symbol of a cyclic extension of a local field, see §0.56 |
| 5 | **Global duality `Ш²(k, A) ≅ Ш¹(k, A′)^∨`** | wall #1 as of §0.36; §0.84(c) argued this row was replaceable by degree-two Hochschild–Serre, but **§0.87 refutes that** (step 3 there is circular), so the row stands.  **§0.88 does the torsion-free half unconditionally** (`CFT/Units/IdeleTorusSha.lean`: the locally trivial part of `Ĥ^{n+3}(G, K^×⊗N)` is the image of `Ĥ^n(G,N)`, from the class formation alone) and reduces the `p`-torsion half to the derived correction `Ĥ^*(G, C_K[p]⊗W)` in Tate–Nakayama |
| 6 | ~~The `p`-th power Hilbert symbol over a number field and its product formula~~ | **DONE** — `CFT/Profinite/Symbol.lean` builds `kummerSymbol` for Kummer data of any exponent over any base, and `CFT/Brauer/CyclicProduct.lean` proves `totalInvariant_smoothBrauerHom_kummerSymbolUnits` and its finite-set form; `CFT/PoitouTate/CupDual.lean` generalizes both to the pairing of a class with a class with Cartier dual coefficients (see §0.89).  The *local* nondegeneracy of the `p`-th power symbol is §0.39(b) |
| 7 | ~~**Chebotarev density over a number field**, in the abelian/ray-class form of (e)~~ | **DONE for odd `p`** — `NumberTheory/RelativeSplitDensity.lean` + `CFT/RelativeFrobenius.lean`: Theorem 13 only needs the Frobenius *up to a scalar*, which is `exists_relStabilizer_eq_zpowers` (see §0.41).  What remains is "every ideal class contains a prime", used only in the `p = 2` Claim |
| 8 | Poitou–Tate, at least the eight-term sequence for `μ_p` over `k_S` | needed by Lemma 10 and Theorem 13; §0.84(c) argued this row was avoidable, **§0.87 refutes that** |
| 9 | SW Theorem 13, then Theorems 14 and 15 | assembly |

Already-existing bricks that will be consumed and should not be rebuilt:

* `CFT/GroupCohomology/Duality.lean` — `h1DualEquiv` (`H₁` of the contragredient `≅` dual of `H¹`);
* `CFT/GroupCohomology/TateTwist.lean` — `h1TwistEquiv`, `exists_h1Twist_surjective` (the finite-
  group half of SW's Claim, already formalized);
* `CFT/Units/ABHN.lean` — `exists_sub_add_eq_globalUnits`;
* `CFT/Units/SplitNorm.lean` — `subsingleton_gal_of_isSolvable_of_free`, the Hasse-principle brick;
* `CFT/GrunwaldWang.lean` — Grunwald–Wang in power-class form (SW Prop 11 wants the character
  form).

---

## 0.37 Status (2026-08-30) — rows 1 and 2 were already built; `Br(K) ≅ ℚ/ℤ` is now a theorem

### (a) Two rows of the §0.36 table were stale

A survey of the tree found that the "next brick" named in §0.36 had in fact already been laid,
twice over.

**Row 1** is `InverseGalois/CFT/Profinite/`.  It carries the smooth (= continuous, finite-level)
cohomology of the absolute Galois group in degrees one and two — `SmoothH1`, `SmoothH2`,
`smoothH1Mk`, `smoothH2Mk` — with the inflation maps `galInflH1`, `galInflH2` from a finite level,
the localization maps `resH1`, `resH2` to a subgroup, and the Tate–Shafarevich subgroups
`sha1 (S : Set (Subgroup G))`, `sha2` cut out by them (`Profinite/Res.lean`), plus the trivial-
action dictionary in `Profinite/Trivial.lean` (`cocycleHom`, `smoothH1Mk_eq_one_iff_of_trivial`,
`resH1_eq_one_iff_of_trivial`, `smoothH1Mk_mem_sha1_iff_le_ker`).

**Row 2** is `InverseGalois/CFT/Units/HasseInflation.lean`.  It proves exactly the required
statement — a smooth one-cocycle that dies on every decomposition subgroup at every finite level is
inflated from that level:

```lean
theorem exists_galInflH1_eq_of_forall_level (hs : IsSmooth₁ u) (hloc : …) :
    ∃ z : SmoothH1 (↥F ≃ₐ[k] ↥F) M, galInflH1 F hπ z = smoothH1Mk u hu hs
```

together with the variant `exists_galInflH1_eq_of_forall_level_outside` that ignores a finite set of
places.

**What is genuinely still open in row 2** is only the glue: `sha1` is stated for an abstract family
`S : Set (Subgroup G_k)`, while `HasseInflation` quantifies over `levelDecompositionSet L`.  Making
the two match needs *genuine* decomposition subgroups of `G_k` — i.e. a place of `k̄` over a place
of `k` and its stabilizer — which is a design task in its own right and has been deferred.

### (b) The Brauer group of a local field is `ℚ/ℤ`

`InverseGalois/CFT/Brauer/InvariantSurjective.lean` closes the other half of the local invariant
map.  Injectivity was already in `InvariantInjective.lean`; surjectivity needs unramified
extensions of arbitrary degree, which the file builds by hand:

* `dvd_of_pow_sub_one_dvd_pow_sub_one : 2 ≤ q → q ^ a - 1 ∣ q ^ b - 1 → a ∣ b`.  Elementary, but not
  in Mathlib — only the converse `Nat.pow_sub_one_dvd_pow_sub_one` is.  The proof writes
  `b = a·(b/a) + b%a`, moves to `ℤ` (where `x^b - 1 = x^{b%a}(x^{a(b/a)} - 1) + (x^{b%a} - 1)` is a
  ring identity), and squeezes the remainder term between `0` and `q^a - 1`.
* `dvd_card_divisionResidue_sub_one_of_isPrimitiveRoot` — a root of unity whose order is invertible
  in `K` keeps that order in the residue field.  Its residue is a nonzero element of a finite field,
  so `ζ^{N-1}` is congruent to `1`; and a root of unity of invertible order congruent to `1` **is**
  `1` (`eq_one_of_pow_eq_one_of_divisionNorm_sub_lt_one`, from `DivisionCyclic.lean`).  Hence
  `M ∣ N - 1`.
* `exists_unramified_dvd_finrank` — given `n`, put `Q = #(residue field)` and `M = Q^n - 1`.  Then
  `‖M‖ = 1` (`norm_natCast_pow_card_divisionResidue_sub_one`), so `L = CyclotomicField M K` is
  unramified (`unramified_of_isCyclotomicExtension`) and its residue field has `Q^{[L:K]}` elements
  (`card_divisionResidue_of_unramified`).  The primitive `M`-th root forces `M ∣ Q^{[L:K]} - 1`,
  i.e. `Q^n - 1 ∣ Q^{[L:K]} - 1`, i.e. `n ∣ [L:K]`.
* `localInvariantHom_surjective` — for a target `r + ℤ`, take `n = r.den`, get `L` with
  `[L:K] = r.den · t`, take the class `w` with invariant `1/[L:K]` (`exists_localInvariant_eq`) and
  raise it to the power `r.num · t`.
* `localInvariantEquiv : BrauerGroup K ≃* Multiplicative (ℚ/ℤ)` — the two halves combined.

This is the group-theoretic cornerstone of local class field theory and the prerequisite for row 4
(local Tate duality) and row 6 (the `p`-th power Hilbert symbol).

---

## 0.38 Status (2026-08-30, later) — row 3 is laid: `Ш²(k, μ_n) = 0`, and the prime `2` is covered

### (a) The relative Brauer group of a local field is bounded by the degree

`InverseGalois/CFT/Brauer/RelativeTorsion.lean` isolates the `n`-torsion of `ℚ/ℤ` as a subgroup,
transports it through `localInvariantEquiv`, and reads off the consequences for the relative Brauer
group of a finite extension `L/K` of local fields:

* `nsmulTorsionQModZ`, `zmodEquivNsmulTorsionQModZ`, `natCard_nsmulTorsionQModZ` — the `n`-torsion of
  `ℚ/ℤ` is cyclic of order `n`;
* `brauerTorsion`, `brauerTorsionEquiv`, `natCard_brauerTorsion` — hence the `n`-torsion of `Br K`
  is cyclic of order `n`;
* `relative_le_brauerTorsion`, `finite_relative_local`,
  `card_relative_le_finrank_local : Nat.card ↥(relativeBrauerGroup K L) ≤ finrank K L` — a class
  split by `L` is killed by `[L:K]`;
* `relative_eq_brauerTorsion_of_unramified` — for unramified `L/K` the bound is an equality.

The reverse bound `#Br(L/K) ≥ [L:K]` for an arbitrary `L` still wants the base-change formula
`inv_L ∘ res = [L:K] · inv_K`, which is what would turn this into the local reciprocity isomorphism.

### (b) The local-global principle for central embedding problems, now at `p = 2` as well

The multiplicative wrappers of Albert–Brauer–Hasse–Noether that were in the tree all bought their
silence at the archimedean places by restricting the integer killing the cocycle — odd order, or
order coprime to the local degrees at infinity.  Two new files remove the restriction and pay for
the infinite places instead:

* `InverseGalois/CFT/Units/ABHNPlaces.lean` — `smulUnitsAut_infiniteUnitHom_algebraMap` (the
  decomposition group at an archimedean place fixes the local units coming from the base field) and
  `exists_isMulCoboundary_of_forall_place`: **a two-cocycle with values in `kˣ` which splits at
  every place of `K`, archimedean places included, is the coboundary of a one-cochain with values
  in `Kˣ`** — no hypothesis whatever on the cocycle.
* `InverseGalois/CFT/Kummer/CentralEmbeddingPlaces.lean` —
  `exists_surjective_hom_of_forall_place`, the archimedean twin
  `exists_local_coboundary_of_exists_lift_infinitePlace` of
  `exists_local_coboundary_of_exists_lift`, and
  `exists_surjective_hom_of_forall_place_lift`: **a central Frattini embedding problem that is
  solvable over the decomposition group at every place is solvable over a larger extension**, with
  no restriction on the order of the kernel.

This is the form of the criterion that survives at `p = 2`, where the real places genuinely
obstruct.

### (c) Row 3: the everywhere locally trivial classes of `H²` with `μ_n` coefficients vanish

`InverseGalois/CFT/Units/HasseTwo.lean` is the degree-two analogue of `Units/HasseLevel.lean` and
`Units/HasseInflation.lean`, and it is what §0.36(d) asked for:

* `exists_level_cochain₂` — a two-cochain constant on the cosets of the kernel is a two-cochain of
  the quotient (the curried companion of `exists_comap₂_eq`, with no action on the quotient
  required);
* `restrictNormalHom_eq_of_res` — restriction to a level factors through restriction to a larger
  level, which is what transfers a cochain produced at the radical level back down;
* `IsLocallySplitLevel ι L a` — the local hypothesis: the `kˣ`-transported level cocycle is a
  coboundary in the completion at every place of `L`, archimedean places included;
* `exists_isSmooth₁_coboundary₂_eq_of_isLocallySplitLevel` — the inflation of a locally split level
  cocycle to `G_k` is the coboundary of a **smooth** one-cochain;
* `smoothH2Mk_eq_one_of_isLocallySplitLevel`, and
* `eq_one_of_forall_isLocallySplitLevel` — **a class of `SmoothH2 G_k M` every level representative
  of which splits at every place of its level is trivial**, for coefficients `M` acted on trivially
  and embedded in `kˣ` as the `n`-th roots of unity.

The chain is: `exists_isGalois_smooth₂` (every class lives at a finite Galois level) →
`exists_level_cochain₂` (descend the representative to that level) →
`exists_isMulCoboundary_of_forall_place` (ABHN, §0.38(b), so `p = 2` is fine) →
`exists_intermediateField_cochain_of_isMulCoboundary` (Kummer, `Kummer/CocycleDescent.lean`:
rescale over a radical extension so the trivialising cochain is `μ_n`-valued) →
`restrictNormalHom_eq_of_res` + `isSmoothHom_restrictNormalHom` (read it as a smooth cochain on
`G_k`).  Notably the profinite Kummer sequence is **not** needed: the finite-level Hilbert 90
argument already in `Kummer/InflationRootsOfUnity.lean` does the whole job.

**What was still open in row 3** (closed in §0.42) is the same glue as in row 2:
`IsLocallySplitLevel` quantifies over the places of a *level*, while genuine membership in `sha2`
is a statement about the decomposition subgroups of `G_k` itself.  Matching the two needs a place of `k̄` over a place of `k` and its
stabilizer — the design task deferred in §0.37(a).  With that glue, the finiteness of `Ш²(k, E)`
for a `G_K`-trivial `E ≅ (ℤ/p)^d` is `Ш²(K, μ_p)^d = 0` plus Hochschild–Serre.

### (d) The table, updated

Rows 1, 2 and 3 are laid (each modulo the one shared glue lemma, itself closed in §0.40 for
degree one and in §0.42 for degree two).  The next brick is **row 4**,
local Tate duality with `μ_p` coefficients, for which `localInvariantEquiv` (§0.37(b)) and the
torsion computation of §0.38(a) are the inputs.  Rows 5 and 7 — Poitou–Tate and Chebotarev over a
number field — remain the two walls.  (Row 4 was laid the same day; see §0.39.)

---

## 0.39 Status (2026-08-30, later still) — the local norm index for **every** cyclic extension, and the nondegeneracy of the norm residue symbol

### (a) The unramifiedness hypothesis was never needed

`InverseGalois/CFT/Local/CompleteNormIndex.lean` has carried, for some time, the sharp local first
inequality

```
(normSubgroup K L).index = finrank K L
```

for an arbitrary cyclic `L/K` — ramified or not — *provided* the larger field `L` is itself
presented as complete and discretely valued with the automorphisms acting by isometries.  What was
missing was the package supplying that presentation.  The only one in the tree,
`exists_valued_of_spectralNorm` (`CFT/Local/NormValued.lean`), carries a hypothesis

```
hval : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ spectralNorm K L z = ‖c‖
```

which says `L/K` is unramified.  Reading its proof line by line shows that `hval` is used for
**one** conclusion only, `IsUnramifiedValued K L`; every other component — the valuation
`normValued K L`, completeness, rank one, proper-ness, the residue characteristic, finiteness of
the graded pieces, invariance under `Gal(L/K)`, a unit of nontrivial value, a generator of the
value group — is proved from the field norm alone and does not care about ramification.

`InverseGalois/CFT/Local/CyclicNormIndex.lean` therefore just drops it:

* `exists_valued_of_finite` — **a finite extension of a complete, discretely valued, locally
  compact field carries all the structure of a local field**, with no hypothesis on the extension;
* `index_normSubgroup_eq_finrank_local` — **the norm index of any cyclic extension of a local field
  is its degree**;
* `exists_notMem_normSubgroup` — hence a cyclic extension of degree bigger than one always has a
  unit of the base field which is not a norm.

This is the first inequality of local class field theory in full.  It is one of the two halves of
the local reciprocity isomorphism `Kˣ / N Lˣ ≅ Gal(L/K)^{ab}`; what the second half still wants is
the base-change formula `inv_L ∘ res = [L:K] · inv_K` of §0.38(a).

### (b) The norm residue symbol is nondegenerate

`InverseGalois/CFT/Local/KummerNonNorm.lean` is the immediate arithmetic consequence, and it is the
shape in which the theory of embedding problems actually consumes local duality.  Let `K` be a
local field containing a primitive `q`-th root of unity, `q` prime, and let `a ∈ K` not be a `q`-th
power.  Then `X^q - a` is irreducible (`X_pow_sub_C_irreducible_of_prime`, valid at `q = 2` too),
its splitting field is cyclic of degree `q` over `K` (Mathlib's Kummer API), and (a) gives a unit of
`K` which is not a norm from it:

* `exists_notMem_normSubgroup_of_isSplittingField` — for any field presented as a splitting field of
  `X^q - a`;
* `exists_cyclic_notMem_normSubgroup` — packaged with the construction of the extension by
  `AdjoinRoot`, together with the root itself and the degree.

Written with the norm residue symbol `(a, c)` — the class of the cyclic algebra of `K(q√a)` with
coefficient `c`, equivalently the amount by which the Artin symbol of `c` moves `q√a` — this says
that the symbol is nondegenerate in its second argument: for every `a` which is not a `q`-th power
there is a `c` with `(a, c) ≠ 1`.  That is the duality between `H¹(K, μ_q)` and `H¹(K, ℤ/q)` in the
only shape rows 6 and 9 use it.

### (c) What row 4 still owes

The full statement of local Tate duality — a perfect pairing
`H^i(K, A) × H^{2-i}(K, A′) → H²(K, 𝔾_m) = ℚ/ℤ` for every finite module `A` — is not what SW
Theorem 13 consumes; it consumes the `i = 1`, `A = ℤ/p` case, which is (b), plus the *global*
product formula for the same symbol (row 6).  So the honest reading of the table is that row 4 is
laid in its usable form, and the remaining work has moved into rows 6 and 5.

The one piece of row 4 which is genuinely still missing and genuinely still wanted elsewhere is the
invariant-map functoriality `inv_M ∘ res = [M:K] · inv_K` for an arbitrary finite `M/K`.  The tree
has `localInvariant_baseChange` (`Brauer/LocalInvariantRestrict.lean`) only for `K ⊆ M ⊆ L` with
`L/K` unramified, and `brauerInvariant_baseChange_compositum`
(`Brauer/InvariantCompositum.lean`) only when `Gal(N/M) ≅ Gal(E/K)`, which fails as soon as
`E ∩ M ≠ K`.  The classical repair is to factor `M/K` through its maximal unramified subextension
`M₀` (degree `f`) and the totally ramified `M/M₀` (degree `e`), using
`exists_unramified_le_finrank_eq`, `eq_of_finrank_eq_of_unramified` and
`ramification_mul_finrank_divisionResidue`, all of which are already in the tree.  That is a
self-contained chunk and it is what would upgrade `card_relative_le_finrank_local` of §0.38(a) to
an equality, i.e. to local reciprocity.

---

## 0.40 Status (2026-08-30, later still) — the glue is closed: genuine decomposition subgroups of `G_k`

The "one shared glue lemma" that §0.36 rows 2 and 3 and §0.37(a) both deferred is now a theorem.

### (a) The obstruction, restated

`sha1`/`sha2` (`CFT/Profinite/Res.lean`) are stated for an abstract family `S : Set (Subgroup G)`,
while `HasseLevel`/`HasseInflation` quantify over `levelDecompositionSet L` — the automorphisms
whose *restriction to a finite level* fixes a place *of that level*.  A local-global principle
produces the first shape, not the second.  Matching them needs genuine decomposition subgroups of
`G_k` itself, i.e. primes of the ring of integers of the (infinite) top field and transitivity of
the Galois action on them.

### (b) `CFT/Units/InfiniteDecomposition.lean`

`NumberField.RingOfIntegers K = integralClosure ℤ K` is defined for *any* field, with no
`NumberField` hypothesis, and Mathlib already supplies the whole `𝓞`-functoriality package for
infinite extensions (`inst_ringOfIntegersAlgebra`, `inst_isScalarTower`,
`extension_algebra_isIntegral`, `ker_algebraMap_eq_bot`, and the `MulSemiringAction G (𝓞 K)`
instance).  So the primes are there; what has to be proven is transitivity.

* `under_smul_ringOfIntegers` — the prime of a subfield below a moved prime is the moved prime
  below, for raw ideals and with no finiteness anywhere (the `HeightOneSpectrum` version in
  `Units/PlaceRestrict.lean` needs `NumberField K`).
* `isInvariant_ringOfIntegers_of_isGalois` — `Algebra.IsInvariant (𝓞 F) (𝓞 K) Gal(K/F)` for an
  *arbitrary* Galois `K/F`, via `InfiniteGalois.mem_range_algebraMap_iff_fixed` (Mathlib's
  `Algebra.isInvariant_of_isGalois` wants `FiniteDimensional`).
* `smulCommClass_ringOfIntegers`, `continuousSMul_ringOfIntegers` — the two side conditions; the
  second is `continuousSMul_iff_stabilizer_isOpen` plus `stabilizer_isOpen_of_isIntegral`, i.e. the
  Krull topology.
* `exists_smul_eq_of_under_eq_ringOfIntegers` — **the Galois group of an arbitrary Galois extension
  acts transitively on the primes of its integers above a prime of the base.**  This is Mathlib's
  `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` (`RingTheory/Invariant/Profinite.lean`),
  which does the whole compactness / inverse-limit argument; the work here was assembling its five
  hypotheses for `𝓞 K` with the discrete topology.
* `exists_stabilizer_prime_restrictNormalHom_eq` — **an automorphism of a level fixing a place
  there is the restriction of an automorphism fixing a prime above**: lift by
  `restrictNormalHom_surjective_level`, then correct by an element of `Gal(K/L)` using
  transitivity.  This is the actual glue.
* `finiteDecompositionSubgroups k K` and `finiteDecompositionSubgroupsOutside k K S` — the
  stabilisers of the nonzero primes of `𝓞 K` (with the place below avoiding `S`).  `P ≠ ⊥` is part
  of the definition on purpose: `stabilizer ⊥ = ⊤`, so admitting `⊥` would wrongly strengthen the
  `sha1` hypothesis.
* `eq_one_of_finiteDecomposition`, `eq_one_of_finiteDecompositionOutside` — **a homomorphism into a
  commutative group killing a level and every decomposition subgroup is trivial.**
* `eq_one_of_mem_sha1`, `eq_one_of_mem_sha1_outside` — **`Ш¹(G_k, M) = 0` for trivial coefficients,
  with `Ш¹` taken over the genuine decomposition subgroups**, the class being reduced to a level by
  `exists_isGalois_smooth₁` and the cocycle to a homomorphism by `Profinite/Trivial.lean`.

### (c) `CFT/Units/HasseDecomposition.lean`

The bridge to the consumer.  `HasseInflation`'s `exists_galInflH1_eq_of_forall_level_outside` works
relative to the base `↥F` (the finite Galois level trivialising the coefficients), with
`L : IntermediateField ↥F K`; and `ρ • P = P` for `ρ : K ≃ₐ[↥F] K` says exactly that
`ρ ∈ stabilizer Gal(K/↥F) P`.  So the decomposition-subgroup hypothesis is fed straight in:

* `eq_one_of_finiteDecompositionOutside_over`, and
* `exists_galInflH1_eq_of_finiteDecomposition` /
  `exists_galInflH1_eq_of_finiteDecompositionOutside` — **a class dying on the stabiliser of every
  nonzero prime of `𝓞 K` is inflated from the field trivialising its coefficients**, with no level
  left in the hypothesis.

### (d) The table, updated again

Rows 1, 2, 3 are now laid **without** the glue caveat, and row 4 is laid in the shape consumed.
The remaining bricks are unchanged: row 4's leftover `inv_M ∘ res = [M:K]·inv_K`, row 6 (the `p`-th
power Hilbert symbol over a number field and its product formula), row 8, row 9 — and the two
walls, row 5 (**Poitou–Tate global duality**, `Ш²(k,A) ≅ Ш¹(k,A′)^∨`) and row 7 (**Chebotarev
density over a number field**).

Phase 1 is the finite places only; `levelDecompositionSetOutside` never mentions the archimedean
ones, so nothing was lost *in degree one*.

> **Correction (see §0.42).**  The last sentence of this subsection originally read that
> archimedean decomposition subgroups of `G_k` "are not needed by anything downstream".  That is
> false in degree two: `IsLocallySplitLevel` is a *conjunction* of an archimedean clause and a
> finite clause, so the degree-two glue needs the archimedean half as well.  It is built in §0.42.

---

## 0.41 Status (2026-08-30, night) — **wall #2 falls for odd `p`**: Theorem 13 only needs Frobenius *up to a scalar*

### (a) The analytic floor over a general base

Two modules carry the density argument of `NumberTheory/SplitDensity.lean` from the base `ℚ` to an
arbitrary number field `k`.

* `InverseGalois/NumberTheory/RelativeSplitDensity.lean` — `idealSum`, `HasIdealDensity`, the
  fibre decomposition of `log ζ_L(s)` over the primes of the base, and the three headline
  statements `hasIdealDensity_relSplitSet` (the primes of `k` splitting completely in a Galois
  `L|k` of degree `n` have Dirichlet density `1/n`), `infinite_relSplitSet`, and
  `infinite_setOf_splitsCompletelyIn_not_splitsCompletelyIn`.
* `InverseGalois/CFT/RelativeFrobenius.lean` — the decomposition dictionary at the base `k`:
  `card_relStabilizer`, `relInertia_eq_bot_iff_isUnramifiedAt`, `relStabilizer_eq_bot_iff`,
  `relStabilizer_eq_zpowers_arithFrobAt`, the restriction lemmas
  `relAlgebraMap_smul_restrictNormal` / `relRestrictNormal_mem_stabilizer`, and
  `relStabilizer_le_of_splitsCompletelyIn`.

Their combination is

```
exists_relStabilizer_eq_zpowers :
  (Subgroup.zpowers σ).Normal → (orderOf σ).Prime → ∀ T : Finset (HeightOneSpectrum (𝓞 k)),
    ∃ v ∉ T, v ∉ relRamifiedSet k L, ∃ P over v,
      MulAction.stabilizer Gal(L/k) P = Subgroup.zpowers σ ∧
      Subgroup.zpowers (arithFrobAt (𝓞 k) Gal(L/k) P) = Subgroup.zpowers σ
```

— for `σ` of prime order generating a normal subgroup, the decomposition group at infinitely many
primes of the base is exactly `⟨σ⟩`, and the Frobenius there generates `⟨σ⟩`.  It is **not** the
statement `Frob_P = σ`: what is produced is `Frob_P = σ^j` for an uncontrolled `j ≢ 0 mod p`.

### (b) The ambiguity is not removable by splitting conditions

"Splits completely in `F`" is the condition `Frob ∈ Gal(M|F)`, i.e. membership in a *subgroup*.
Every subgroup of an abelian `A` containing `σ` contains every `jσ`, so no boolean combination of
complete-splitting conditions — in `M` or in any larger field, since the constraint sets pull back
to subgroups — separates `σ` from `jσ`.  Nor does a nonabelian crossing help: for
`G = A ⋊ ⟨c⟩` with `c` acting on `A ≅ 𝔽_p^d` by a generator of `𝔽_p^×`, the conjugacy class of `σ`
is exactly `{jσ : j ≠ 0}`.  Pinning a single `Frob` is therefore equivalent to genuine Chebotarev,
which needs `L(1, χ) ≠ 0` for `χ` of order `p`; for `p = 2` the ratio `ζ_M/ζ_k` gives it, for
`p = 3, 4, 6` the pair `|L(s,χ)|²` does, and for `p ≥ 5` there is no escape from analytic
continuation of Hecke `L`-series (which needs the ideal count with error term `O(x^{1-1/d})`, not
in Mathlib).

### (c) But Schmidt–Wingberg's Theorem 13 does not need it

Reading the proof (arXiv `math/9809211`, pp. 14–16) line by line: the odd-`p` half constructs a
sequence `z_1, z_2, … ∈ H¹(k_S|K, μ_p)` with

```
(1)  ∃ 𝔓_i ∈ S ∖ T(K) with (z_i)_{𝔓_i} ≡ Frob_{𝔓_i} mod H¹_nr(K_{𝔓_i}, μ_p),
                       and (z_i)_𝔓 ∈ H¹_nr(K_𝔓, μ_p) for all 𝔓 ≠ 𝔓_i,
(2)  (z_i)_𝔓 = ½ y_𝔓 for 𝔓 ∈ T(K),
(3)  (z_{n+1})_{σ𝔓_i} = −(z_i)_{σ𝔓_i} for i ≤ n and all σ ∈ G(K|k) ∖ {1},
```

the prime `𝔓_{n+1}` being produced by "using Čebotarev's density theorem, we can choose a prime
`𝔓_{n+1} ∈ S ∖ T_n(K)` such that the image of `−ξ` in `H¹(k_{T_n}|K, ℤ/pℤ)^∨` is equal to
`Frob_{𝔓_{n+1}}`".

`H¹(K_𝔓, μ_p)/H¹_nr` is **cyclic of order `p`** (local duality: it is dual to
`H¹_nr(K_𝔓, ℤ/p) = ℤ/p`), and the map to `H¹(k_{T_n}|K, ℤ/pℤ)^∨ ≅ Gal(k_{T_n}|K)` sends its
canonical generator to `Frob_𝔓`.  So a prime with `Frob_𝔓 = λ·(image of −ξ)`, `λ ≠ 0`, is just as
good: put `λ^{-1}` times the generator in the `𝔓`-slot, and the exactness of the upper line still
produces `z_{n+1}`.  Condition (1) weakens to

```
(1')  (z_i)_{𝔓_i} ≡ λ_i · Frob_{𝔓_i} mod H¹_nr,   λ_i ∈ 𝔽_p^×.
```

Propagate `λ` through the closing computation.  With `u = z_i(Frob_{σ𝔓_i})` and
`w = z_i(Frob_{σ𝔓_N})`, and using that the Hilbert symbol is bilinear:

| step | SW | with scalars |
| --- | --- | --- |
| `ψ` | `z_N(Frob_{σ𝔓_N}) = u` | unchanged |
| (1) for `z_i` | `(z_i, σz_i)_{σ𝔓_i} = u` | `= u^{λ_i}` |
| product formula | `(z_i, σz_i)_{𝔓_i} = u^{-1}` | `= u^{-λ_i}` |
| (3) | `(z_i, σz_N)_{𝔓_i} = u` | `= u^{λ_i}` |
| product formula | `(z_i, σz_N)_{σ𝔓_N} = u^{-1}` | `= u^{-λ_i}` |
| (1) for `z_N` | `= w` | `= w^{λ_N}` |

so `w^{λ_N} = u^{-λ_i}`, and what the proof needs is `w·u = 1`, i.e. `λ_i = λ_N`.  Nothing else in
the argument touches the normalization: the two product-formula steps use only the *support* of
`z_i` (the second bullet of (1)), and conditions (2), (3), (a), (b) are `λ`-free.

The scalars are then absorbed by the pigeonhole.  SW apply the shoe-box principle to
`ψ : {z_1, z_2, …} → μ_p^r` to get `i < N` with `ψ(z_i) = ψ(z_N)`; apply it instead to

```
z_i ↦ (ψ(z_i), λ_i) ∈ μ_p^r × 𝔽_p^×
```

— still a finite set, of size `p^r (p-1)` instead of `p^r` — and the pair `i < N` produced
satisfies `ψ(z_i) = ψ(z_N)` **and** `λ_i = λ_N`.  The proof goes through verbatim.

**Conclusion.**  For odd `p`, `exists_relStabilizer_eq_zpowers` is exactly the Chebotarev input
that Theorem 13 consumes.  Row 7 of the §0.36 table is closed on the odd side, with no `L`-series,
no ray-class groups and no analytic continuation.  (`Gal(k_{T_n}|K)` is a finite elementary abelian
`p`-group, so every nonzero element has order `p` and generates a normal subgroup — the two
hypotheses of the theorem.  The side condition `𝔓_{n+1} ∈ S = cs(Ω|k) ∪ T` is free: take
`L = k_{T_n}·Ω` and `σ` the element that is `ξ` on `k_{T_n}` and `1` on `Ω`, whereupon
`Frob ∈ ⟨σ⟩ ⊆ Gal(L|Ω)` forces complete splitting in `Ω` automatically.)

### (d) What is left of row 7

The `p = 2` half of Theorem 13 uses Chebotarev twice, and only one of the two is covered.

* Condition (1) at `p = 2` reads `(z_i)_{𝔓_i} ≡ Frob_{𝔓_i} mod H¹_nr(K_{𝔓_i}, μ_2)`, and
  `𝔽_2^× = {1}`: there is no scalar to absorb, and none is created, because
  `exists_relStabilizer_eq_zpowers` at `orderOf σ = 2` gives `Frob_P = σ` on the nose.  **Covered.**
* The Claim's proof needs: *"there exists a prime ideal `𝔔 ∉ T(K)` of `𝒪_{K,S_∞}` with
  `𝔔 ≠ σ𝔔` such that `𝔔 = 𝔄·(x)` with `x ∈ K^×`"* — i.e. **every ideal class of `Cl_{S_∞}(K)`
  contains a prime**, used to replace the fractional ideal `𝔄` in `(z̃_i) = 𝔓_i 𝔄²` by a prime, so
  that `z̃_i` and `σz̃_i` are coprime.  Here `[𝔔] = [𝔄]` is needed exactly: `𝔔² = 𝔄²(x²)` in the
  free abelian group of ideals forces `𝔔 = 𝔄(x)`.  `Cl_{S_∞}(K)` is an arbitrary finite abelian
  group, so this is *not* a prime-order statement and the scalar trick does not apply.  **Open.**
  Mathlib's `NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop` is the count of ideals of
  bounded norm in a fixed class — the *ideal* count, not the *prime* count; upgrading it is the
  non-vanishing `L(1, χ) ≠ 0` for an unramified class character.

So row 7 reduces to a single classical statement: **every ideal class of a number field contains
infinitely many prime ideals**.

---

## 0.42 Status (2026-08-31) — the degree-two glue is closed: `Ш²(k, μ_n) = 0` for the genuine decomposition subgroups of `G_k`

§0.38(c) named the one thing still open in row 3: `IsLocallySplitLevel` quantifies over the places
of a finite *level*, while membership in `sha2` is a statement about the decomposition subgroups of
`G_k` itself.  That glue is now a theorem, in both halves.

`IsLocallySplitLevel` (`Units/HasseTwo.lean`) is a **conjunction** — an archimedean clause over
`InfinitePlace ↥L` and a finite clause over `HeightOneSpectrum (𝓞 ↥L)` — so closing it required
building the archimedean mirror of the whole finite tower, not just the finite half.  This is where
the last sentence of §0.40 was wrong.

### (a) The finite half — `Units/TowerDescent.lean`, `Units/HasseTwoDecomposition.lean`

For a tower `k ⊆ F ⊆ K` of number fields and a prime `v` of `K`, a local coboundary of the
decomposition group at `v` with values in `(v.adicCompletion K)ˣ` descends to one of the
decomposition group at the prime below with values in the completion of `F`
(`exists_sub_add_eq_adicUnits_descent`).  The three inputs are: the decomposition group at `v` maps
*onto* the one below (`stabilizerRestrictPlaceFinite_surjective`), the kernel is the automorphisms
fixing `F`, and Hilbert 90 for that kernel (`Units/CompletionHilbert90.lean`) together with the
abstract descent of a 2-coboundary along a surjection (`GroupCohomology/CoboundaryDescent.lean`).

`exists_sub_add_eq_adicUnits_of_resH2` then goes from `sha2` to the local condition at a finite
place of a level: pick a prime `P` of `𝓞 Ω` above the place, take the trivialising cochain of
`stabilizer Gal(Ω/k) P`, use its *smoothness* to make it constant on the automorphisms fixing some
finite Galois `E₀`, enlarge the level to `E ⊔ E₀`, descend the cochain along the surjection onto
the decomposition group of that level, and finally descend the tower `k ⊆ E ⊆ E''`.

### (b) The archimedean half — `Units/InfiniteHilbert90.lean`, `Units/InfiniteTowerDescent.lean`

The same four steps, with `HeightOneSpectrum` replaced by `InfinitePlace` and `adicCompletion` by
`InfinitePlace.Completion`:

* `stabilizerAlgEquivInfinite` — **the decomposition group at an infinite place *is* the
  automorphism group of the completion there**, `↥(stabilizer Gal(K/k) w) ≃* (w.Completion ≃ₐ[…] …)`.
  This is what makes Hilbert 90 available: a subgroup `S` of it is the Galois group of `w.Completion`
  over the fixed field of the image, a *finite* extension, so
  `isMulCoboundary₁_of_isMulCocycle₁_stabilizerInfinite` is Mathlib's Hilbert 90 read through that
  isomorphism.
* `stabilizerRestrictPlaceInfinite_surjective` — surjectivity onto the decomposition group at the
  place below, from `NumberField.InfinitePlace.exists_smul_eq_of_comap_eq` (which needs no
  `NumberField` instance, so it also applies over an infinite `Ω`).
* `exists_infiniteUnitsComapHom_eq_of_ker` — the units of `w.Completion` fixed by the whole
  decomposition group over `F` are the units of the completion of `F`.
* `exists_sub_add_eq_infiniteUnits_descent` — the descent, assembled from the same abstract lemma.

`Units/InfiniteDecomposition.lean` gains `infiniteDecompositionSubgroups k Ω`, the archimedean
counterpart of `finiteDecompositionSubgroups`, and `Units/HasseTwoDecomposition.lean` gains the
`RestrictInfinitePlace` section and `exists_sub_add_eq_infiniteUnits_of_resH2`.

### (c) The assembly

```lean
theorem eq_one_of_mem_sha2 {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (htriv : ∀ (g : Gal(Ω/k)) (m : M), g • m = m)
    {ι : M →* kˣ} (hιinj : Function.Injective ι) (hιpow : ∀ m : M, ι m ^ n = 1)
    (hιsurj : ∀ y : kˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (z : SmoothH2 Gal(Ω/k) M)
    (hz : z ∈ sha2 M (finiteDecompositionSubgroups k Ω ∪ infiniteDecompositionSubgroups k Ω)) :
    z = 1
```

for `Ω` an algebraic closure of the number field `k` and `M` a `G_k`-trivial group of `n`-th roots
of unity.  A class of `sha2` is represented by a cocycle inflated from a finite Galois level; the
two bridge theorems turn the vanishing on the two families of decomposition subgroups into the two
clauses of `IsLocallySplitLevel` for that representative; and
`eq_one_of_forall_isLocallySplitLevel` (Albert–Brauer–Hasse–Noether plus Kummer theory) finishes.

So **row 3 is done**: `Ш²(k, μ_n) = 0` in the form the downstream Hochschild–Serre argument needs,
stated for the genuine decomposition subgroups of `G_k` and with no hypothesis left.

**Cost.** `Units/InfiniteTowerDescent.lean` needs `maxHeartbeats 4000000` on its headline theorem
and takes ~11 min to compile on its own; the pathology is instance search on `(w.Completion)ˣ`
(failing `Ring`/`AddCommGroup`/`LieRing` searches), the same one the three shortcut instances in
`Units/InfiniteHilbert90.lean` were introduced to cure.

Build: 9444 jobs green, zero warnings, zero sorries outside the comparator.

**What is left** is unchanged from §0.41: rows 5 and 8 (Poitou–Tate global duality), row 6 (the
`p`-th power Hilbert symbol and the product formula), row 7 (Chebotarev / "every ideal class
contains infinitely many primes", needed for `p = 2` only), and row 9 (the Schmidt–Wingberg
Theorem 13/14/15 assembly).

---

## 0.43 Status (2026-08-31) — cup products in low degrees

Two corrections to the §0.36 table first.

* **Row 4 is finished, not partial.**  The cell says "what is left of the row is
  `inv_M ∘ res = [M:K] · inv_K`".  That is exactly `localInvariant_baseChange` in
  `CFT/Brauer/LocalInvariantRestrict.lean`, together with `restrictScalars_divisionFrobenius`.
  Nothing is left of row 4.
* **The general-base class formation of §0.36(a) is not "bounded, mechanical".**
  `CFT/Units/IdeleQuotCyclic.lean` carries `[IsPrincipalIdealRing (𝓞 k)]` on
  `forall_mem_multiples_ideleQuot`, `addOrderOf_ideleQuot_eq`,
  `exists_addOrderOf_H2_ideleClassRep_eq` and
  `exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep`, and the class group is a genuine obstruction, not
  a convenience.  What *is* unconditional in `k` is the **order**: `first_inequality_index`
  (`Units/IdeleClassIndex.lean`), `card_tateModule_resObj_ideleClassRep_two_le`
  (`Units/IdeleClassTate.lean`) and the periodicity `tateH0AddEquivH2` give
  `#Ĥ⁰(Gal(F|k), C_F) = n` with no hypothesis; only the *cyclicity* of that group uses the
  principal-ideal hypothesis.  The repair is to work with `S`-ideles for a finite set `T` of primes
  generating `Cl(k)` and to choose the auxiliary prime `q` so that every `v ∈ T` splits completely
  in `F`, i.e. `q` split completely in `K · ℚ(ζ_{2n}) · ∏_{v ∈ T} ℚ(ζ_n, (Nv)^{1/n})`.

### The brick

Rows 5, 6 and 8 all consume cup products, and **neither Mathlib v4.28 nor this repository had
any** (`grep -ri cup Mathlib/RepresentationTheory/` is empty).
`CFT/GroupCohomology/Cup.lean` supplies them in the two degrees that matter, without the monoidal
structure on `Rep k G`: instead of a tensor product of representations the input is an equivariant
bilinear pairing of the coefficients,

```lean
(Φ : A →ₗ[k] B →ₗ[k] C) (hΦ : ∀ g a b, Φ (A.ρ g a) (B.ρ g b) = C.ρ g (Φ a b))
```

and the product of two `1`-cochains is

```lean
cup₁₁ Φ f₁ f₂ = fun p => Φ (f₁ p.1) (B.ρ p.1 (f₂ p.2))
```

matching Mathlib's sign conventions for `d₀₁`, `d₁₂`, `d₂₃`.  The three computations are
`cup₁₁_mem_cocycles₂` (a product of cocycles is a cocycle), and
`cup₁₁_mem_coboundaries₂_left` / `_right` (a product with a coboundary is a coboundary), the latter
two with explicit primitives `y ↦ Φ a (f₂ y)` and `x ↦ -Φ (f₁ x) (B.ρ x b)`.  Descending through
`Submodule.liftQ` twice gives

```lean
cupH1 Φ hΦ : H1 A →ₗ[k] H1 B →ₗ[k] H2 C
cupH1_apply : cupH1 Φ hΦ (H1π A f₁) (H1π B f₂) = H2π C (cupCocycles₁₁ A B Φ hΦ f₁ f₂)
```

Note for the consumer: this is the **`Rep k G` / finite-level** flavour.  The profinite layer
(`CFT/Profinite/Cochain.lean`) is multiplicative — `IsMulCocycle₁`/`IsMulCocycle₂` and
`SmoothH1`/`SmoothH2` — so a multiplicative, smoothness-preserving mirror will be needed before the
Hilbert symbol can be written as `H¹(G_K, μ_p) × H¹(G_K, μ_p) → H²(G_K, μ_p)`.  Smoothness is the
easy half: the product of two cochains constant on the cosets of `N` and `N'` is constant on the
cosets of `N ⊓ N'`, which is `IsOpenNormal.inf`.

Build: 9445 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.44 Status (2026-08-31, later) — the profinite cup product, and `H¹(G_k, μ_n) = kˣ/(kˣ)ⁿ`

The mirror that §0.43 asked for is built, and with it the first cohomology of an *infinite* Galois
group is now computed, not merely defined.  Five modules, all sorry- and axiom-free.

### (a) `CFT/Profinite/Cup.lean` — the multiplicative cup product

The input is a pairing `Φ : M → M' → M''` of the coefficients of three smooth modules,
multiplicative in each variable and compatible with the three actions, and the product of two
`1`-cochains is

```lean
mulCup₁₁ Φ u v = fun p => Φ (u p.1) (p.1 • v p.2)
```

with `isMulCocycle₂_mulCup₁₁`, `isSmooth₂_mulCup₁₁` (the subgroup at which the product is constant
is the intersection of the three subgroups for the two factors and the action — `IsOpenNormal.inf`,
exactly as predicted), and `mulCup₁₁_mem_smoothCoboundary₂_left`/`_right` with explicit primitives.
Descending gives

```lean
cupSmoothH1 Φ hΦ : SmoothH1 G M → SmoothH1 G M' →* SmoothH2 G M''
```

`comapH2_cupSmoothH1` makes it commute with pullback along any smooth homomorphism, hence
`resH2_cupSmoothH1` with restriction to a subgroup, hence `cupSmoothH1_mem_sha2_left`/`_right`:
**a cup product one of whose factors is everywhere locally trivial is everywhere locally trivial.**
That is the shape in which the Hilbert symbol will be consumed.

### (b) `CFT/Profinite/Hilbert90.lean` — Hilbert 90 for an infinite Galois group

`isMulCoboundary₁_of_isMulCocycle₁_smooth`: a *smooth* `1`-cocycle of `Gal(Ω|k)` with values in
`Ωˣ` is the coboundary of a single unit; hence `subsingleton_smoothH1_units`.  The reduction to the
finite case is the only interesting step and it is short: a smooth cochain is constant on the
cosets of an open normal subgroup, the fixing subgroups of the finite Galois levels are cofinal
among those (`exists_fixingSubgroup_le`, §0.40), and the values of a cocycle constant on the cosets
of `E.fixingSubgroup` are *fixed* by that subgroup, so by `InfiniteGalois.fixedField_fixingSubgroup`
they lie in `E` itself.  Choosing a preimage of each automorphism of `E` turns the cocycle into a
cocycle of the finite level, Noether's form supplies a primitive there, and the primitive works
upstairs unchanged because every automorphism of `Ω` acts on `E` through its restriction.

### (c) `CFT/Profinite/Kummer.lean` — the two directions

With a primitive `n`-th root of unity in the base, the coefficients are an abstract `M` mapping
into `kˣ` by `ι` with image the `n`-th roots of unity — deliberately the *same* convention as
`eq_one_of_mem_sha2` (row 3), so the two layers compose.

* `exists_isMulCocycle₁_kummer`: if `β ^ n = a` with `a ∈ kˣ` then `σ ↦ σ • β / β` has values in
  the `n`-th roots of unity of the base, and the resulting `M`-valued cochain is a *smooth*
  cocycle.  Smoothness is where the infinite case differs from the finite one, and it comes from
  `exists_isOpenNormal_forall_apply_eq`: a single element of `Ω` is fixed by the subgroup fixing
  the normal closure of the field it generates, which is open because that closure is finite.
* `exists_pow_eq_of_isMulCocycle₁`: conversely, Hilbert 90 turns a smooth cocycle into a radical
  `β`, and `β ^ n` is fixed by everything, hence lies in the base.
* `smoothH1Mk_eq_one_iff_exists_pow`: the class is trivial exactly when the radicand is already an
  `n`-th power in the base.

### (d) `CFT/Profinite/KummerHom.lean` — the isomorphism

`IsKummerData k Ω M ι n` bundles the five hypotheses (a primitive root in `k`, the trivial action
on `M`, `ι` injective with image the `n`-th roots of unity, and an `n`-th root in `Ω` of every unit
of `k`).  Two roots of the same unit differ by a root of unity of the base, which every
automorphism fixes, so `smul_div_eq_of_pow_eq` says the coboundary does not depend on the root; and
a cocycle is determined by its coboundary because `ι` is injective.  So `cochain` is well defined,
`cochain_mul` is multiplicative, and

```lean
kummerHom      : kˣ →* SmoothH1 Gal(Ω/k) M
ker_kummerHom  : kummerHom.ker = (powMonoidHom n).range
kummerHom_surjective
kummerEquiv    : kˣ ⧸ (powMonoidHom n : kˣ →* kˣ).range ≃* SmoothH1 Gal(Ω/k) M
```

**Non-vacuity was a genuine risk** and is now closed.  A grep showed that the abstract-`M`-with-`ι`
convention introduced by row 3 had never once been instantiated, so the entire layer could have
been about an empty class of data.  `isKummerData_rootsOfUnity` supplies the witness — `M` is
`rootsOfUnity n k` with the trivial action (`rootsOfUnityTrivialAction`, kept a `def` rather than a
global instance to avoid an instance diamond on `Gal(Ω/k)`-actions), and `exists_units_pow_eq`
supplies the roots whenever `Ω` is algebraically closed.

### (e) `CFT/Profinite/KummerRes.lean` — restriction, and Ш¹ in Kummer terms

The point of the whole layer.  The cochain of `a` measures how far a chosen root is from being
fixed, and because the action on the coefficients is trivial a cocycle is a coboundary on a
subgroup exactly when it *vanishes* there.  So

```lean
resH1_kummerClass_eq_one_iff_smul_root : resH1 D (h.kummerClass a) = 1 ↔ ∀ d ∈ D, d • h.root a = h.root a
resH1_kummerClass_eq_one_iff_mem_fixedField :
  resH1 D (h.kummerClass a) = 1 ↔ ∃ b ∈ IntermediateField.fixedField D, b ^ n = algebraMap k Ω a
resH1_fixingSubgroup_kummerClass_eq_one_iff :
  resH1 E.fixingSubgroup (h.kummerClass a) = 1 ↔ ∃ b : ↥E, (b : Ω) ^ n = algebraMap k Ω a
```

No closedness hypothesis on `D` is needed: the fixed field is taken as it stands, and the
intermediate-field form follows from `InfiniteGalois.fixedField_fixingSubgroup`.  Over a family `S`
of subgroups this reads off the everywhere locally trivial classes: `localPowers S` is the subgroup
of `kˣ` of units that are `n`-th powers in the field fixed by every `D ∈ S`, and

```lean
map_localPowers : (h.localPowers S).map h.kummerHom = sha1 M S
```

For `S` the genuine decomposition subgroups of `G_k` (`decompositionSubgroups`, §0.40) this is
exactly **`Ш¹(k, μ_n) = {a ∈ kˣ : a is locally an n-th power} / (kˣ)ⁿ`**, which is the object the
dual of row 5 has to be paired with, and the object Theorem 13 of Schmidt–Wingberg computes.

### What this does and does not unlock

It does *not* touch rows 5 and 8: Poitou–Tate is still wall #1.  What it does is make rows 6 and 9
writable in the same language as row 3.  The remaining piece for the Hilbert symbol itself is the
**invariant map on `SmoothH2`** — the repository has `localInvariant` only at the finite level
(`CFT/Brauer/LocalInvariant.lean`), and the bridge `SmoothH2 G_K Ωˣ ≅ Br(K)` does not exist.
Building it needs one compatibility that a search of the 81 modules of `CFT/Brauer/` did not turn
up: that the crossed product of an *inflated* cocycle (same base, larger splitting field) has the
same Brauer class, i.e. `(Ω_E/K, inf f) ≅ M_{[E:L]}((L/K, f))`.  That is the next brick on this
line.

Build: 9450 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.45 Status (2026-08-31, night) — Ш² restricts to a larger base, and inflation preserves the Brauer class

Two bricks, and one correction to the §0.26 table.

### (a) `CFT/Units/DecompositionRestrict.lean` — step 1 of the narrowed route of §0.26

§0.26 narrowed the remaining route to: *first* show that an everywhere locally trivial class over
`k` dies after passing to a base that contains the roots of unity, *then* feed that into
Hochschild–Serre.  Step 1 is now a theorem.  Three pieces:

* `continuous_galRestrictScalarsHom` — an automorphism of `Ω` over an intermediate field `k ⊆ K` is
  in particular one over `k`, and that inclusion `Gal(Ω/K) → Gal(Ω/k)` is *continuous* for the
  Krull topologies.  The proof is the only one with content: a finite subextension `E/k` is
  finitely generated (`IntermediateField.essFiniteType_iff` is the practical route to `E.FG`),
  adjoining generators to `K` gives a finite subextension of `Ω/K`, and an automorphism fixing the
  latter fixes `E` pointwise because `E` lands in the fixed field of the group it generates.
* `decompositionSubgroups_le_galRestrictScalarsHom` — a prime of `𝓞 Ω` and an archimedean place of
  `Ω` are *the same objects* whichever base one works over, and the two stabilizer conditions are
  literally the same proposition, so each decomposition subgroup over `K` sits inside the
  corresponding one over `k`.  Both cases are `rw [mem_stabilizer_iff] at hx ⊢; exact hx`.
* `comapH2_mem_sha2_decompositionSubgroups` (and its degree-one twin) — feeding those two into
  `comapH2_mem_sha2` (§0.40): **Ш²(k, ·) restricts into Ш²(K, ·)**.

Composing with row 3 gives the statement the route asked for:

```lean
theorem eq_one_of_mem_sha2_of_isPrimitiveRoot_intermediate … :
    comapH2 (galRestrictScalarsHom k K Ω) hπ (isSmoothHom_galRestrictScalarsHom k K Ω) z = 1
```

so `Ш²(k, M) ⊆ ker(H²(k, M) → H²(K, M))` whenever `K` contains the `n`-th roots of unity.

**Correction to the §0.26 table.**  Four of its rows are stale.  "the fundamental class of a class
formation", "Tate's cohomological triviality theorem", "Tate–Nakayama" and "cup products" were all
listed as *absent*; `baseFundamentalClass`, `baseTateEquiv`, `baseTateNakayamaEquiv` and
`baseArtinEquiv` landed in `74e3a6d` (§0.35–§0.36) and `CFT/Profinite/Cup.lean` in §0.44.  The
residual obstacle in that direction is narrower than the table suggests: the `Module.Flat ℤ`
hypothesis on the coefficients, which `p`-torsion modules do not satisfy (§0.28).

### (b) `CFT/Brauer/CrossedProductInflate.lean` — the brick §0.44 named

§0.44 ended by naming the missing compatibility for the bridge `SmoothH2 G_K Ωˣ ≅ Br(K)`: that
inflating a cocycle to a larger splitting field does not change the Brauer class.  That is now a
theorem.

For a tower `K ⊆ L ⊆ L'` of finite Galois extensions, the inflation of `f : Gal(L/K)² → Lˣ` is

```lean
inflateCocycle L' f = fun p => Units.map (algebraMap L L')
  (f (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2))
```

and it is a cocycle by a transport lemma stated for an arbitrary pair of a group homomorphism and
an equivariant coefficient homomorphism (`isMulCocycle₂_comp`), instantiated at
`AlgEquiv.restrictNormalHom L` and `Units.map (algebraMap L L')`; the equivariance
`smul_units_map_algebraMap` is `AlgEquiv.restrictNormal_commutes` wrapped in `Units.ext`.

The recognition theorem is the `CyclicTower.lean` pattern run for an arbitrary Galois group instead
of a cyclic one, and it reuses that file's `coordMatrix` toolkit verbatim.  Given a simple algebra
`A` of dimension `[L : K]²` containing `L` via `emb` together with units `u σ` conjugating it by
`Gal(L/K)` and multiplying by `f`, and a basis `b : Basis ι L L'`, put

```lean
W σ = emb.mapMatrix (coordMatrix b fun j => σ (b j)) * diagonal (fun _ => u (σ.restrictNormal L))
```

inside `Matrix ι ι A`.  Two facts make these the symbols of the inflated cocycle:
`coordMatrix_map`, which says `S (σ * τ) = S σ * (S τ).map (σ|_L)` — that is exactly the semilinear
cocycle identity the change-of-basis matrices satisfy — and `hDcomm`, which says the diagonal of a
symbol conjugates matrix entries by the restriction.  A dimension count
`finrank K (Matrix ι ι A) = [L:K]² · |ι|² = [L':K]²` then lets
`crossedProductAlgHom_bijective` (§0.36's recognition API) conclude:

```lean
nonempty_algEquiv_matrix_inflateCocycle :
  Nonempty (CrossedProduct (isMulCocycle₂_inflateCocycle (L' := L') hf) ≃ₐ[K]
    Matrix (Fin (finrank L L')) (Fin (finrank L L')) A)
```

Applying it to `A = CrossedProduct hf` itself, with `emb = inclAlgHom hf` and the symbols
`unitSymbol hf g = (isUnit_single_one hf g).unit`, gives the headline

```lean
mk_csa_inflateCocycle (hf : IsMulCocycle₂ f) :
  (⟦csa (isMulCocycle₂_inflateCocycle (L' := L') hf)⟧ : BrauerGroup K) = ⟦csa hf⟧
```

i.e. `(L'/K, inf f) ≅ M_{[L':L]}((L/K, f))` in the Brauer group.  This is the cyclic
`cyclicBrauerHom_restrictNormal` of `CyclicTower.lean` with the cyclicity dropped.

**Lean note.**  `crossedProductAlgHom` and `crossedProductAlgHom_bijective` live in a
`variable {K L A : Type u}` block, so the target algebra must be in the *same* universe as `K`.
Declaring the index type `{ι : Type*}` makes `Matrix ι ι A : Type (max u u_1)` and the application
fails on universes; `{ι : Type}` (so `max 0 0 u = u`) is the fix, and it costs nothing because the
only instantiation is `Fin (finrank L L')`.

### What is left

Unchanged: rows 5 and 8 (Poitou–Tate global duality, wall #1), row 6 (the `p`-th power Hilbert
symbol and the product formula), row 7 (Chebotarev, `p = 2` only), row 9 (the Schmidt–Wingberg
Theorem 13/14/15 assembly).  On the row-6 line the next step is now the colimit itself:
`colim_L H²(Gal(L/K), Lˣ) ≅ colim_L Br(L/K) = Br(K)`, for which (b) supplies the compatibility that
makes the maps of the colimit system well defined, and then the composite with `localInvariantHom`
is the invariant map on `SmoothH2`.

Build: 9454 jobs green, zero warnings, zero sorries outside the comparator; the new headline has
axioms `[propext, Classical.choice, Quot.sound]`.

---

## 0.46 Status (2026-08-31, late night) — the colimit: `SmoothH2(G_k, Ωˣ) ↪ Br(k)`

§0.45(b) supplied the compatibility; this section builds the map it makes well defined.  The
statement is the one the row-6 line asked for:

```lean
smoothBrauerHom : SmoothH2 Gal(Ω/k) Ωˣ →* BrauerGroup k
smoothBrauerHom_injective : Function.Injective (smoothBrauerHom (k := k) (K := Ω))
```

for an arbitrary Galois extension `Ω/k` (no finiteness anywhere).  Three files moved.

### (a) `CFT/Profinite/Cochain.lean` — three quotient lemmas

`smoothH2Mk` is a `QuotientGroup.mk` of a subtype, so the three obvious facts about it were
missing and every one of them is needed below:

* `smoothH2Mk_congr` — equal cocycles have equal classes (a `subst` + `rfl`; it exists only to
  avoid dependent rewriting, since the proof arguments change type when the cocycle does);
* `smoothH2Mk_eq_iff` — **two classes agree exactly when the quotient of the cocycles is the
  coboundary of a *smooth* cochain**, via `QuotientGroup.eq` and `Subgroup.mem_subgroupOf`
  followed by a `show` that turns the subgroup membership `b⁻¹ * a ∈ smoothCoboundary₂` into the
  pointwise `fun p => a p / b p`;
* `smoothH2Mk_eq_mul` — the same dodge for `smoothH2Mk_mul`.

### (b) `CFT/Brauer/InflateTower.lean` — transitivity of inflation, and the compositum trick

**Transitivity.**  For a tower `k ⊆ L ⊆ L' ⊆ K` of normal subfields,

```lean
inflateCocycle_trans (w : Gal(L/k)² → Lˣ) :
  inflateCocycle K (inflateCocycle L' w) = inflateCocycle K w
```

This is short because Mathlib already has the restriction half:
`IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply` (`FieldTheory/Normal/Defs.lean:245`) says
`σ|_L = (σ|_{L'})|_L`, so the proof is `Units.ext` plus a three-step `rw` ending in
`← IsScalarTower.algebraMap_apply`.

**Raising a level.**  The awkwardness in stating "compare two levels in their compositum" is that
`Algebra ↥E ↥F` for `E ≤ F` is *not* an instance — the two are intermediate fields of the same
`K`, not a tower.  Rather than introduce a global instance (which would clash with the ambient
`Algebra ↥E K`), the level-raising is packaged as an existential whose *statement* never mentions
the extra algebra, and the instances live inside the proof:

```lean
exists_cocycle_of_le (hEF : E ≤ F) (hw : IsMulCocycle₂ w) :
  ∃ v (hv : IsMulCocycle₂ v), inflateCocycle K v = inflateCocycle K w ∧
    (⟦CrossedProduct.csa hv⟧ : BrauerGroup k) = ⟦CrossedProduct.csa hw⟧
```

with `letI : Algebra ↥E ↥F := ((IntermediateField.inclusion hEF).toRingHom).toAlgebra` and both
scalar towers by `IsScalarTower.of_algebraMap_eq fun _ => rfl` — all three `rfl`s hold on the nose.
The witness is `inflateCocycle ↥F w`; the first conjunct is `inflateCocycle_trans` and the second
is §0.45(b)'s `mk_csa_inflateCocycle`.

**Well-definedness.**  With those two, the key comparison is a five-line proof: given cocycles at
levels `E₁, E₂` whose inflations to `K` have the same smooth class, raise both to `E₁ ⊔ E₂` (which
is finite and Galois over `k` by `IntermediateField.finiteDimensional_sup` and the repo's
`isGalois_sup`), read the hypothesis through `smoothH2Mk_eq_iff` to get a smooth cochain
trivialising the quotient, and feed it to `SmoothLevel.lean`'s
`isMulCoboundary₂_of_coboundary₂_inflateCocycle` — the descent of a smooth trivialisation to the
level — to conclude via `mk_csa_eq_mk_csa_iff`:

```lean
mk_csa_eq_mk_csa_of_smoothH2Mk_eq :
  … → (⟦CrossedProduct.csa hw₁⟧ : BrauerGroup k) = ⟦CrossedProduct.csa hw₂⟧
```

`existsUnique_mk_csa` then packages "every smooth class comes from some level"
(`exists_isGalois_levelCocycle₂`) with that uniqueness into an `∃!`, `smoothBrauer` is its
`choose`, and `mk_csa_eq_smoothBrauer` is the defining property.  Multiplicativity
(`smoothBrauer_mul`) is the same compositum argument once more: raise the two levels to
`E₁ ⊔ E₂`, note that inflation is multiplicative (`map_mul` of `Units.map`), and use
`CrossedProduct.mk_csa_mul`.  `MonoidHom.mk'` then avoids proving `map_one` separately.

**Injectivity.**  A cocycle at a finite level whose crossed product splits is a coboundary there
(`mk_csa_eq_one_iff`), and the inflation of that trivialising cochain — pull back along
`AlgEquiv.restrictNormalHom E` and push forward along `Units.map (algebraMap ↥E K)` — is smooth
(it is constant on the cosets of `E.fixingSubgroup`, which is open normal) with differential the
inflated coboundary.  So the class dies in `SmoothH2`:

```lean
smoothH2Mk_eq_one_of_mk_csa_eq_one (hw : IsMulCocycle₂ w)
    (h : (⟦CrossedProduct.csa hw⟧ : BrauerGroup k) = 1) :
  smoothH2Mk (inflateCocycle K w) … = 1
```

and `injective_iff_map_eq_one` plus `exists_isGalois_levelCocycle₂` finishes.

**Lean note.**  `isGalois_sup` already existed in `CFT/Compositum.lean` (proved by `inferInstance`);
declaring it again is a hard error, not a shadow.  The `omit`s the `unusedSectionVars` linter asked
for are all of `[IsGalois k K]`, plus `[FiniteDimensional k ↥E]` on the coboundary computation —
the `IsGalois k K` hypothesis is only needed for the *surjectivity* half (`exists_levelCocycle₂`),
never for inflation itself.

### What is left

Unchanged: rows 5 and 8 (Poitou–Tate, wall #1), row 7 (Chebotarev, `p = 2` only), row 9 (the
Schmidt–Wingberg 13/14/15 assembly).  On row 6 the remaining step is *surjectivity* of
`smoothBrauerHom` — every class of `Br(k)` is split by some finite Galois extension, which is
`H2Surjective.lean`'s `exists_brauerHom_eq` at each level, modulo its universe-0 restriction — and
then the composite with `localInvariantHom` is the invariant map on `SmoothH2`.

---

## 0.47 Status (2026-08-31, late night) — `H²(G_k, k̄ˣ) = Br(k)`, and `= ℚ/ℤ` for a local field

§0.46 built `smoothBrauerHom` and proved it injective.  It is also surjective, as soon as the top
field is an algebraic closure of a **perfect** field, and then the local invariant turns it into an
isomorphism with `ℚ/ℤ`.

### (a) `CFT/Brauer/SmoothBrauer.lean`

Two steps, both short because the pieces were already there.

* `exists_mk_csa_eq_of_mem_relative` — a `Type u` restatement of `H2Surjective.lean`'s
  `exists_brauerHom_eq`, avoiding that file's universe-0 restriction.  The restriction came from
  `brauerHom`, which the statement need not mention: `exists_csa_finrank_sq_of_mem_relative`
  (`SplittingSubfield.lean`) and `exists_algEquiv_crossedProduct_of_finrank_sq`
  (`CrossedProductRecognition.lean`) are both stated in `Type u`, and chaining them directly gives
  `∃ c (hc : IsMulCocycle₂ c), ⟦CrossedProduct.csa hc⟧ = x`.
* `smoothBrauerHom_surjective` — `GaloisSplitting.lean`'s `exists_isGalois_mem_relative` produces a
  finite Galois level `E ⊆ k̄` splitting the class, the previous bullet produces a cocycle there,
  and `mk_csa_eq_smoothBrauer E hc rfl` identifies its inflation's smooth class as a preimage.

Hence

```lean
smoothBrauerEquiv (k) [PerfectField k] :
  SmoothH2 Gal(AlgebraicClosure k/k) (AlgebraicClosure k)ˣ ≃* BrauerGroup k
```

**The Brauer group of a perfect field is the smooth second cohomology of its absolute Galois
group.**  Note `smoothBrauerHom` elaborates at `BrauerGroup.{u, u}`, which is what
`localInvariantEquiv` (stated at `BrauerGroup.{0, 0}`) needs when `k : Type`.

### (b) `CFT/Brauer/SmoothInvariant.lean`

Composing with §'s `localInvariantEquiv`:

```lean
smoothLocalInvariantEquiv (K) [PerfectField K] (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) :
  SmoothH2 Gal(AlgebraicClosure K/K) (AlgebraicClosure K)ˣ ≃* Multiplicative QModZ
```

This is the invariant map of local class field theory in cohomological form — the half of the norm
residue symbol that turns a cup product into a number.

### Why this is on the critical path

Re-reading §0.41(c): SW's Theorem 13 consumes the `p`-th power Hilbert symbol only through
(i) bilinearity, (ii) the product formula `∏_v (a, b)_v = 1`, and (iii) the local computation
`(z, σz)_𝔓 = z(Frob_𝔓)` at a prime where one argument is unramified.  All three are statements
about `inv_v(χ_a ∪ χ_b)`, so the invariant map on `SmoothH2` is the first of the two halves.  The
second is the cup product `H¹(G, μ_p) × H¹(G, μ_p) → H²(G, k̄ˣ)`, which `CFT/Profinite/Cup.lean`
already supports *provided* the base contains `μ_p`: for a trivial action on `μ_p` the pairing
`Φ(ζ^a)(η) = η^a` is genuinely `G`-equivariant (for a non-trivial action it is not — that is the
`μ_p ⊗ μ_p` twist), and SW work over a base containing `μ_p` throughout.

Build: 9458 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.48 Status (2026-08-31, late night) — coefficient functoriality, and `H²(G, μ_n) = Br(k)[n]`

Two bricks, both prerequisites for the Hilbert symbol named at the end of §0.47.

### (a) `CFT/Profinite/Coeff.lean` — functoriality in the coefficients

The repo had `Comap.lean` (functoriality in the *group*) but nothing in the *coefficients*.  For a
homomorphism `φ : M →* N` commuting with the two actions:

```lean
coeffMap₁ φ u := fun g => φ (u g)          coeffMap₂ φ a := fun p => φ (a p)
coeffH1 φ hφ : SmoothH1 G M →* SmoothH1 G N
coeffH2 φ hφ : SmoothH2 G M →* SmoothH2 G N
```

All the content is that the cocycle relations are equations built from the group law and the
action, that a cochain constant on the cosets of an open normal subgroup stays constant there, and
that `coboundary₂ (coeffMap₁ φ u) = coeffMap₂ φ (coboundary₂ u)`.  Both maps are computed on
cocycles by `rfl`.

⚠ One asymmetry to remember: `coeffH1`'s descent needs `(coeffMap₁_smul_div φ hφ t).symm` while
`coeffH2`'s needs the *unsymmetrised* equation, because `smoothCoboundary₁`'s carrier is
`{u | ∃ t, (fun g => g • t / t) = u}` and `smoothCoboundary₂`'s is
`{a | ∃ u, IsSmooth₁ u ∧ coboundary₂ u = a}` — the two equations point in opposite directions.

### (b) `CFT/Profinite/KummerTwo.lean` — the Kummer sequence one degree up

Let `Ω/k` be Galois with every unit of `Ω` having an `n`-th root (e.g. `Ω = k̄`), and let
`ι : M →* Ωˣ` be an injective equivariant map onto the `n`-th roots of unity of `Ω`.  Then

* `pow_coeffH2_eq_one` — every class in the image is killed by `n`;
* `coeffH2_injective` — **`coeffH2 ι : H²(G, M) → H²(G, Ωˣ)` is injective**;
* `exists_coeffH2_eq_of_pow_eq_one` — **every class killed by `n` is in the image**;
* `range_coeffH2`, `kummerH2Equiv` — so `H²(G, μ_n) ≅ H²(G, Ωˣ)[n]`, which by §0.47 is `Br(k)[n]`
  when `k` is perfect and `Ω = k̄`.

Injectivity is Hilbert 90.  If `ι ∘ b = coboundary₂ w`, then `coboundary₂ (wⁿ) = 1`, so `wⁿ` is a
smooth *one* cocycle, so `wⁿ = g ↦ g•β/β`; an `n`-th root `γ` of `β` corrects `w` into
`t g := w g · γ / (g•γ)`, whose `n`-th power is `(g•β/β)·(β/g•β) = 1` and whose coboundary is still
`coboundary₂ w` (because `g ↦ γ/(g•γ)` is the inverse of a one cocycle).  Surjectivity onto the
`n`-torsion is the same computation backwards: choose an `n`-th root `ρ(y)` of every unit, put
`v := ρ ∘ u` where `coboundary₂ u = aⁿ`, and `a / coboundary₂ v` takes values in `μ_n`.

**The one real obstacle** was smoothness of `coboundary₂ v`.  `Cochain.lean`'s
`IsSmooth₁.coboundary₂` needs `IsSmoothAction G M` — *one* open normal subgroup acting trivially on
*all* of `M` — and `Ωˣ` does not satisfy that.  The fix is that it does not have to: a smooth
cochain `u : Gal(Ω/k) → Ωˣ` is constant on the cosets of `E.fixingSubgroup` for a *finite* Galois
level `E` (`exists_fixingSubgroup_le`), and `restrictNormalHom_surjective_level` gives a section, so
`u` has only `|Gal(E/k)|` values; the normal closure of the field they generate is a finite level
whose fixing subgroup fixes them all.  That is

```lean
exists_isOpenNormal_forall_smul_eq_of_isSmooth₁ :
  IsSmooth₁ u → ∃ P, IsOpenNormal P ∧ ∀ g m, m ∈ P → m • u g = u g
isSmooth₂_coboundary₂_of_isSmooth₁ : IsSmooth₁ u → IsSmooth₂ (coboundary₂ u)
```

and the second is `Cochain.lean`'s proof verbatim with `hact n hn.2` replaced by `hfix y n hn.2`.

### Why this is on the critical path

The Hilbert symbol wants `H¹(G, μ_p) × H¹(G, μ_p) → H²(G, μ_p) → H²(G, k̄ˣ) —inv→ ℚ/ℤ`.
`Cup.lean` gives the first arrow (for `μ_p` in the base, the pairing `Φ(ζᵃ)(η) = η^a` is
`G`-equivariant), `coeffH2 ι` is the second, and §0.47's `smoothLocalInvariantEquiv` is the third.
Injectivity of `coeffH2 ι` is what makes the symbol *faithful*: a cup product is trivial in
`Br(K)` exactly when it is trivial in `H²(G, μ_p)`.

Build: 9460 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.49 Status (2026-08-31, late night) — the `n`-th power symbol

Row 6 of the §0.36 table asks for the `p`-th power Hilbert symbol.  Its *definition* and its
formal properties are now in the repository; only the product formula (global reciprocity) is
still missing.

### `CFT/Profinite/Symbol.lean`

Given Kummer data `h : IsKummerData k Ω M ι n` (see `KummerHom.lean`: `M` is an abstract copy of
the `n`-th roots of unity with its trivial `Gal(Ω/k)`-action, `ι : M →* kˣ` the inclusion) and a
pairing `Φ : M →* M →* M`, the symbol is the cup product of the two Kummer classes:

```lean
noncomputable def kummerSymbol : kˣ →* kˣ →* SmoothH2 Gal(Ω/k) M where
  toFun a := (cupSmoothH1 Φ (h.equivariant Φ) (h.kummerHom a)).comp h.kummerHom
```

Bimultiplicativity is free — it is exactly the statement that `kummerHom` and `cupSmoothH1` are
homomorphisms, so `map_one'`/`map_mul'` are one `rw` each.  Because the action on `M` is trivial,
*every* pairing is equivariant (`IsKummerData.equivariant`, proved by three rewrites with
`h.smul_eq`), which is what keeps `kummerSymbol h Φ` a two-argument gadget instead of a
three-argument one carrying an equivariance proof around.

The four properties that make it usable:

* `kummerSymbol_eq_one_of_isPow_left` / `_right`: the symbol is trivial as soon as one argument is
  an `n`-th power in `k`.  This is `kummerClass_eq_one_iff` plus `map_one`, so the symbol descends
  to `kˣ/(kˣ)ⁿ × kˣ/(kˣ)ⁿ`.
* `resH2_kummerSymbol`: restriction to a subgroup `H ≤ Gal(Ω/k)` turns the symbol into the symbol
  of the restricted classes — that is, the symbol localizes.  This is `resH2_cupSmoothH1` from
  `Cup.lean`.
* `kummerSymbol_mem_sha2_left` / `_right`: combining the previous two with `KummerRes.lean`'s
  `resH1_kummerClass_eq_one_iff`, a symbol one of whose arguments lies in `h.localPowers S` is in
  `sha2 M S`.  Over a number field, with `S` the decomposition subgroups, this says: *a symbol one
  of whose arguments is locally a power everywhere is everywhere locally trivial.*
* `pow_kummerSymbol_eq_one`: the symbol is killed by `n`.  The general fact behind it,
  `smoothH2_pow_eq_one`, is that `H²(G, M)` is killed by `n` when `M` is — one line, because
  `coboundary₂ 1 = 1`.

### Avoiding a discrete logarithm

A pairing `μ_n × μ_n → μ_n` is *not* canonical: it is a choice of a primitive root, i.e. a
discrete logarithm.  Rather than manufacture one on an abstract cyclic group, the file supplies
the model where the pairing is free:

```lean
def mulZMod : Multiplicative (ZMod n) →* Multiplicative (ZMod n) →* Multiplicative (ZMod n)
noncomputable def zmodRootHom (hζ : IsPrimitiveRoot ζ n) : Multiplicative (ZMod n) →* kˣ
theorem isKummerData_zmod (hζ) (hroot) : IsKummerData k Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n
```

`mulZMod` is multiplication in `ZMod n` read multiplicatively, and `zmodRootHom hζ` sends a
residue `a` to `ζ^a.val`.  That this is a homomorphism is `ZMod.val_add` together with
`pow_mod_of_pow_eq_one`; injectivity is `IsPrimitiveRoot.pow_inj` on representatives below `n`,
and surjectivity onto the `n`-th roots of unity is `IsPrimitiveRoot.eq_pow_of_pow_eq_one` with
`ZMod.val_cast_of_lt`.  The trivial action `zmodTrivialAction` is a `def` used through `letI`,
deliberately not a global instance — the same pattern as `rootsOfUnityTrivialAction`.

⚠ In this Mathlib pin `Multiplicative` is a plain `def`, `ofAdd`/`toAdd` are `Equiv`s, and the
simp lemmas `ofAdd_toAdd`, `toAdd_mul`, … live in the **root** namespace, *not* under
`Multiplicative.`; `Multiplicative.ofAdd_toAdd` is an unknown constant.  All of them are `rfl`, so
the file uses `show`/`rfl` throughout and closes injectivity with `Multiplicative.ext` (which
*does* exist) applied to `ZMod.val_injective`.

### Landing the symbol in the Brauer group

`IsKummerData.unitsHom = Units.map (algebraMap k Ω) ∘ ι : M →* Ωˣ` is the coefficient
homomorphism into the units of the extension; it is equivariant because the base units are fixed
(`smul_units_algebraMap`), injective, and its image consists of `n`-th roots of unity.  Pushing
the symbol along it:

```lean
noncomputable def kummerSymbolUnits : kˣ →* kˣ →* SmoothH2 Gal(Ω/k) Ωˣ :=
  ...(coeffH2 h.unitsHom h.unitsHom_equivariant).comp (kummerSymbol h Φ a)
theorem kummerSymbolUnits_eq_one_iff (hroot : ∀ y : Ωˣ, ∃ z : Ωˣ, z ^ n = y) (a b : kˣ) :
    kummerSymbolUnits h Φ a b = 1 ↔ kummerSymbol h Φ a b = 1
```

The `iff` is §0.48's `coeffH2_injective`: over an extension closed under `n`-th roots, nothing is
lost by reading the symbol in `H²(Gal(Ω/k), Ωˣ)`.  Composed with §0.46's `smoothBrauerEquiv` this
is a symbol with values in `Br(k)[n]`, and over a local field §0.47's
`smoothLocalInvariantEquiv` turns it into a number in `(1/n)ℤ/ℤ ⊆ ℚ/ℤ`.

### What is still missing for row 6

The *product formula* `∏_v (a,b)_v = 0`.  That is global reciprocity — the statement that the sum
of the local invariants of a global Brauer class vanishes — and it needs the exact sequence
`0 → Br(k) → ⊕_v Br(k_v) → ℚ/ℤ → 0`, of which only the injectivity on the left (row 3's
`eq_one_of_mem_sha2`, in the roots-of-unity form) is currently available.  The symbol as built is
already enough for the *local* Scholz–Reichardt bookkeeping, which is where it is wanted.

Build: 9461 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.50 Status (2026-08-31, late night) — the norm residue symbol of a local field

`CFT/Brauer/LocalSymbol.lean` closes the local half of row 6.  Over a local field `K` (perfect,
complete, discretely valued, locally compact) containing a primitive `n`-th root of unity `ζ`, the
composite

```
Kˣ × Kˣ  —kummerSymbol→  H²(G_K, μ_n)  —coeffH2→  H²(G_K, K̄ˣ)  —smoothBrauer→  Br(K)  —inv→  ℚ/ℤ
```

is packaged as

```lean
noncomputable def localSymbol (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) : Kˣ →* Kˣ →* Multiplicative QModZ
```

together with `pow_localSymbol_eq_one` (values in the `n`-torsion), and
`localSymbol_eq_one_of_isPow_left` / `_right`.  The general form `localKummerSymbol` takes arbitrary
Kummer data and an arbitrary pairing; `localSymbol` instantiates it at `Multiplicative (ZMod n)`
with `mulZMod n`, which is where §0.49 put the choice of primitive root.

Two small things make the assembly clean:

* `MonoidHom.compHom` post-composes a *bilinear* gadget in one step — `localKummerSymbol` is just
  `(MonoidHom.compHom inv).comp (kummerSymbolUnits h Φ)`, so bimultiplicativity is inherited rather
  than re-proved.
* `exists_units_pow_eq_self`: over an algebraically closed field every unit is an `n`-th power.
  This discharges the hypothesis of §0.49's `kummerSymbolUnits_eq_one_iff` outright, so

  ```lean
  theorem localKummerSymbol_eq_one_iff … :
      localKummerSymbol hres hm h Φ a b = 1 ↔ kummerSymbol h Φ a b = 1
  ```

  holds with no side condition: **the invariant sees the whole symbol.**

### What row 6 still lacks, and why it is not a local question

The product formula `∑_v inv_v (a,b)_v = 0` is *not* a statement about the symbol; it is the
statement that the sum of the local invariants of a global Brauer class vanishes.  Formally that is
the middle of

```
0 → Br(k) → ⊕_v Br(k_v) → ℚ/ℤ → 0,
```

whose left exactness is row 3 (`eq_one_of_mem_sha2`).  The repo's global class formation
(`Units/GlobalTate.lean`) produces `globalFundamentalClass` by a *choice* — the existence of a
class annihilated by exactly the multiples of the degree — which is enough for Tate's theorem but
does **not** pin the invariant map down as the sum of local invariants.  Getting the product
formula therefore means building the invariant map of the global class formation from the local
ones, which needs:

* the decomposition subgroup `D_v ≤ G_k` identified with `G_{k_v}` as a topological group, with
  `Ω` becoming `k̄_v` as a `D_v`-module (the repo has `decompositionSubgroups`
  (`Units/InfiniteDecomposition.lean`) and the completions, but not yet the identification at the
  level of absolute Galois groups);
* the localization `H²(G_k, Ωˣ) → H²(D_v, Ωˣ) ≅ Br(k_v)` for each `v`, and the fact that all but
  finitely many components vanish;
* exactness of `H²(G, K̄ˣ) → H²(G, I) → H²(G, C)` from `Units/IdeleClassSES.lean`, plus Shapiro to
  read `H²(G, I)` as `⊕_v Br(k_v)`.

That is the next large project on the critical path, and it is shared with row 8: Poitou–Tate needs
the same localization maps.

Build: 9462 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.51 Status (2026-08-31, late night) — the localization of the Brauer group at a finite place

`CFT/Brauer/PlaceInvariant.lean` lays the first brick of the project named at the end of §0.50 —
and it turns out that the hardest-looking prerequisite listed there is **not needed at all**.

### (a) The localization map does not need the decomposition group

§0.50 planned the localization `H²(G_k, Ωˣ) → H²(D_v, Ωˣ) ≅ Br(k_v)` and observed that it requires
identifying the decomposition subgroup `D_v ≤ G_k` with `G_{k_v}` as a topological group, with `Ω`
becoming `k̄_v` as a `D_v`-module.  That is a genuine piece of work (a normal-closure/compositum
argument plus continuity of the comparison map) and it has *not* been done.

It does not have to be.  The same map is available purely algebraically:

```
Br(k)  —baseChangeHom k_v→  Br(k_v)  —localInvariantHom→  ℚ/ℤ
```

`BrauerGroup.baseChangeHom` (`Brauer/BaseChange.lean`) sends `⟦A⟧` to `⟦k_v ⊗_k A⟧` with no Galois
theory whatsoever, and `localInvariantHom` (`Brauer/InvariantMap.lean`) is the invariant map of
local class field theory.  Composing them is

```lean
noncomputable def placeInvariant (v : HeightOneSpectrum (𝓞 k)) :
    BrauerGroup.{0, 0} k →* Multiplicative QModZ
```

and, because `smoothBrauerEquiv` identifies `Br` of a perfect field with `SmoothH2` of its absolute
Galois group, the cohomological form `smoothPlaceInvariant` is a one-line transport.  The
comparison of Galois groups is thereby *replaced* by the comparison of Brauer groups, which is a
tensor product.

### (b) The completion is a local field in the sense the repo already uses

Every hypothesis of the local invariant map is discharged for `v.adicCompletion k`:

| hypothesis | source |
| --- | --- |
| `Valued _ ℤᵐ⁰`, `CompleteSpace` | Mathlib |
| `Valuation.RankOne` | `NumberField.instRankOneValuedAdicCompletion` — but only with `synthInstance.maxHeartbeats 1000000`; at the default it times out |
| `ProperSpace` | `Local.properSpace_adicCompletion` (`Local/AdicLocalField.lean`) |
| `PerfectField` | new instance `charZero_adicCompletion` + `PerfectField.ofCharZero` |
| `IsUnitValGen _ 1` | `isUnitValGen_one (valued_adicCompletion_surjective v)` — the canonical normalization, so `placeInvariant` carries no `hm` argument |
| `HasResidueChar _ p e` | `exists_hasResidueChar_adicCompletion` (`Local/AdicHerbrand.lean`) — available for *every* place, so it can be produced inside a proof rather than carried as a hypothesis |

The last row is what makes the main result unconditional:

```lean
theorem placeInvariant_eq_one_iff (v) (x) :
    placeInvariant k v x = 1 ↔ x ∈ BrauerGroup.relative k (v.adicCompletion k)
```

**a Brauer class of a number field has trivial invariant at a place exactly when the completion
there splits it.**  Injectivity of the local invariant map (`localInvariantHom_injective`) is the
whole content of the forward direction.

### (c) Base change of the smooth second cohomology, functorially

The same transport gives, for perfect fields,

```lean
noncomputable def smoothBaseChange (k K : Type u) … :
    SmoothH2 Gal(AlgebraicClosure k/k) (AlgebraicClosure k)ˣ →*
      SmoothH2 Gal(AlgebraicClosure K/K) (AlgebraicClosure K)ˣ
```

with `smoothBaseChange_self` and `smoothBaseChange_comp` inherited from `baseChangeHom_self` and
`baseChangeHom_comp`.  This is the coefficient-and-group change that a direct construction would
have had to build by hand out of `comapH2` and `coeffH2`, complete with an `IsSmoothHom` proof.

### (d) What the product formula still needs

With the localizations in place, the sequence

```
0 → Br(k) → ⊕_v Br(k_v) → ℚ/ℤ → 0
```

decomposes into three independent statements, all now expressible without any profinite plumbing:

1. **Injectivity** (Albert–Brauer–Hasse–Noether): `(∀ v, placeInvariant k v x = 1) → x = 1`.  The
   repo has the finite-level cocycle form, `exists_sub_add_eq_globalUnits` (`Units/ABHN.lean`), and
   `H2Surjective.lean` identifies `Br(K/k)` with `H²(Gal(K/k), Kˣ)`.  The bridge that is missing is
   the compatibility of *algebraic* base change `k_v ⊗_k −` with *cohomological* restriction to the
   decomposition subgroup: `k_v ⊗_k (K/k, a)` is the crossed product `(K_w/k_v, res a)`.
2. **Almost-all vanishing**: for a fixed `x`, `placeInvariant k v x = 1` for all but finitely many
   `v`.  Classically, a splitting field `K/k` is unramified outside a finite set and the values of
   a cocycle are units outside a finite set, and `H²` of the units of an unramified local extension
   vanishes — the last of which the repo has (`Local/UnramifiedCoboundary.lean`,
   `subsingleton_tate_adicUnits`).
3. **The sum vanishes**.  This is the deep one and is the reciprocity law.

Items 1 and 2 need the same bridge, and it is a bounded, purely algebraic project; item 3 is not.

The archimedean places are not yet covered: `Brauer/RealInvariant.lean` has
`realBrauerInvariant : Br(ℝ) →* ℚ/ℤ`, so the missing step is only to turn a real embedding of `k`
into an `Algebra k ℝ` and base change along it.

Build: 9463 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.52 Status (2026-08-31, late night) — the bridge of §0.51(d)1 is built: base change of a crossed product to a completion

The missing compatibility named at the end of §0.51(d)1 — *"`k_v ⊗_k (K/k, a)` is the crossed
product `(K_w/k_v, res a)`"* — is now a theorem, in `CFT/Brauer/PlaceCrossedProduct.lean`, resting
on a new brick `CFT/Units/DecompositionField.lean`.

### (a) The decomposition field, and the tower that was *not* needed

The plan of record was to go through the completion `F_u` of the decomposition field
`F = K^{D_w}` and to compare degrees along `k_v → F_u → K_w`.  That is painful in Lean, because
`primeUnder (𝓞 k) (primeUnder (𝓞 F) w) = primeUnder (𝓞 k) w` holds only propositionally and the
repo has to transport along it with the `ringCast` machinery of `Units/PlaceTower.lean`.

None of it is necessary.  `Units/CompletionGalois.lean` already proves

```lean
mem_range_algebraMap_iff_forall_stabilizer_smul_eq :
    z ∈ Set.range (algebraMap (primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K))
      ↔ ∀ σ : ↥(stabilizer Gal(K/k) w), σ • z = z
```

so an element of `F` — fixed by the decomposition group by definition — lands in the image of
`k_v` the moment it is pushed into `K_w`.  That gives a ring homomorphism directly,

```lean
noncomputable def decompositionFieldHom : ↥(decompositionField k w) →+* (primeUnder (𝓞 k) w).adicCompletion k
```

built as `(rangeEquivBaseCompletion k w).symm ∘ codRestrict (toAdicCompletion w ∘ algebraMap …)`,
together with `algebraMap_decompositionFieldHom` saying the triangle into `K_w` commutes.  From it
come the `Algebra ↥F k_v` instance and both scalar towers (`k → F → k_v` and `F → k_v → K_w`).
`F_u`, `ringCast` and the degree count are all off the critical path.

### (b) The Galois groups

`Units/DecompositionGalois.lean` has `decompositionEquiv k w : ↥(stabilizer Gal(K/k) w) ≃* Gal(K_w/k_v)`,
and `IntermediateField.subgroupEquivAlgEquiv` has `↥(stabilizer Gal(K/k) w) ≃* Gal(K/F)`.  Composing,

```lean
noncomputable def localDecompositionEquiv : Gal(K_w/k_v) ≃* Gal(K/↥(decompositionField k w))
```

with the compatibility `algebraMap_localDecompositionEquiv` — `τ` and `localDecompositionEquiv k w τ`
agree on the image of `K` — which is exactly the hypothesis shape `he` of
`CrossedProduct.baseChangeHom_mk_csa_compositum`.

### (c) The bridge, in two steps

`Brauer/CrossedProductRestrict.lean` computes base change from `k` to an intermediate field, and
`Brauer/CrossedProductCompositum.lean` computes base change along a field over which the Galois
group is unchanged.  `F` is precisely the field where the second applies, so the composite

```
Br(k) —base change→ Br(F) —base change→ Br(k_v)
```

evaluated on `⟦(K/k, f)⟧` is the class of the crossed product of

```lean
noncomputable def localCocycle (f : Gal(K/k) × Gal(K/k) → Kˣ) :
    Gal(K_w/k_v) × Gal(K_w/k_v) → (w.adicCompletion K)ˣ :=
  CrossedProduct.compositumCocycle (localDecompositionEquiv k w)
    (CrossedProduct.restrictCocycle ↥(decompositionField k w) f)
```

(`baseChangeHom_mk_csa_adicCompletion`, via `BrauerGroup.baseChangeHom_comp`), and with
`Brauer/Kernel.lean`'s `mk_csa_eq_one_iff` this gives the payoff

```lean
theorem placeInvariant_mk_csa_eq_one_iff (hf : IsMulCocycle₂ f) :
    placeInvariant k (primeUnder (𝓞 k) w) (⟦CrossedProduct.csa hf⟧ : BrauerGroup k) = 1
      ↔ IsMulCoboundary₂ (localCocycle k w f)
```

**the invariant at a finite place of a crossed-product class vanishes exactly when the local
cocycle is a coboundary.**  That is the hypothesis `hfin` of `exists_sub_add_eq_globalUnits`
(`Units/ABHN.lean`) up to the notational dictionary between `IsMulCoboundary₂` and the
`Additive`/`smulUnitsAut`/`adicUnitHom` spelling, which is the next brick.

### (d) What §0.51(d)1 still needs after this

1. the notational dictionary just named (mechanical);
2. the archimedean analogue: `w.Completion` in place of `w.adicCompletion K`, an infinite-place
   decomposition field, and `Br(ℝ)` in place of `Br(k_v)` — `Brauer/RealInvariant.lean` supplies
   the invariant, the decomposition-field construction transcribes;
3. surjectivity of `H²(Gal(K/k), Kˣ) → Br(K/k)` for a *variable* splitting field, so that an
   arbitrary class of `Br(k)` is a crossed product — `H2Surjective.lean` has the finite-level
   statement.

Lean notes: two instance traps.  A module-level `set_option synthInstance.maxHeartbeats 1000000`
is mandatory once `Algebra ↥(IntermediateField …) (… adicCompletion …)` is in scope — the default
20000 cannot even find `SMul ↥F k_v`, and the failure surfaces as a bogus goal rather than an
error.  And `IsGalois k_v K_w` is needed to *state* `localCocycle`, so the in-proof
`haveI := isGalois_adicCompletion k w` is too late; it must be
`attribute [local instance] isGalois_adicCompletion` before the `variable` block.

Build: 9466 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.53 Status (2026-08-31, late night) — the Albert–Brauer–Hasse–Noether theorem, on the Brauer group

Item 1 of §0.51(d) is **done**.

```lean
theorem eq_one_of_forall_mem_relative (x : BrauerGroup k)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 k), x ∈ BrauerGroup.relative k (v.adicCompletion k))
    (hinf : ∀ u : InfinitePlace k, x ∈ BrauerGroup.relative k u.Completion) :
    x = 1
```

**a Brauer class over a number field which is split by every completion is trivial**
(`Brauer/HasseNoether.lean`), together with the invariant-map phrasing
`eq_one_of_forall_placeInvariant_eq_one` and the packaged

```lean
theorem brauerToCompletions_injective : Function.Injective (brauerToCompletions k)
```

into `(∏_v Br(k_v)) × (∏_u Br(k_u))`.  Unconditional, sorry-free, axiom-free.

### (a) The three §0.52(d) items, and where each landed

1. **The notational dictionary** — `Brauer/PlaceCoboundary.lean`.  The two identifications of the
   decomposition group agree (`localDecompositionEquiv_decompositionEquiv`), so transporting
   `IsMulCoboundary₂ (localCocycle k w f)` along `decompositionEquiv` and unwinding
   `Additive`/`smulUnitsAut`/`adicUnitHom` gives
   `placeInvariant_mk_csa_eq_one_iff_exists` and its `relative`-phrased twin
   `mem_relative_mk_csa_adicCompletion_iff_exists`, which are *literally* the `hfin` clause of
   `exists_sub_add_eq_globalUnits`.
2. **The archimedean analogue** — `Units/InfiniteDecompositionField.lean` +
   `Brauer/InfinitePlaceCrossedProduct.lean`.  This turned out to be a transcription rather than a
   new construction: the whole infinite-place infrastructure already existed in parallel
   (`mem_range_algebraMap_iff_forall_stabilizer_smul_eq_infinite`, `isGalois_infiniteCompletion`,
   `finiteDimensional_infiniteCompletion`, and crucially `stabilizerAlgEquivInfinite`, the infinite
   analogue of `decompositionEquiv`), so only the decomposition-field embedding and the two-step
   base change had to be written.  `Br(ℝ)` is *not* used: the statement is
   `x ∈ BrauerGroup.relative k u.Completion`, which needs no invariant map at all.
3. **Surjectivity for a variable splitting field** — already in the repo.
   `exists_mk_csa_eq_of_mem_relative` (`Brauer/SmoothBrauer.lean`) plus
   `exists_isGalois_mem_relative` (`Brauer/GaloisSplitting.lean`, applicable because a number field
   is perfect) writes an arbitrary class of `Br(k)` as `⟦CrossedProduct.csa hf⟧` for a cocycle of
   some finite Galois extension of number fields.

### (b) The assembly

Given `x : Br(k)`, pick the Galois splitting field `L` (a number field by
`NumberField.of_module_finite`) and write `x = ⟦csa hf⟧`.  Then:

* `hfin` at a prime `v` of `𝓞 L` is the hypothesis at `primeUnder (𝓞 k) v`;
* `hinf` at an infinite place `w` of `L` is the hypothesis at `w.comap (algebraMap k ↥L)`;
* the cocycle identity `IsMulCocycle₂ f` *is* the additive cocycle identity `ha`, via the one-line
  dictionary `Additive.toMul (globalUnitsAut σ u) = σ • Additive.toMul u`, proved by `Units.ext rfl`;
* `exists_sub_add_eq_globalUnits` then returns a cochain, which is exactly a witness of
  `IsMulCoboundary₂ f`, and `CrossedProduct.mk_csa_eq_one_iff` concludes.

So the global input is *only* `Units/ABHN.lean`; everything else is the crossed-product dictionary.

### (c) What is left of the product formula

Of the three items of §0.51(d), **item 1 is closed**.  Remaining:

2. **almost-all vanishing** of `placeInvariant k v x` — a splitting field is unramified outside a
   finite set and `H²` of the units of an unramified local extension vanishes
   (`Local/UnramifiedCoboundary.lean`, `subsingleton_tate_adicUnits`);
3. **the sum vanishes** — the reciprocity law, still the deep one.

Lean notes.  `MonoidHom.pi` does not exist in Mathlib; the product of monoid homomorphisms into a
dependent product is `Pi.monoidHom`.  `placeInvariant` takes `k` explicitly but
`placeInvariant_eq_one_iff` takes it implicitly.  And an `@[simp]` lemma whose right-hand side is a
pair of lambdas needs the binder types written out, or the field projections inside them cannot be
elaborated.

Build: 9470 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.54 Status (2026-08-31, late night) — almost all local invariants vanish

Item 2 of §0.51(d) is **done**.

```lean
theorem finite_setOf_not_mem_relative_adicCompletion (x : BrauerGroup k) :
    {v : HeightOneSpectrum (𝓞 k) | x ∉ BrauerGroup.relative k (v.adicCompletion k)}.Finite

theorem finite_setOf_placeInvariant_ne_one (x : BrauerGroup k) :
    {v : HeightOneSpectrum (𝓞 k) | placeInvariant k v x ≠ 1}.Finite
```

(`Brauer/PlaceInvariantFinite.lean`), with the base-change phrasing
`finite_setOf_baseChangeHom_adicCompletion_ne_one` in between.  Unconditional, sorry-free,
axiom-free.  Together with §0.53 this says that `brauerToCompletions` is injective *and* lands in
the restricted product: a Brauer class over a number field is determined by its local invariants,
and only finitely many of them are nontrivial.

### (a) `CFT/Units/ABHNUnitValues.lean` — dropping the torsion hypothesis of `ABHNTorsion`

`Units/ABHNTorsion.lean` proved that at an unramified finite place the local component of a
two-cocycle of the units is a coboundary **provided the cocycle is killed by a nonzero integer**.
Reading that proof, the torsion hypothesis is used for exactly one thing: to know that the values
land in `(unitVal).ker`, the units of the valuation ring, where the second cohomology of the cyclic
decomposition group vanishes (`Local/UnramifiedCoboundary.lean`, `exists_sub_add_eq_adicUnits`).
So the hypothesis can simply be replaced by that conclusion:

```lean
theorem exists_sub_add_eq_adicUnits_of_unitVal (v : HeightOneSpectrum (𝓞 K))
    (hunr : Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal)
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (hu : ∀ x y : Gal(K/k), unitVal (Additive.ofMul (adicUnitHom v (a x y).toMul)) = 0)
    (ha : ∀ x y z : Gal(K/k),
      globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y) :
    ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ, …
```

and the hypothesis `hu` is then available for free at almost every place, because it is literally
the statement that the diagonal image of a unit is an idele:

```lean
theorem finite_setOf_unitVal_adicUnitHom_ne_zero (u : Kˣ) :
    {v : HeightOneSpectrum (𝓞 K) | unitVal (Additive.ofMul (adicUnitHom v u)) ≠ 0}.Finite
```

which is `fullDiag_mem_idele` (`Units/Idele.lean`) read through `mem_idele` and
`Filter.eventually_cofinite`.  A number field element has nonzero order at only finitely many
primes; nothing further is needed.

### (b) `CFT/Brauer/PlaceInvariantFinite.lean` — the bad set, and pushing it down

Take a class `x` of `Br(k)`.  By `exists_isGalois_mem_relative` and
`exists_mk_csa_eq_of_mem_relative` it is `⟦CrossedProduct.csa hf⟧` for a two-cocycle
`f : Gal(L|k) × Gal(L|k) → Lˣ` of a finite Galois extension of number fields.  Upstairs, put

```
Bad = {w : ramified over k} ∪ ⋃_{(σ,τ)} {w : unitVal (adicUnitHom w (f (σ,τ))) ≠ 0}.
```

The first piece is finite by `finite_setOf_not_isUnramifiedAt` (a ramified place divides the
different ideal, and a nonzero ideal has finitely many prime divisors); the union is over the
**finite** set `Gal(L|k) × Gal(L|k)`, so `Set.finite_iUnion` applies to the finiteness of (a).
Downstairs, every place of `k` has a place of `L` above it (`exists_primeUnder_eq`), so the set of
bad places of `k` is contained in `primeUnder (𝓞 k) '' Bad`, which is finite.  And a place of `k`
under a `w ∉ Bad` is good: `exists_sub_add_eq_adicUnits_of_unitVal` produces the local coboundary
and `mem_relative_mk_csa_adicCompletion_iff_exists` (§0.53) turns it into splitting.

The additive form of the cocycle identity for `f` is re-derived inline, as in `HasseNoether.lean`;
the dictionary lemma `toMul_globalUnitsAut` (`Units/ABHNCoboundary.lean`) is what makes it one
`simp only`.

### (c) What is left of the product formula

Of the three items of §0.51(d), **items 1 and 2 are closed**.  What remains is

3. **the sum vanishes**, `∑_v inv_v(x) = 0` — the reciprocity law.

This is not a bookkeeping item: it is the fundamental class of global class field theory, and it is
what upgrades §0.53 + §0.54 to the exact sequence `0 → Br(k) → ⊕_v Br(k_v) → ℚ/ℤ → 0`.  It is also
the input that rows 5 and 8 of the §0.36 table (Poitou–Tate, wall #1) are waiting on: the pairing
`Ш¹(k, A′) × Ш²(k, A) → ℚ/ℤ` is *defined* by a sum of local invariants, and its well-definedness is
exactly the product formula.

Build: 9472 jobs green, zero warnings, zero sorries outside the comparator.

---

## 0.55 Status (2026-08-31, late night) — the archimedean invariant, and the full family

Two new modules, `CFT/Brauer/InfiniteInvariant.lean` and `CFT/Brauer/TotalInvariant.lean`.  Together
they close the archimedean gap flagged at the end of §0.51(d) and give the family of local
invariants a single name.

### (a) `CFT/Brauer/InfiniteInvariant.lean` — the invariant at an infinite place

Up to now the archimedean side of the theory was phrased through *real embeddings*:
`realEmbeddingInvariant k` needs an `[Algebra k ℝ]` instance supplied by the caller, and
`realPlaceInvariant k hw` supplies it from a proof that a place is real.  The completions
`u.Completion` never appeared on the invariant side, so `eq_one_of_forall_placeInvariant_eq_one`
still had to take its archimedean hypothesis in the raw form `x ∈ BrauerGroup.relative k u.Completion`.

The two facts that fix this are entirely about the shape of the completion.

```lean
theorem relative_completion_eq_top_of_isComplex {u : InfinitePlace k} (hu : u.IsComplex) :
    BrauerGroup.relative k u.Completion = ⊤

theorem relative_completion_eq_relative_real {u : InfinitePlace k} (hu : u.IsReal) [Algebra k ℝ]
    (halg : (algebraMap k ℝ) = (InfinitePlace.embedding_of_isReal hu : k →+* ℝ)) :
    BrauerGroup.relative k u.Completion = BrauerGroup.relative k ℝ
```

Mathlib already has the two ring isomorphisms `ringEquivComplexOfIsComplex` and
`ringEquivRealOfIsReal`, and the compatibility with the base is `extensionEmbedding_coe` /
`extensionEmbeddingOfIsReal_coe`.  What is worth recording is the mechanical part: **turn the ring
isomorphism into an `AlgEquiv` with `AlgEquiv.ofRingEquiv`, not with a structure-update `{ e.symm
with commutes' := … }`**.  The structure-update route builds an `AlgHom` whose application unfolds
to `(↑↑e.symm.toRingHom).toFun x`, and `rw [RingEquiv.apply_symm_apply]` then fails to match; with
`AlgEquiv.ofRingEquiv hmap` the same proof is two `relative_le_relative_of_algHom` calls on
`e.toAlgHom` and `e.symm.toAlgHom`, and the compatibility hypothesis `hmap` is exactly what
`ofRingEquiv` asks for.  A pleasant surprise: `algebraMap k u.Completion r` is *definitionally* the
coercion `↑r`, so `hmap` is `extensionEmbedding_coe` applied verbatim, with no glue.

For the complex case, `relative k ℂ = ⊤` is `BrauerGroup.relative_eq_top_of_isAlgClosed`, and the
`Algebra k ℂ` instance needed to state it is a `letI` from `u.embedding`; the conclusion is about
`u.Completion` only, so the instance never escapes.

The invariant itself is then a `dite` on `u.IsReal`:

```lean
noncomputable def infinitePlaceInvariant (u : InfinitePlace k) :
    BrauerGroup.{0, 0} k →* Multiplicative QModZ :=
  if hu : u.IsReal then realPlaceInvariant k hu else 1

theorem infinitePlaceInvariant_eq_one_iff (u : InfinitePlace k) (x : BrauerGroup.{0, 0} k) :
    infinitePlaceInvariant k u x = 1 ↔ x ∈ BrauerGroup.relative k u.Completion
```

Note that none of these need `[NumberField k]`: `InfinitePlace`, its completion and
`realPlaceInvariant` are all defined for a bare field, so the linter's `omit [NumberField k] in` is
correct and not a warning to be silenced.

### (b) `CFT/Brauer/TotalInvariant.lean` — the family, and its sum

```lean
noncomputable def localInvariants :
    BrauerGroup.{0, 0} k →*
      ((HeightOneSpectrum (𝓞 k) → Multiplicative QModZ) ×
        (InfinitePlace k → Multiplicative QModZ))

theorem localInvariants_injective : Function.Injective (localInvariants k)
```

which is the Albert–Brauer–Hasse–Noether theorem in its final form: **a Brauer class over a number
field is determined by its family of local invariants.**  The archimedean hypothesis of
`eq_one_of_forall_placeInvariant_eq_one` is now discharged by (a), so the intermediate statement

```lean
theorem eq_one_of_forall_invariant_eq_one (x : BrauerGroup.{0, 0} k)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x = 1)
    (hinf : ∀ u : InfinitePlace k, infinitePlaceInvariant k u x = 1) :
    x = 1
```

mentions no relative Brauer groups at all.

The sum over all places is a `MonoidHom` because of §0.54:

```lean
noncomputable def totalInvariant : BrauerGroup.{0, 0} k →* Multiplicative QModZ where
  toFun x := (∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x) *
    ∏ u : InfinitePlace k, infinitePlaceInvariant k u x
```

`map_mul'` is `finprod_mul_distrib` fed with `finite_setOf_placeInvariant_ne_one` twice — the
`Function.mulSupport` of `fun v => placeInvariant k v x` *is* the set of §0.54 on the nose, so no
conversion lemma is needed — followed by `Finset.prod_mul_distrib` (the infinite places are a
`Fintype`) and `mul_mul_mul_comm`.

### (c) What is left

Reciprocity is now a one-line statement in the repository's own vocabulary:

```
totalInvariant k = 1.
```

That is item 3 of §0.51(d), unchanged, and still the input rows 5, 6 and 8 of the §0.36 table are
waiting on.  What §0.55 adds is that everything *around* it is now phrased in invariants: the exact
sequence to aim for is

```
0 → Br(k) --localInvariants--> ⊕_v ℚ/ℤ --sum--> ℚ/ℤ → 0,
```

whose left exactness is `localInvariants_injective` (done), whose "almost all vanish" is §0.54
(done), and whose middle exactness is reciprocity plus a surjectivity statement.

Also worth recording, from the survey done while choosing this brick: **row 4 of the §0.36 table is
stale.**  Its stated remainder, `inv_M ∘ res = [M : K] · inv_K`, is already a theorem —
`localInvariantHom_baseChange` in `CFT/Brauer/InvariantBaseChange.lean`.  Local class field theory
in this repository is complete (`localInvariantEquiv`, `localInvariantHom_injective`,
`localInvariantHom_baseChange`), and so is the idele class formation on the global side
(`first_inequality`, `globalFundamentalClass`, `globalTateEquiv`, `globalReciprocityEquiv`,
`H¹(G, C_K) = 0`, `H²(G, K*) ↪ H²(G, I_K)`).  The reciprocity law is genuinely the one missing
global input, not a bookkeeping gap.

One shortcut was considered and **refuted**: one cannot get reciprocity by comparing indices, on the
grounds that the image of `H²(G, I_K)` in `H²(G, C_K)` and the kernel of the sum have the same
index.  The image is generated by `1 / lcm_v(n_v)`, not by `1 / n`, and these differ already for a
biquadratic extension.

Build: 9474 jobs green, zero warnings, zero sorries outside the comparator; axioms of
`localInvariants_injective` and `totalInvariant` are `[propext, Classical.choice, Quot.sound]`.

---

## 0.56 Status (2026-08-31) — the norm residue symbol of a cyclic local extension, and the shape of reciprocity

### (a) `CFT/Brauer/CyclicNormResidue.lean`

Two bricks that were already in the tree turn out to fit together with nothing in between:

* `cyclicBrauerEquiv` (`CFT/Brauer/CyclicNorm.lean`) — for *any* finite cyclic Galois `L/K` of
  *any* fields, `Kˣ / N(Lˣ) ≃* Br(L/K)`, together with `exists_cyclicBrauerHom_eq` (surjectivity)
  and `ker_cyclicBrauerHom`.  No local hypotheses at all.
* `index_normSubgroup_eq_finrank_local` (`CFT/Local/CyclicNormIndex.lean`) — the norm index of a
  cyclic extension of a local field is the degree, **ramified or not**.

Transporting the second along the first is immediate and gives the two structural facts:

```lean
theorem natCard_relative_eq_finrank_of_cyclic … :
    Nat.card ↥(BrauerGroup.relative K L) = finrank K L
theorem relative_eq_brauerTorsion_of_cyclic … :
    BrauerGroup.relative K L = brauerTorsion K (finrank K L)
```

The second is `Subgroup.eq_of_le_of_card_ge` fed with `relative_le_brauerTorsion` and
`natCard_brauerTorsion`.  It is the *general* form of `relative_eq_brauerTorsion_of_unramified`
(`CFT/Brauer/RelativeTorsion.lean`): **a cyclic extension of a local field splits exactly the
classes killed by its degree**, with no unramifiedness hypothesis and no Frobenius.

The symbol itself is the composite of the two maps that are now available:

```lean
noncomputable def cyclicNormResidue (hm : IsUnitValGen K m) : Kˣ →* Multiplicative QModZ :=
  (localInvariantHom K hm).comp (cyclicBrauerHom hsigma)
```

with `ker_cyclicNormResidue = normSubgroup K L` (injectivity of `localInvariantHom` turns the
kernel of the cyclic algebra map into the kernel of the symbol), the user-facing
`cyclicNormResidue_eq_one_iff` (*a unit has trivial symbol exactly when it is a norm*),
`pow_cyclicNormResidue_eq_one`, and

```lean
theorem exists_cyclicNormResidue_eq … :
    ∃ a : Kˣ, cyclicNormResidue hsigma hm a
      = Multiplicative.ofAdd (QuotientAddGroup.mk (1 / (finrank K L : ℚ)) : QModZ)
```

so the symbol is onto `(1/n)ℤ/ℤ`.  Together: `Kˣ / N(Lˣ) ≅ (1/n)ℤ/ℤ ≅ ℤ/n ≅ Gal(L/K)`, which is
local class field theory for cyclic extensions in the concrete form the global argument consumes.
`a ↦ σ₀ ^ (n · inv(L/K, σ₀, a))` is the local Artin map, and it is now one definition away.

Build: 9475 jobs green, zero warnings, zero sorries outside the comparator; all seven new
declarations have axioms `[propext, Classical.choice, Quot.sound]`.

### (b) The obstruction named in §0.55 was the wrong one

§0.55 left reciprocity as `totalInvariant k = 1` and the next brick as the *global splitting
criterion*

> `x ∈ Br(L/k)` ⟺ for every place `v`, `placeInvariant k v x ^ n_v = 1`, `n_v` the local degree.

The apparent obstruction was `localInvariantHom_baseChange`, whose hypothesis
`hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖` genuinely fails for a tower of adic completions:
`valued_adicCompletionComap` gives `v(comap z) = v(z) ^ e` and `normValued K L` restricts to
`v_K ^ n`, so neither normalization is an isometry.

That lemma is **not needed**.  `relative_eq_brauerTorsion_of_cyclic` is *intrinsic* — it is a
statement about the subgroup `Br(L_w / k_v) ≤ Br(k_v)`, not about comparing two invariant maps —
so the criterion factors as

```
x_v ∈ Br(L_w / k_v)  ⟺  x_v ∈ brauerTorsion k_v n_v  ⟺  inv_v(x) ^ n_v = 1,
```

the middle step being (a) and the right step `localInvariantHom_injective`.  The reverse direction
of the criterion is then ABHN over `L` (`eq_one_of_forall_invariant_eq_one`) plus
`BrauerGroup.baseChangeHom_comp`, since `(x_L)_w` and `(x_v)_{L_w}` are the same base change of `x`
read two ways.

### (c) The completion tower `k_v ⊆ L_w` is already built

The plumbing that (b) consumes turned out to be in the tree already, from the ABHN work:

| ingredient | source |
| --- | --- |
| `Algebra (v.adicCompletion k) (w.adicCompletion L)` | `instAlgebraAdicCompletion` (`CFT/Units/CompletionFinite.lean`), from the ring map `adicCompletionComap` |
| `IsScalarTower k (v.adicCompletion k) (w.adicCompletion L)` | `instIsScalarTowerBaseAdicCompletion` (`CFT/Units/CompletionGalois.lean`) |
| `FiniteDimensional (v.adicCompletion k) (w.adicCompletion L)` | `finiteDimensional_adicCompletion` — an **instance** |
| `IsGalois (v.adicCompletion k) (w.adicCompletion L)` | `isGalois_adicCompletion` — a theorem, so `attribute [local instance]` |
| the Galois group is the decomposition group | `restrictToBase`, `adicCompletionAut_restrictToBase`, `mem_range_algebraMap_iff_forall_stabilizer_smul_eq` |

So the only genuinely new step is `IsCyclic (L_w ≃ₐ[k_v] L_w)` for cyclic `L/k`, which is
`restrictToBase` packaged as an injective group homomorphism into `Gal(L/k)`.

That makes the splitting criterion a three-step chain, each step short:

1. **Hasse principle for relative Brauer groups.**  `x ∈ Br(L/k)` iff every completion of `L`,
   finite or infinite, splits `x`.  Forwards is monotonicity of `relative`; backwards is ABHN over
   `L` (`eq_one_of_forall_invariant_eq_one`) together with `BrauerGroup.baseChangeHom_comp`, since
   `(x_L)_w` and `x_{L_w}` are the same base change read two ways.
2. **Descend the local condition to `k_v`.**  `x ∈ Br(L_w / k)` iff `x_{k_v} ∈ Br(L_w / k_v)`, again
   just `baseChangeHom_comp` along `k → k_v → L_w`.
3. **Read it off as an invariant**, by (a): `Br(L_w / k_v) = brauerTorsion k_v [L_w : k_v]`, and
   membership in the latter is `placeInvariant k v x ^ [L_w : k_v] = 1` by injectivity of
   `localInvariantHom`.

### (d) Reciprocity itself, costed

With (c) in hand the two remaining routes are both explicit computations, not soft arguments:

* **Cyclotomic.** Every class of `Br(ℚ)` is split by a cyclic subfield of some `ℚ(ζ_m)`; the sum
  formula becomes the product formula for the local Artin symbols of `ℚ(ζ_m)/ℚ`.  At `p ∤ m` the
  extension is unramified and `localInvariant_apply_cyclicBrauerHom` already gives `v(a)/n`; at
  `p ∣ m` it is wildly ramified and needs the explicit local Artin map of `ℚ_p(ζ_{p^k})/ℚ_p`, i.e.
  Lubin–Tate.  That last piece is the expensive one.
* **One auxiliary tame prime.**  Split off a single auxiliary prime `q` and a cyclic
  `L ⊆ ℚ(ζ_q)` of degree `N ∣ q − 1`, so that the only ramified place is *tame*.  The tame symbol
  reduces to the unramified formula by bilinearity together with `⟨−a, a⟩ = 1` (which holds because
  `N_{K(a^{1/N})/K}(a^{1/N}) = (−1)^{N−1} a`) and the fact that the Kummer extension of a unit is
  unramified.  The local tame norm groups are then computable from
  `index_normSubgroup_eq_finrank_local`, `Φ_q(1) = q = N(1 − ζ_q)`, "a subgroup of index prime to
  `q` contains `1 + qℤ_q`", and uniqueness of the index-`N` subgroup of a cyclic group.
  **Caveat, established while costing this:** knowing the *kernels* of the local symbols does not
  pin the symbols themselves, so one genuine ramified (tame) computation survives, and routing it
  through the bilinear `kummerSymbol` of `CFT/Profinite/Symbol.lean` needs the **cup product ↔
  cyclic algebra bridge**, which is still on the deferred list.

The second route avoids Lubin–Tate entirely and is the one to take; its enabling lemma is that
bridge, and its prerequisite is the chain of (c).

---

## 0.57 Status (2026-08-31) — the chain of §0.56(c) is built: when a cyclic extension of number fields splits a Brauer class

The three-step chain named in §0.56(c) is now three files, all sorry- and axiom-free.

### (a) `CFT/Units/CompletionCyclic.lean` — the decomposition group is a subgroup

The local input of §0.56(a) is a statement about a *cyclic* extension of a local field, so applying
it at a place of a global cyclic extension needs the completion `L_w / k_v` to be cyclic.  It is,
for the cheapest possible reason: restriction

```
Gal(L_w | k_v) → Gal(L | k)
```

is **injective** (`restrictToBase_injective`), because an automorphism of `L_w` over `k_v` is
continuous (`continuous_algEquiv`, already in `Units/CompletionGalois.lean`) and `L` is dense in
`L_w`, so its values on `L` determine it.  Packaged as a group homomorphism `restrictToBaseHom`
(the `map_one'`/`map_mul'` proofs are `FaithfulSMul.algebraMap_injective` plus
`toAdicCompletion_restrictToBase`), Mathlib's `isCyclic_of_injective` then gives

```
isCyclic_algEquiv_adicCompletion : IsCyclic Gal(L | k) → IsCyclic Gal(L_w | k_v).
```

No decomposition-group theory, no `e·f·g`, no surjectivity: only injectivity is needed, and only
subgroup-heredity of cyclicity is used.

### (b) `CFT/Brauer/RelativeHasse.lean` — the Hasse principle for a fixed extension

`Brauer/HasseNoether.lean` and `Brauer/TotalInvariant.lean` state Albert–Brauer–Hasse–Noether for a
fixed *class*: a class of `Br(L)` which is locally trivial everywhere is trivial.  What the
splitting criterion needs is the same theorem read for a fixed *extension*:

```
mem_relative_iff_forall_completion :
  x ∈ Br(L | k) ↔ (∀ w finite, x ∈ Br(L_w | k)) ∧ (∀ U real, x ∈ Br(L_U | k)).
```

The forward direction is `BrauerGroup.relative_le_relative` twice.  The reverse direction applies
ABHN over `L` to `base_L(x)` and, at each place, rewrites
`base_{L_w}(base_L(x)) = base_{L_w}(x)` with `BrauerGroup.baseChangeHom_comp` — the *only* content
is that functoriality of base change lets the same class be read either way.

The complex places drop out: `relative_completion_eq_top_of_isComplex_extension` transports
`BrauerGroup.relative_eq_top_of_isAlgClosed ℂ` along `AlgEquiv.ofRingEquiv` applied to
`InfinitePlace.Completion.ringEquivComplexOfIsComplex`, whose compatibility with the base is
`extensionEmbedding_coe` after `IsScalarTower.algebraMap_apply k L U.Completion`.  Finally

```
mem_relative_adicCompletion_iff_baseChange :
  x ∈ Br(L_w | k) ↔ base_{k_v}(x) ∈ Br(L_w | k_v),   v = w ∩ k
```

is again `baseChangeHom_comp`, and it is what turns a global condition into a local-field one.

### (c) `CFT/Brauer/RelativeCyclic.lean` — the criterion

Putting (a), (b) and §0.56(a) together:

```
mem_relative_adicCompletion_iff_pow_placeInvariant :
  x ∈ Br(L_w | k)  ↔  inv_v(x) ^ [L_w : k_v] = 0

mem_relative_iff_forall_pow_placeInvariant :
  x ∈ Br(L | k)  ↔  (∀ w, [L_w : k_v] · inv_v(x) = 0) ∧ (∀ U real, x ∈ Br(L_U | k)).
```

Note which hypotheses are *absent*.  There is no unramifiedness assumption; there is no isometry
hypothesis `‖·‖_{k_v} = ‖·‖_{L_w}`, which genuinely fails for an adic tower and is why
`Brauer/LocalReciprocity.lean`'s `relative_eq_brauerTorsion` — the same statement for an arbitrary
finite Galois extension of local fields — cannot be used here; and there is no restriction on the
residue characteristic, since `exists_hasResidueChar_adicCompletion` supplies one for every place.
The cyclic hypothesis is the price paid for dropping the isometry, and it is free for us: the
extensions reciprocity is proven against are cyclic anyway.

### (d) What is left, unchanged

Reciprocity, `totalInvariant k = 1`.  The route is §0.56(d)'s second one, and its remaining
prerequisite is the single deferred item

> **the cup product ↔ cyclic algebra bridge**: for `K ∋ ζ_n`, `b ∈ K^×` and `L = K(b^{1/n})`
> cyclic of degree `n` with `σβ = ζβ`, the class `kummerSymbolUnits a b` of
> `Profinite/Symbol.lean` is the class `cyclicBrauerHom hσ a` of `Brauer/CyclicNorm.lean`.

That bridge is what makes `localSymbol` (`Brauer/LocalSymbol.lean`: already bimultiplicative,
`n`-torsion, trivial on `n`-th powers) *computable*: it identifies its kernel with a norm group, and
from `N_{K(x^{1/n})|K}(x^{1/n}) = (−1)^{n−1} x` one gets `⟨x, −x⟩ = 1`, hence skew-symmetry by the
usual expansion of `⟨ab, −ab⟩ = 1`, hence the tame value at the auxiliary prime from the *unramified*
formula `localInvariant_apply_cyclicBrauerHom` on the other argument.  Without it the symbol is a
pairing whose values are never computed, and reciprocity is a statement about values.

Build: 9478 jobs green, zero warnings, zero sorries outside the comparator; all ten new
declarations have axioms `[propext, Classical.choice, Quot.sound]`.

---

## 0.58 Status (2026-08-31) — step 1 of the bridge: the power symbol *is* a carry cocycle

`CFT/Profinite/SymbolCyclic.lean`, sorry- and axiom-free.  This is the cohomological half of the
bridge named in §0.57(d): it rewrites `kummerSymbolUnits` — defined as a cup product of two Kummer
classes — as (the inverse of) the class of the *explicit cyclic-algebra cocycle* of
`GroupCohomology/Cyclic.lean`, with no finite level, no crossed product and no Brauer group in
sight.

### (a) The dictionary

Fix `n`, a primitive `n`-th root `ζ ∈ k`, and Kummer data
`h : IsKummerData k Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n`.  For `a : kˣ` write

* `Z := kummerRootUnit Ω hζ : Ωˣ` — the image of `ζ` in the units of `Ω`, so `Z ^ n = 1`;
* `R := h.root a : Ωˣ` — a chosen `n`-th root, so `R ^ n = a`;
* `α := kummerChar h a : Gal(Ω/k) → ZMod n` — the Kummer cochain read additively.

`kummerChar_mul` says `α` is a homomorphism (the action on the coefficients is trivial, so the
cocycle identity *is* additivity), and `smul_root_eq_kummerRootUnit_pow` says

```
g • R = Z ^ (α g).val * R.
```

### (b) The computation

The one-cochain `u g := R ^ (β g).val`, `β := kummerChar h b`, has coboundary

```
coboundary₂ u (g, g') = Z ^ ((α g).val * (β g').val) · ( R ^ ((β g).val + (β g').val)
                                                        / R ^ (β g + β g').val ).
```

The first factor is exactly the cup product `coeffMap₂ h.unitsHom (mulCup₁₁ (mulZMod n) …)` whose
class is `kummerSymbolUnits h (mulZMod n) a b`; the identification uses `ZMod.val_mul` together
with `pow_mod_of_pow_eq_one` for `Z ^ n = 1`, so that reducing the product of residues modulo `n`
costs nothing.  The second factor is the **carry**: by `pow_val_add_div` (a two-line lemma valid in
any group) it is `1` when `(β g).val + (β g').val < n` and `R ^ n = a` otherwise — i.e. it is
`kummerCyclicCocycle h a b`, the image under `Gal(Ω/k) → ZMod n` of `cyclicCocycle`.  Hence

```
kummerSymbolUnits h (mulZMod n) a b · smoothH2Mk (kummerCyclicCocycle h a b) = 1.
```

### (c) Two things that made this cheap

* `hsym : kummerSymbolUnits h Φ a b = smoothH2Mk (coeffMap₂ h.unitsHom (mulCup₁₁ Φ …)) _ _ := rfl`.
  The whole chain `kummerSymbolUnits → coeffH2 → cupSmoothH1 → kummerHom → smoothH1Mk` is
  definitional, because `cupSmoothH1_apply` and `coeffH2_smoothH2Mk` are themselves `rfl`.  No
  rewriting under proof-argument metavariables was needed.
* Smoothness of both the carry cocycle and the correcting cochain is inherited verbatim from
  smoothness of the Kummer cochain of `b`: the same open normal subgroup works, since both are
  built out of `β` alone.

### (d) What step 2 needs

The remaining half is purely a *level* statement, with no cohomology in it:

> if `E ⊆ Ω` is a finite cyclic Galois level with generator `σ₀`, of degree exactly `n`, whose
> discrete logarithm matches the Kummer character of `b`, then
> `inflateCocycle Ω (cyclicUnitCocycle σ₀ a) = kummerCyclicCocycle h a b`.

Feeding that to `mk_csa_eq_smoothBrauer` identifies `smoothBrauer` of the symbol with the class of
the crossed product, i.e. with `cyclicBrauerHom hσ₀ a`, and feeding it instead to
`isMulCoboundary₂_of_coboundary₂_inflateCocycle` together with
`isMulCoboundary₂_cyclicUnitCocycle_iff` gives the norm criterion
`kummerSymbolUnits a b = 1 ↔ a ∈ N_{E/k}(Eˣ)` with no Brauer group at all.

Build: 9479 jobs green, zero warnings, zero sorries outside the comparator; all eight new
declarations have axioms `[propext, Classical.choice, Quot.sound]`.

---

## 0.59 Status (2026-09-01) — step 2: the bridge of §0.57(d) is built

`CFT/Brauer/SymbolCyclicAlgebra.lean`, sorry- and axiom-free.  With §0.58 the symbol is the inverse
of the class of the carry cocycle `kummerCyclicCocycle h a b`; what remains is that that cocycle is
*inflated from a finite level*, which is a statement with no cohomology in it at all.

### (a) The one hypothesis

The carry cocycle reads only the Kummer character `β := kummerChar h b`.  The cyclic algebra
cocycle of a level `E` reads only the discrete logarithm `dlog σ₀` of `Gal(E/k)`.  So the *only*
thing the comparison needs is that the two carry conditions agree:

```lean
hcarry : ∀ g g',  (dlog σ₀ (g|E)).val + (dlog σ₀ (g'|E)).val < Nat.card Gal(E/k)
                ↔ (β g).val + (β g').val < n
```

and then `inflateCocycle Ω (cyclicUnitCocycle σ₀ a) = kummerCyclicCocycle h a b` pointwise, by
`if_pos`/`if_neg` and `IsScalarTower.algebraMap_apply` on the two branches.  Stating the hypothesis
this way is deliberate: it is satisfied not only when `[E : k] = n` and `dlog σ₀ (g|E) = β g`
(`carry_iff_of_dlog_eq`, a one-line `rw`), but also when `b` is a `d`-th power and the character
lands in the subgroup of index `d`, where the level has degree `n / d` and the carries still match.

### (b) The two conclusions

Feeding the equality to `mk_csa_eq_smoothBrauer` at the level `E` gives

```lean
smoothBrauerHom (kummerSymbolUnits h (mulZMod n) a b) = (cyclicBrauerHom hσ₀ a)⁻¹
```

— the bridge named in §0.57(d).  Composing with `smoothBrauerHom_injective` and
`mem_ker_cyclicBrauerHom_iff` turns it into the statement the downstream computations actually
consume:

```lean
kummerSymbolUnits h (mulZMod n) a b = 1 ↔ ∃ c : Eˣ, Algebra.norm k (c : E) = (a : k)
```

**the power symbol is trivial exactly when its first argument is a norm from the level.**  This is
what makes `localSymbol` computable: its kernel is now a norm group, and its *values* are local
invariants of cyclic algebras, so `localInvariant_apply_cyclicBrauerHom` applies.

### (c) What is still missing before `⟨−a, a⟩ = 1`

Nothing cohomological: only the *construction* of the level.  Both theorems above take `E`, `σ₀`
and `hcarry` as hypotheses, and the remaining Kummer-theory brick is to produce them from `b`
alone:

> `E := k⟮b^{1/n}⟯` is finite Galois with `Gal(E/k)` cyclic, the Kummer character descends to an
> injective character of `Gal(E/k)`, and if the character is onto `ZMod n` then a preimage of `1`
> generates and its discrete logarithm is the character.

That is the next file.  With it, `N_{k(a^{1/n})/k}(a^{1/n}) = (−1)^{n−1} a` gives
`⟨(−1)^{n−1} a, a⟩ = 1` directly from the norm criterion, and skew-symmetry follows by expanding
`⟨(−1)^{n−1} ab, ab⟩ = 1`.

Build: 9480 jobs green, zero warnings, zero sorries outside the comparator; all seven new
declarations have axioms `[propext, Classical.choice, Quot.sound]`.

---

## 0.60 Status (2026-09-01) — the level itself: `k⟮b^{1/n}⟯` is cyclic and carries the character

`CFT/Profinite/KummerLevel.lean`, sorry- and axiom-free.  This is the brick §0.59(c) named: it
*constructs* the `E`, `σ₀` and `hcarry` that `Brauer/SymbolCyclicAlgebra.lean` takes as hypotheses.

### (a) The only geometric input

Everything follows from one identity already in the tree,
`smul_root_eq_kummerRootUnit_pow`:

```
g • R = Z ^ (β g).val * R,     R := h.root b,  Z := ζ in Ω,  β := kummerChar h b.
```

Read three ways it gives the whole file:

* `Z ^ j = 1` only for `n ∣ j` (`isPrimitiveRoot_kummerRootUnit`, which is
  `IsPrimitiveRoot.map_of_injective` along `Units.map (algebraMap k Ω)`), so **`g` fixes `R` exactly
  when `β g = 0`** (`smul_root_eq_self_iff`).
* `Z` lies in the base, so `g • R` lies in `k⟮R⟯`: the level `kummerLevel h b := k⟮R⟯` is stable
  under every automorphism, hence **normal**, hence — separability being inherited downwards —
  **finite Galois** (`isGalois_kummerLevel`; finiteness is `adjoin.finiteDimensional` applied to the
  monic `X ^ n - C b`).
* combining the two with `fixingSubgroup_adjoin_simple_eq_stabilizer` (which, thanks to its
  `omit`ed finiteness hypotheses, applies to the *infinite* `Ω`): **the subgroup fixing the level is
  the kernel of the Kummer character** (`mem_fixingSubgroup_kummerLevel_iff`).

### (b) Why no quotient group appears

The obvious move — descend `β` to a character of `Gal(E/k)` — needs `QuotientGroup.lift` and then
fights the dependent type `ZMod (Nat.card Gal(E/k))`.  It is avoidable.  Composing
`restrictNormalHom_ker` with (a) gives the single working lemma

```lean
restrictNormalHom_kummerLevel_eq_iff :  g|E = g'|E  ↔  β g = β g'
```

and everything else is read off it.  If `β g₀ = 1` for some `g₀`, put `σ₀ := g₀|E`; then
`g|E = σ₀ ^ (β g).val` for every `g` (apply the lemma to `g` and `g₀ ^ (β g).val`), so `σ₀`
generates by surjectivity of restriction (`restrictNormalHom_surjective_level`), `orderOf σ₀ = n`
by `orderOf_eq_iff`, and `pow_eq_pow_iff_modEq` converts `σ₀ ^ (dlog σ₀ (g|E)).val = σ₀ ^ (β g).val`
into the equality of the two residues *as naturals*, both being `< n`.  That is exactly the shape
`carry_iff_of_dlog_eq` wants:

```lean
exists_generator_kummerLevel (hg₀ : kummerChar h b g₀ = 1) :
    ∃ σ₀ : Gal(E/k), (∀ x, x ∈ Subgroup.zpowers σ₀) ∧ Nat.card Gal(E/k) = n ∧
      ∀ g, (dlog σ₀ (g|E)).val = (kummerChar h b g).val
```

Stating the conclusion with `.val` on both sides is the point: no residue ever has to be
transported along `Nat.card Gal(E/k) = n`.

### (c) What it unlocks, and the one gap that remains

Feeding this to §0.59(b) gives, for any `b` whose character is onto,

```
kummerSymbolUnits h (mulZMod n) a b = 1  ↔  a ∈ N_{k⟮b^{1/n}⟯ | k}( k⟮b^{1/n}⟯ˣ ).
```

With `a := (−1)^{n+1} b` and the norm of the generator this is `⟨(−1)^{n+1} b, b⟩ = 1`.  But
skew-symmetry needs that relation for `a`, `b` *and* `ab`, and the character of a product need not
be onto even when both factors' are — indeed the character of an `n`-th power is zero.  So the
general level, of degree `m ∣ n` with the character landing in the subgroup of index `t = n / m`,
is genuinely required; there `N(β^t) = (−1)^{(m+1)t} b` and the missing `(−1)^{t−1}` is
`N(ζ^{t/2})` when `t` is even.  That, plus the norm computation itself, is the next file.

Build: 9481 jobs green, zero warnings, zero sorries outside the comparator; all eighteen new
declarations have axioms `[propext, Classical.choice, Quot.sound]`.

---

## 0.61 Status (2026-09-01) — the gap of §0.60(c) is closed: the power symbol is skew-symmetric

`CFT/Profinite/KummerLevelDegree.lean` and `CFT/Brauer/SymbolNorm.lean`, both sorry- and axiom-free.
Together they remove the "character is onto" hypothesis and prove `⟨a,b⟩⟨b,a⟩ = 1` for *every* pair
of units.

### (a) The general level (`KummerLevelDegree.lean`)

`restrictNormalHom_kummerLevel_eq_iff` of §0.60(b) says `g|E = g'|E ↔ β g = β g'`, i.e. the fibres
of restriction to `E := kummerLevel h b` are exactly the fibres of `β := kummerChar h b`.  Since
restriction is onto (`restrictNormalHom_surjective_level`), that is precisely the statement that
`β` *descends* to `Gal(E/k)`.  The descent is written without any quotient group: pick, for each
`σ : Gal(E/k)`, a preimage (`levelPreimage`, by `Classical.choose` of surjectivity) and set

```lean
levelChar h b σ := kummerChar h b (levelPreimage h b σ)
```

Well-definedness, `levelChar (σ * τ) = levelChar σ + levelChar τ`, and injectivity are all one
application of the fibre lemma.  Injectivity of a homomorphism `Gal(E/k) ↪ ZMod n` gives at once

```lean
card_gal_kummerLevel_dvd :  m ∣ n,        m := Nat.card Gal(E/k)
card_nsmul_kummerChar    :  m • β g = 0
```

(the second by Lagrange in `Gal(E/k)`, transported through the descent).

**The counting step.**  Let `t := n / m`.  `m • x = 0` in `ZMod n` says `n ∣ m * x.val`, i.e.
`t ∣ x.val`, so the image of `levelChar` sits inside the set of multiples of `t`.  But the image has
exactly `m` elements (injectivity) and there are exactly `m` multiples of `t` in `ZMod n`
(`j ↦ (j*t : ZMod n)` is injective on `range m` because `j*t < n`).  `Finset.eq_of_subset_of_card_le`
turns the inclusion into an equality, so `t` itself is in the image: some `σ₀` has
`levelChar σ₀ = t`.  Then `σ₀` generates (its `levelChar`-image already exhausts the group) and

```lean
exists_generator_kummerLevel_index :
    ∃ σ₀ t, (∀ x, x ∈ Subgroup.zpowers σ₀) ∧ 0 < t ∧ m * t = n ∧
      ∀ g, (kummerChar h b g).val = t * (dlog σ₀ (g|E)).val
```

Multiplying the discrete logarithm by `t` is order-preserving on the relevant range, so
`carry_iff_of_index` converts the carry condition of `dlog` into the carry condition of `β`, with
**no hypothesis at all on `b`**.  That is the last input `Brauer/SymbolCyclicAlgebra.lean` was
missing:

```lean
kummerSymbolUnits_eq_one_iff_norm_kummerLevel (a b : kˣ) :
    ⟨a, b⟩ = 1  ↔  ∃ c : (k⟮b^{1/n}⟯)ˣ, N(c) = a
```

### (b) The norm of the root (`SymbolNorm.lean`)

Write `R := h.root b`, `x := kummerLevelGen h b` for `R` read inside `E`, and `m := Nat.card
Gal(E/k)` as above.  `card_nsmul_kummerChar` says `n ∣ (β g).val * m`, so in

```
g • R^m = (Z^{(β g).val})^m · R^m = (Z^{(β g).val · m}) · R^m = R^m
```

the root of unity disappears: **`R^m` is fixed by every automorphism of `Ω`**.  Restriction to `E`
is onto, so `x^m` is fixed by every element of `Gal(E/k)`, and — `E` being *finite* Galois —
`IsGalois.mem_range_algebraMap_iff_fixed` puts it in the base: `x^m = c` for some `c : k`.

Hence `X^m - C c` is a monic polynomial killing `x`, so `minpoly k x ∣ X^m - C c`; and
`natDegree (minpoly k x) = [k⟮R⟯ : k] = m` by `adjoin.finrank` plus `IsGalois.card_aut_eq_finrank`.
Two monic polynomials of the same degree, one dividing the other, are equal
(`Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff`), so

```
minpoly k x = X^m - C c,   N_{E|k}(x) = (-1)^m · coeff 0 = (-1)^{m+1} c
```

by `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly` on `adjoin.powerBasis`.

Now raise to the index.  `c^t = b` (both have the same image `R^{mt} = R^n = b` in `Ω`), so

```
N(x^t) = ((-1)^{m+1} c)^t = (-1)^{mt + t} b = (-1)^{n+t} b.
```

For odd `t` that is already `(-1)^{n+1} b`.  For even `t = 2s` the correction is a *base* element:
`N(ζ^s) = ζ^{sm}` and `sm = n/2`, so `ζ^{sm}` is a primitive second root of unity, i.e. `-1`
(`IsPrimitiveRoot.pow_of_dvd` then `eq_neg_one_of_two_right`), and `x^t · ζ^s` has norm
`(-1)^{n+t} b · (-1) = (-1)^{n+1} b`.  Either way

```lean
exists_norm_eq_neg_one_pow (b : kˣ) : ∃ w ≠ 0, N_{k⟮b^{1/n}⟯ | k}(w) = (-1)^{n+1} b
```

and therefore `⟨(-1)^{n+1} b, b⟩ = 1` for every `b`.

### (c) Skew-symmetry falls out of bilinearity

Abbreviate `S x y := ⟨x, y⟩` and `ε := (-1)^{n+1} : kˣ`.  Applying (b) to `a`, to `b`, and to `ab`,
and expanding `S (εa) a`, `S (εb) b`, `S (ε(ab)) (ab)` by bilinearity of `kummerSymbolUnits` (the
target `SmoothH2` is a commutative group, so `kˣ →* kˣ →* SmoothH2` is bilinear on the nose):

```
S ε a · S a a = 1,   S ε b · S b b = 1,   (S ε a · S ε b) · ((S a a · S b a) · (S a b · S b b)) = 1.
```

Cancelling the first two relations inside the third leaves exactly `S a b · S b a = 1`.  The
rearrangement is a two-line lemma in an abstract `CommGroup` (`mul_swap_aux`), so no cohomology is
touched:

```lean
kummerSymbolUnits_mul_swap (a b : kˣ) :  ⟨a, b⟩ · ⟨b, a⟩ = 1
```

### (d) Lean notes

* Never `rw` an equation that rewrites *away from* `n` in a goal mentioning `kummerLevel h b`: `n`
  occurs in the `NeZero n` instance argument, so the motive is not type correct.  Rewriting *to* `n`
  is fine.  The arithmetic of `carry_iff_of_index` is therefore hoisted into a fully abstract
  `∀ M N T x y : ℕ, 0 < T → M * T = N → (x + y < M ↔ T*x + T*y < N)`.
* `adjoin.powerBasis hint` lives over `↥k⟮R⟯`, whose instances are only *defeq* to those of
  `↥(kummerLevel h b)`; `rw` sees two different terms.  Restating the power-basis norm with
  `have hgoal : ... := hnorm` forces the coercion and costs nothing.
* Restriction is best applied through `Subtype.ext` plus `AlgEquiv.restrictNormalHom_apply` (stated
  with the `SetLike` coercion), not through `algebraMap` injectivity.

Build: 9483 jobs green, zero warnings, zero sorries outside the comparator; all twenty-four new
declarations have axioms `[propext, Classical.choice, Quot.sound]`.

### (e) What is left for reciprocity

The symbol is now a genuine skew-symmetric pairing on `kˣ × kˣ` with values in the Brauer group, and
`smoothBrauerHom_kummerSymbolUnits` computes its class as a cyclic algebra.  What remains of the
§0.56(d) plan is the *local* evaluation: the tame value at the auxiliary prime via
`localInvariant_apply_cyclicBrauerHom`, and then `totalInvariant k = 1` by the one-auxiliary-prime
route (`Φ_q(1) = q = N(1 - ζ_q)`, `index_normSubgroup_eq_finrank_local`, "a subgroup of index prime
to `q` contains `1 + qℤ_q`", uniqueness of the index-`N` subgroup of a cyclic group).

---

## 0.62 Status (2026-09-01) — the Steinberg relation: `⟨1-a, a⟩ = 1`

`CFT/Brauer/SymbolSteinberg.lean`, sorry- and axiom-free.  With §0.61 this gives the power symbol
**all three universal relations of Milnor K-theory**: bilinearity (free, the symbol is a
`kˣ →* kˣ →* SmoothH2`), skew-symmetry (§0.61(c)), and now Steinberg.  Those are exactly the
relations every local computation of the symbol is assembled from, so this is the last purely
*algebraic* input before the local evaluation of §0.61(e).

### (a) The norm of a base element minus the root

The one new general tool.  For a power basis `pb : PowerBasis K S`, multiplication by `pb.gen` has
characteristic polynomial `minpoly K pb.gen` (`charpoly_leftMulMatrix`), and `Matrix.eval_charpoly`
evaluates a characteristic polynomial as `det (r • 1 - M)`.  Since `Algebra.norm` *is* that
determinant (`Algebra.norm_eq_matrix_det`) and `leftMulMatrix` is an algebra map, the two sides are
literally the same determinant:

```lean
norm_algebraMap_sub_powerBasis_gen (pb : PowerBasis K S) (r : K) :
    Algebra.norm K (algebraMap K S r - pb.gen) = (minpoly K pb.gen).eval r
```

(four rewrites and a `congr 1`).  This is the general form of "the norm is the constant coefficient
of the minimal polynomial up to sign" that §0.61(b) used at `r = 0`, and it is what makes the
Steinberg computation cheap: **no Galois conjugates are ever enumerated.**

Applied to `pb := kummerLevelPowerBasis h b` (the `adjoin.powerBasis` of the chosen root, retyped
over `↥(kummerLevel h b)` — the §0.61(d) defeq dance again) together with
`minpoly_kummerLevelGen = X^m - C c` from §0.61(b), and after factoring
`1 - e·x = e·(e⁻¹ - x)`:

```lean
norm_one_sub_algebraMap_mul_kummerLevelGen (e ≠ 0) :
    N_{E|k}(1 - e·x) = e^m · ((e⁻¹)^m - c) = 1 - e^m · c
```

### (b) `1 - a` is a norm from the level of `a`

Keep `m := [E:k]`, `t := n/m`, `x^m = c`, `c^t = a` of §0.61.  Take `e := ζ^j` for `j < t`: then
`e^m = (ζ^m)^j`, and `ζ^m` is a *primitive `t`-th root of unity* (`IsPrimitiveRoot.pow_of_dvd`,
`n/m = t`).  So by (a) the `t` elements `1 - ζ^j x` of `E` have norms

```
N(1 - ζ^j x) = 1 - (ζ^m)^j · c,      j = 0, …, t-1,
```

and those are exactly the values at `X = 1` of the linear factors of `X^t - C a`
(`X_pow_sub_C_eq_prod` for the primitive `t`-th root `ζ^m` and the root `c` of `c^t = a`).  Hence
their product is `1 - a`, and the norm is multiplicative:

```lean
exists_norm_eq_one_sub (a : kˣ) (ha : a ≠ 1) :
    ∃ w ≠ 0, N_{k⟮a^{1/n}⟯ | k}(w) = 1 - a,      w := ∏_{j<t} (1 - ζ^j·x)
```

Note the two degenerate cases are handled for free: `t = 1` gives the classical
`1 - a = N(1 - a^{1/n})`, and `w ≠ 0` is read off backwards from `N(w) = 1 - a ≠ 0`.

Feeding this into `kummerSymbolUnits_eq_one_iff_norm_kummerLevel` (§0.61(a)):

```lean
kummerSymbolUnits_one_sub      (u = 1 - a) :  ⟨1 - a, a⟩ = 1
kummerSymbolUnits_self_one_sub (u = 1 - a) :  ⟨a, 1 - a⟩ = 1     -- by skew-symmetry
```

### (c) The companion relation `⟨a, -a⟩ = 1`

Purely formal from (b).  For `a ≠ 1`, `-a = (1-a)/(1-a⁻¹)` in `kˣ`, and both
`⟨a, 1-a⟩ = 1` (Steinberg) and `⟨a, 1-a⁻¹⟩ = 1` hold — the latter because `⟨a⁻¹, 1-a⁻¹⟩ = 1` is
Steinberg for `a⁻¹` and `⟨·, v⟩` is a homomorphism, so `⟨a, v⟩ = ⟨a⁻¹, v⟩⁻¹`.  The case `a = 1` is
`map_one`.

```lean
kummerSymbolUnits_neg_self (a : kˣ) :  ⟨a, -a⟩ = 1
```

### (d) Lean notes

* `charpoly_leftMulMatrix` is in the *root* namespace (`Mathlib/LinearAlgebra/Matrix/Charpoly/
  Minpoly.lean`), not in `Matrix`; `Matrix.eval_charpoly` is `M.charpoly.eval t = (scalar t - M).det`.
* `hζ.pow_of_dvd hm0 ⟨t, hmt⟩ : IsPrimitiveRoot (ζ^m) (n/m)` — the exponent is `n/m`, so convert it
  to `t` *before* using it; and by §0.61(d) `n / m = t` must be proved by rewriting `m*t → n` inside
  `Nat.mul_div_cancel_left`, never by rewriting `n → m*t` in the goal.
* `Algebra.norm_zero` turns "`N(w) = 1 - a ≠ 0`" into `w ≠ 0` with no extra hypotheses, which is
  much cheaper than showing each factor `1 - ζ^j x` is nonzero.

Build: 9484 jobs green, zero warnings, zero sorries outside the comparator; all twelve new or
refactored declarations have axioms `[propext, Classical.choice, Quot.sound]`.

### (e) What is left for reciprocity

Unchanged from §0.61(e): the *local* evaluation of the symbol (the tame value at an auxiliary prime,
then `totalInvariant k = 1`).  The relations of (a)–(c) are the algebra that computation runs on:
the tame symbol at a place of residue characteristic prime to `n` is determined by bilinearity,
skew-symmetry and `⟨u, -u⟩ = 1` once one knows `⟨u, v⟩ = 1` for two *units* `u, v`, which is the
statement that a Kummer extension by a unit is unramified.  That is the next brick.

---

## 0.63 Status (2026-09-01) — the brick of §0.62(e): `⟨u, v⟩ = 1` for two units

Three new modules, all sorry- and axiom-free: `CFT/Local/GaussNorm.lean`,
`CFT/Local/RadicalUnramified.lean`, `CFT/Brauer/LocalSymbolUnits.lean`.  Build 9487 jobs green,
zero warnings; every new declaration has axioms `[propext, Classical.choice, Quot.sound]`.

With this the **tame symbol is completely determined**: bilinearity (free), skew-symmetry (§0.61),
Steinberg and `⟨a, -a⟩ = 1` (§0.62), and now `⟨u, v⟩ = 1` for two units, so the symbol only depends
on the *values* of its two arguments and on `⟨π, u⟩`.

### (a) The Gauss norm as the way to recognise an unramified extension

The mathematical statement wanted is: *`K` complete with a rank-one valuation, `L = K(x)` with
`minpoly K x = F`, `F` monic with integral coefficients whose reduction `F̄` is irreducible over the
residue field `𝓀[K]`; then `L/K` is unramified.*

The route that the repository already had (`exists_valued_of_spectralNorm`) needs exactly one input:

```lean
hval : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ spectralNorm K L z = ‖c‖
```

("every absolute value of `L` is already an absolute value of a scalar" — which *is*
unramifiedness, since the value group does not grow).  The cheap way to get `hval` is **not** to
compute norms, matrices or resultants but to *build* the absolute value:

* write `z ∈ L` in the power basis `1, x, …, x^{d-1}` — `repPoly pb z : K[X]` of degree `< d`;
* take the **Gauss (sup) norm** `coordNorm pb z := (repPoly pb z).supNorm`, the largest absolute
  value of a coordinate;
* the only nontrivial axiom is multiplicativity, and it reduces to
  `coordNorm z = coordNorm w = 1 ⇒ coordNorm (z·w) = 1` by scaling;
* that in turn is: the product of two integral representatives, reduced `%ₘ F`, still has a
  coefficient of absolute value one — i.e. `(P·Q) %ₘ F` does not reduce to `0` mod the maximal
  ideal.  Over `R/𝔪 = 𝓀[K]` the quotient `𝓀[X]/(F̄)` is a **field** because `F̄` is irreducible, so
  `P̄ ≠ 0`, `Q̄ ≠ 0` force `F̄ ∤ P̄·Q̄`, and `deg((P·Q) %ₘ F) < deg F` then forbids
  `(P·Q) %ₘ F ≡ 0`;
* `coordNorm` is therefore an `AbsoluteValue L ℝ` extending `‖·‖` on `K`, so by
  `spectralNorm_unique_field_norm_ext` it **equals the spectral norm**;
* and the values of `coordNorm` are literally `‖c‖` for `c` a coordinate of `z`, which is `hval`.

```lean
spectralNorm_eq_coordNorm  (hF : F.Monic) (hFmin : F.map ι = minpoly K pb.gen)
    (hirr : Irreducible (F.map (IsLocalRing.residue 𝒪[K]))) (z : L) :
    spectralNorm K L z = coordNorm pb z
exists_valued_of_residue_irreducible … :
    ∃ (_ : Valued L ℤᵐ⁰) (_ : CompleteSpace L) (m : ℤ) (e' : ℕ), … ∧ IsUnramifiedValued K L ∧ …
```

Mathlib has `Polynomial.supNorm` and its basic lemmas but **no multiplicativity**, so
`supNorm_C_mul` and the ultrametric `supNorm_add_le` are proved here too.

### (b) A radical extension by a unit is unramified

Now specialise `F = X^ℓ - C c` with `c` a **unit** of `𝒪[K]` and `ℓ` **prime**, `ℓ` prime to the
residue characteristic `p`.  Two steps:

1. *Hensel.* If `c̄ = ȳ^ℓ` in `𝓀[K]` then `c/y^ℓ ≡ 1`, and the repository's
   `exists_pow_eq_of_valued_sub_lt_one` (a unit congruent to one is an `n`-th power whenever
   `p ∤ n`) gives `c ∈ (K^×)^ℓ`:

   ```lean
   exists_pow_eq_of_residue_pow_eq (hres) (hd : d ≠ 0) (hpd : ¬ p ∣ d)
       (hc : v c = 1) (hy : y ^ d = residue c) : ∃ z : K, z ^ d = c
   ```

2. *Irreducibility.* For a **prime** exponent, `X^ℓ - C a` is irreducible exactly when `a` is not
   an `ℓ`-th power (`X_pow_sub_C_irreducible_iff_of_prime`) — no `4 ∣ d` clause to worry about, and
   this is exactly the case Scholz–Reichardt needs.  So `c ∉ (K^×)^ℓ ⇒ c̄ ∉ (𝓀^×)^ℓ ⇒ X^ℓ - C c̄`
   irreducible, and (a) applies.

Combining with `index_normSubgroup_eq_finrank_local` (norm index of a cyclic local extension = the
degree) and `mem_normSubgroup_of_unitVal_eq_zero` (in an unramified extension a unit of value `0`
is a norm; `v(a) = v(N a) = v(a)^{[L:K]} = 1`):

```lean
mem_normSubgroup_of_radical_unit [IsGalois K L] [IsCyclic Gal(L/K)] (pb : PowerBasis K L)
    (hl : ℓ.Prime) (hpl : ¬ p ∣ ℓ) (hc : v c = 1) (hmin : minpoly K pb.gen = X ^ ℓ - C c)
    (hres : HasResidueChar K p e) (ha : v a = 1) : a ∈ normSubgroup K L
```

### (c) `⟨u, v⟩ = 1`

`kummerSymbolUnits_eq_one_iff_norm_kummerLevel` (§0.61(a)) says `⟨a, b⟩ = 1` iff `a` is a norm from
the level `E := k⟮b^{1/n}⟯`.  With `n = ℓ` prime, `[E:k] ∣ ℓ` leaves two cases:

* `[E:k] = 1`: then `a = N(a)` because `N ∘ algebraMap = (·)^{[E:k]} = id`;
* `[E:k] = ℓ`: then §0.61(b) gives `minpoly k x = X^ℓ - C c` with `algebraMap c = x^ℓ`, and
  `x^ℓ = algebraMap b` by the definition of the chosen root, so `c = b` — the minimal polynomial is
  `X^ℓ - C b`, a **radical extension by a unit**, and (b) applies.

`IsCyclic Gal(E/k)` comes for free from `exists_generator_kummerLevel_index` (§0.60).

```lean
kummerSymbolUnits_eq_one_of_valued_eq_one (hn : n.Prime) (hpn : ¬ p ∣ n) (hres)
    (ha : v a = 1) (hb : v b = 1) : kummerSymbolUnits h (mulZMod n) a b = 1
localSymbol_eq_one_of_valued_eq_one … : localSymbol hres hm hζ a b = 1
```

The bridge from the power symbol to the norm residue symbol is one `rw`
(`localKummerSymbol = invariantEquiv ∘ kummerSymbolUnits`), so §0.61 and §0.62 are lifted at the
same time:

```lean
localSymbol_mul_swap      : ⟨a,b⟩ · ⟨b,a⟩ = 1
localSymbol_one_sub       : ⟨1-a, a⟩ = 1
localSymbol_self_one_sub  : ⟨a, 1-a⟩ = 1
localSymbol_neg_self      : ⟨a, -a⟩ = 1
```

### (d) Lean notes

* `Polynomial.degree_sum_fin_lt` is stated with `C (f i) * X ^ i`, **not** `monomial i (f i)`;
  unifying against a `monomial` sum blows the heartbeat budget at `whnf`.  Rewrite with
  `← Polynomial.C_mul_X_pow_eq_monomial` first.
* Use `IsLocalRing.residue_eq_zero_iff`, not `Ideal.Quotient.eq_zero_iff_mem` — the latter's pattern
  does not match `IsLocalRing.residue`.  And `rw` does not see through `Ne`, so insert `ne_eq`.
* `Valued.toNormedField` and the `IsUltrametricDist L` instance need only `[Valued L Γ₀]` and
  `Valuation.RankOne` — **no `CompleteSpace`** — so the Gauss-norm section splits into three
  (`CoordNorm` / `Mul` adds `FiniteDimensional` / `Spectral` adds `CompleteSpace`) and the
  `unusedSectionVars` linter stays quiet without a single `omit`.
* `exists_valued_of_spectralNorm` was hiding the compatibility `v y = v (N_{L|K} y)` (which is
  `rfl` inside its own proof); it is now the first conjunct of the existential, which is what makes
  "`a` is a unit ⇒ `unitVal (algebraMap a) = 0`" a two-line computation.
* `mem_normSubgroup_of_radical_unit` is stated for `{K L : Type}`, so the Kummer-level section must
  use `Type`, not `Type u`.

### (e) What is left for reciprocity

The tame symbol is now pinned down up to `⟨π, u⟩`, so the remaining step is the *evaluation*:
`localInvariant_apply_cyclicBrauerHom` at an auxiliary prime `q ≡ 1 mod n` (§0.56(d)) and then
`totalInvariant k = 1`.

---

## 0.64 Status (2026-09-01) — the tame form, and the kernel of the tame symbol

Two modules, `CFT/Brauer/TameSymbol.lean` (commit `ac1d395`) and
`CFT/Brauer/TameEvaluation.lean`.  Both sorry- and axiom-free.

### (a) The tame form

Fix a uniformiser `π`, i.e. a unit with `unitValDiv hm π = 1` (`exists_unitValDiv_eq_one`, which is
just surjectivity of `unitValDiv`).  Then `a · π^{-v(a)}` is a unit of the valuation ring
(`valued_mul_zpow_uniformiser`), so every element is `π^i u` with `u` a unit.  Expanding
`⟨π^i u, π^j w⟩` by bilinearity gives four terms; `⟨u, w⟩ = 1` is §0.63, the skew relation moves
`π` out of the second argument, and `⟨π, π⟩ = ⟨π, -1⟩` because `⟨π, -π⟩ = 1` and `⟨π, -1⟩² = 1`.
What is left is

```lean
localSymbol_zpow_mul_zpow_mul … : ⟨π ^ i * u, π ^ j * w⟩ = ⟨π, (-1) ^ (i * j) * w ^ i * u ^ (-j)⟩
localSymbol_eq_uniformiser … :
    ⟨a, b⟩ = ⟨π, (-1) ^ (v a * v b) * b ^ (v a) * a ^ (-(v b))⟩
valued_tame_argument_eq_one … : v ((-1) ^ (v a * v b) * b ^ (v a) * a ^ (-(v b))) = 1
```

so **the symbol of two elements is the symbol of the uniformiser against an explicit unit of the
valuation ring.**  And that remaining pairing only sees the *residue* of its second argument, since
a unit congruent to one is a power of any exponent prime to `p`
(`localSymbol_eq_one_of_valued_sub_one_lt`, `localSymbol_congr_of_valued_div_sub_one_lt`).

### (b) The evaluation is a counting argument, not a ramified computation

The plan of §0.63(e) was to route `⟨π, u⟩` through `localInvariant_apply_cyclicBrauerHom`.  That is
not needed for the *kernel*, and the kernel is what the global argument consumes.  Write
`E := k⟮u^{1/n}⟯` for the level of `u`.  Three facts already in the tree combine:

* `mem_normSubgroup_of_radical_unit` (§0.63(b)) — `E/K` is unramified, so **every** unit of the
  valuation ring of `K` is a norm from `E`;
* `index_normSubgroup_eq_finrank_local` — `[Kˣ : N(Eˣ)] = [E : K]`;
* the elementary observation that a subgroup of `Kˣ` containing every unit of the valuation ring
  *and* a uniformiser is all of `Kˣ`, because `a = π^{v(a)} · (a π^{-v(a)})`.

So `π ∈ N(Eˣ)` forces `N(Eˣ) = Kˣ`, hence `[E:K] = 1`, hence `u` is a power — the last step being
`exists_pow_eq_of_card_gal_kummerLevel_eq_one`, which reads off `algebraMap c = u^{1/n}` from
`exists_algebraMap_eq_pow_card` at degree one.  Nothing ramified is ever computed.

```lean
eq_top_of_units_le_of_uniformiser_mem (hm) (hU : ∀ x, v x = 1 → x ∈ N)
    (hπ : unitValDiv hm π = 1) (hmem : π ∈ N) : N = ⊤
not_mem_normSubgroup_kummerLevel … (hnp : ¬ ∃ c, c ^ n = b) : π ∉ normSubgroup K ↥(kummerLevel h b)
localSymbol_uniformiser_eq_one_iff … : ⟨π, b⟩ = 1 ↔ ∃ c : Kˣ, c ^ n = b
localSymbol_eq_one_iff_isPow … :
    ⟨a, b⟩ = 1 ↔ ∃ c : Kˣ, c ^ n = (-1) ^ (v a * v b) * b ^ (v a) * a ^ (-(v b))
localSymbol_unit_uniformiser_eq_one_iff … (ha : v a = 1) : ⟨a, π⟩ = 1 ↔ ∃ c : Kˣ, c ^ n = a
orderOf_localSymbol_uniformiser … (hnp : ¬ ∃ c, c ^ n = b) : orderOf ⟨π, b⟩ = n
```

The middle one is **the kernel of the tame norm residue symbol**, complete: the symbol of any two
elements is trivial exactly when one explicit unit of the valuation ring is an `n`-th power.

The bridge that makes the "only if" direction usable is
`localKummerSymbol_eq_one_iff_kummerSymbolUnits`, the *biconditional* form of the descent used in
§0.63(c) — `localKummerSymbol_eq_one_iff` composed with `kummerSymbolUnits_eq_one_iff`, the second
needing only that an algebraic closure is closed under `n`-th roots.

### (c) Lean notes

* `ofMul_mul` and `ofMul_zpow` live in the **root** namespace, not `Additive` — they are declared
  after `end Additive` in `Mathlib/Algebra/Group/TypeTags/Basic.lean`.  `Additive.ofMul_mul` is an
  unknown constant.
* `ring` does not work in a `CommGroup`; the AC-rearrangements of the tame form are
  `mul_mul_mul_comm` together with `← zpow_add` and a `show … = 0 by ring` on the `ℤ` exponent.
* `Valuation.map_eq_of_sub_lt v (h : v (y - x) < v x) : v y = v x` is the clean route from
  `v (u - 1) < 1` to `v u = 1`.
* In `localSymbol_zpow_mul_zpow_mul` a bare `rw [map_mul, …]` matches the *outer* application
  first; pin each rewrite with explicit arguments (`map_mul (localSymbol hres hm hζ) (π ^ i) u`).
* `isKummerData_zmod` has `Ω` implicit, so in a `refine` where it is the *first* explicit argument
  the `IsAlgClosed Ω` instance of `exists_units_pow_eq` is stuck; pass `(Ω := AlgebraicClosure K)`.

### (d) What is left for reciprocity

The local side is now complete for a tame prime: the symbol is computed by its kernel, and
`orderOf_localSymbol_uniformiser` says it is onto the `n`-torsion.  What remains is the global
assembly of §0.56(d): the auxiliary prime `q ≡ 1 mod n`, the cyclic `L ⊆ ℚ(ζ_q)` of degree
`N ∣ q − 1`, and `totalInvariant k = 1`.

---

## 0.65 Status (2026-09-01) — the *value* of the tame symbol

`CFT/Brauer/TameValue.lean`, plus two lemmas added to `CFT/Brauer/CyclicGenerator.lean`.  Both
sorry- and axiom-free; build 9491 jobs green, zero warnings.

§0.64(b) computed the *kernel* of `⟨π, b⟩` by a counting argument that never touches a ramified
computation.  The caveat of §0.56(d) — *"knowing the kernels of the local symbols does not pin the
symbols themselves"* — is what this module removes: the symbol itself, not just its triviality.

### (a) The level of a unit is unramified, as an equation on absolute values

The counting argument of §0.64(b) used `mem_normSubgroup_of_radical_unit`, which needs
unramifiedness only through the *norm* map.  The invariant map needs it through
`localInvariantHom_apply_of_unramified`, whose hypothesis is the sharper

```lean
hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖
```

— every absolute value of `L` is already an absolute value of `K`.  That is exactly what the
Gauss-norm brick `exists_norm_eq_spectralNorm` produces from an irreducible residual minimal
polynomial, so the proof of `exists_valued_of_radical_unit` (`CFT/Local/RadicalUnramified.lean`)
transports verbatim:

```lean
exists_divisionNorm_eq_of_radical_unit (pb : PowerBasis K L) (hl : ℓ.Prime) (hpl : ¬ p ∣ ℓ)
    (hc : Valued.v c = 1) (hmin : minpoly K pb.gen = X ^ ℓ - C c) (hres) (z) (hz : z ≠ 0) :
    ∃ d : K, d ≠ 0 ∧ divisionNorm K L z = ‖d‖
exists_divisionNorm_eq_kummerLevel (hn : n.Prime) (hpn : ¬ p ∣ n) (hres)
    (hb : Valued.v (b : K) = 1) (hdn : Nat.card Gal(↥(kummerLevel h b)/K) = n) : …
```

the second feeding the first with the minimal polynomial `X ^ n - C b` of the chosen root
(`minpoly_kummerLevelGen`), which is available exactly when the level has full degree — and that is
`card_gal_kummerLevel_eq_of_not_isPow`, the degree dividing `n` (`card_gal_kummerLevel_dvd`) and a
level of degree one belonging to a power.

### (b) The symbol as an invariant, and the generator mismatch

Composing `localKummerSymbol_apply`, `smoothLocalInvariantEquiv_apply`,
`smoothBrauerHom_kummerSymbolUnits` (§0.59) and `localInvariantHom_apply_of_unramified` gives

```lean
localKummerSymbol_eq_inv_localInvariant … :
    localKummerSymbol hres hm h (mulZMod n) a b
      = (localInvariant K ↥(kummerLevel h b) hur hm ⟨cyclicBrauerHom hσ₀ a, _⟩)⁻¹
```

The inverse is the one already visible in `smoothBrauerHom_kummerSymbolUnits`.  The subtlety is
that `cyclicBrauerHom hσ₀` is taken with respect to the generator `σ₀` supplied by
`exists_generator_kummerLevel_index` — the one whose discrete logarithm *is* the Kummer character —
whereas `localInvariant` is normalised by the **Frobenius** automorphism.  Rescaling is a power:

```lean
localInvariant_eq_brauerInvariant_pow (hs : divisionFrobenius K L hur = σ₀ ^ s) :
    localInvariant K L hur hm y = brauerInvariant hσ₀ … hm y ^ s
localInvariant_cyclicBrauerHom_pow (hs) (a : Kˣ) :
    localInvariant K L hur hm ⟨cyclicBrauerHom hσ₀ a, _⟩ = baseInvariant hm (finrank K L) a ^ s
```

both immediate from `brauerInvariant_congr_apply` and `brauerInvariant_pow_generator`.

### (c) `t = 1`, so the exponent is the Kummer character itself

For a uniformiser `π` the base invariant is `1 / [E : K]`, so

```lean
localKummerSymbol_uniformiser_eq (hπ : unitValDiv hm (Additive.ofMul π) = 1)
    (hs : divisionFrobenius K ↥(kummerLevel h b) hur = σ₀ ^ s) :
    localKummerSymbol hres hm h (mulZMod n) π b
      = Multiplicative.ofAdd (intQModZ (finrank K ↥(kummerLevel h b)) (-(s : ℤ)))
```

and what is left is to identify `s`.  This is where no residue-field computation is needed:
`exists_generator_kummerLevel_index` returns a generator `σ₀`, an index `t` with
`Nat.card Gal(E/K) * t = n`, and `(kummerChar h b g).val = t * (dlog σ₀ (restrict g)).val` for
every `g`.  When `b` is not a power and `n` is prime the level has full degree `n` by (a), so
`t = 1` and the discrete logarithm of the Frobenius automorphism *is* the Kummer character.
`IsDivisionFrobenius` is a bare `Prop` — it takes no unramifiedness argument — so the hypothesis
can be stated on the restriction of an arbitrary `g` and turned into `hs` by
`eq_divisionFrobenius`:

```lean
localKummerSymbol_uniformiser_eq_kummerChar … (hb : Valued.v (b : K) = 1)
    (hnp : ¬ ∃ c : Kˣ, c ^ n = b)
    (hg : IsDivisionFrobenius (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g)) :
    localKummerSymbol hres hm h (mulZMod n) π b
      = Multiplicative.ofAdd (zmodQModZ n (-kummerChar h b g))
localSymbol_uniformiser_eq_kummerChar … :
    localSymbol hres hm hζ π b = Multiplicative.ofAdd (zmodQModZ n (-kummerChar h b g))
```

`zmodQModZ n` is injective, so this pins the symbol exactly, and
`exists_isDivisionFrobenius_restrictNormalHom` says such a `g` exists (`levelPreimage`).  Together
with §0.64(a) — the tame form moves every occurrence of the uniformiser into the first argument —
**the tame norm residue symbol is now computed, not merely characterised by its kernel.**

### (d) Lean notes

* `localInvariantHom_apply_of_unramified hm hur _` with the relative class left implicit sends the
  elaborator into a `whnf` timeout: it has to solve `↑?x =?= cyclicBrauerHom hσ₀ a` for a subtype
  metavariable.  Supplying `⟨cyclicBrauerHom hσ₀ a, cyclicBrauerHom_mem_relative hσ₀ a⟩` explicitly
  makes it instant.
* `IsSmoothAction` is a `Prop`-valued class, so the section-level
  `attribute [local instance] zmodTrivialAction isSmoothAction_zmod` and the `letI`/`haveI` pair
  inside the body of `localSymbol` are definitionally interchangeable; the `Root` section can state
  its theorem about `localSymbol` and prove it by `exact` on the `localKummerSymbol` form.
* The arithmetic `((ofAdd (intQModZ d 1)) ^ s)⁻¹ = ofAdd (intQModZ d (-s))` is cleanest through the
  additive hom: `← ofAdd_nsmul, ← ofAdd_neg, ← map_nsmul, ← map_neg` and then `nsmul_eq_mul` on `ℤ`.

### (e) What is left for reciprocity

Unchanged in shape, but the local input is now complete: the auxiliary prime `q ≡ 1 mod n`, the
cyclic `L ⊆ ℚ(ζ_q)` of degree `N ∣ q − 1`, and `totalInvariant k = 1`.  The next local brick, if
the global assembly wants it in classical form, is the residue identification
`ζ^s ≡ b^((q−1)/n)` — *the tame symbol is the power residue symbol* — which is `kummerChar` at a
Frobenius read in the residue field.

---

## 0.66 Status (2026-09-01) — the tame symbol *is* the power residue symbol

`CFT/Brauer/TameResidue.lean`, sorry- and axiom-free.  This is the brick that §0.65(e) asked for:
the last local statement in the reciprocity chain, and the first one whose statement mentions
neither a Frobenius, nor a Kummer character, nor the Kummer level.

### (a) The statement

```lean
localSymbol_uniformiser_eq_powerResidue (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) (hpn : ¬ p ∣ n) {π : Kˣ}
    (hπ : unitValDiv hm (Additive.ofMul π) = 1) {b : Kˣ} (hb : Valued.v (b : K) = 1)
    (hnp : ¬ ∃ c : Kˣ, c ^ n = b) {j : ℕ}
    (hj : Valued.v (ζ ^ j - (b : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) < 1) :
    localSymbol hres hm hζ π b = Multiplicative.ofAdd (zmodQModZ n (-(j : ZMod n)))
```

Read `Q := Nat.card (DivisionResidue K K)` as the order of the residue field.  The hypothesis `hj`
says exactly that `ζ^j ≡ b^((Q−1)/n)` in the residue field: this is Euler's criterion, and `j` is
the exponent of the classical `n`-th power residue symbol `(b/𝔭)_n = ζ^j`.  So the theorem reads

> `⟨π, b⟩ = ζ^{−j}` where `ζ^j = (b/𝔭)_n`,

which is the textbook formula for the tame norm residue symbol, with the sign convention already
fixed by §0.65(c).  Note the residue congruence is stated by a *valuation* inequality rather than
in the residue field itself: `Valued.v (x − y) < 1` is the same thing as `x ≡ y` mod the maximal
ideal, and it keeps the statement inside `K` where the rest of the file lives.

### (b) The proof

`localSymbol_uniformiser_eq_kummerChar` (§0.65(c)) already gives
`⟨π, b⟩ = ofAdd (zmodQModZ n (−kummerChar h b g))` for **any** `g` whose restriction to the level
`E = K(b^{1/n})` is a Frobenius.  So the whole content is to identify `kummerChar h b g` with `j`.
That is a three-step computation on the Kummer generator `x := b^{1/n} ∈ E`:

1. `x` is a unit of the division integers: `divisionNorm x ^ n = divisionNorm (x^n) =
   divisionNorm (algebraMap b) = ‖b‖ = 1`, and a positive real with a nontrivial power equal to `1`
   is `1` (`divisionNorm_eq_one_of_pow_eq_one`, factored out of the trichotomy block inside
   `dvd_card_divisionResidue_sub_one_of_isPrimitiveRoot`).
2. `g` acts on `x` by `ζ^{χ(g)}`, where `χ = kummerChar h b`: this is
   `restrictNormalHom_kummerLevelGen`, the level-level form of
   `smul_root_eq_kummerRootUnit_pow`.  Since `g|E` is a Frobenius, `g x ≡ x^Q`, and dividing by the
   unit `x` gives `ζ^{χ(g)} ≡ x^{Q−1}` — this is `divisionNorm_sub_pow_card_sub_one_lt_one`,
   stated for an arbitrary eigenvector `σ x = c · x`.
3. `n ∣ Q − 1` because `ζ` is a primitive `n`-th root of unity in `K` and `n` is invertible
   (`dvd_card_divisionResidue_sub_one_of_isPrimitiveRoot`, fed by `norm_natCast_of_not_dvd`), so
   `x^{Q−1} = (x^n)^{(Q−1)/n} = b^{(Q−1)/n}` lands back in `K`.  Combining,
   `ζ^{χ(g)} ≡ b^{(Q−1)/n} ≡ ζ^j`, and two `n`-th roots of unity congruent mod the maximal ideal
   are equal (`eq_of_valued_sub_lt_one`), so `χ(g) ≡ j mod n`.

Steps 1–3 are `valued_pow_kummerChar_sub_pow_lt_one` and
`kummerChar_eq_of_valued_pow_sub_pow_lt_one`; the theorem of (a) is their composition with §0.65(c)
and `exists_isDivisionFrobenius_restrictNormalHom`.

### (c) Lean notes

* `TameValue.lean` does **not** transitively import `Brauer/FrobeniusBaseChange.lean`,
  `Local/PrimeResidue.lean` or `Local/RootOfUnityValued.lean`; a file built on top of it needs all
  three explicitly (for `isDivisionFrobenius_iff`, `valued_residueChar_lt_one`,
  `eq_of_valued_sub_lt_one` respectively).
* Proving an equality in `↥E` from an equality of `Ω`-coercions: `SetLike.coe_eq_coe.mp` is much
  more robust than `Subtype.ext` or `(algebraMap ↥E Ω).injective`.  The latter forces
  `IntermediateField.algebraMap_apply` to fire twice with different instantiations, where it
  collides with `IntermediateField.coe_algebraMap_apply` on the inner map.
* `Valued.v.map_sub _ _ : v (x − y) ≤ max (v x) (v y)` takes the valuation as its *first explicit*
  argument, so it is `Valued.v.map_sub _ _`, not `Valuation.map_sub _ _ _`.
* To turn `ζ^a = ζ^b` into `a ≡ b mod n`: `IsOfFinOrder.pow_eq_pow_iff_modEq` (the bare
  `pow_eq_pow_iff_modEq` is in a group section and does not apply to a field), with
  `IsOfFinOrder ζ` from `isOfFinOrder_iff_pow_eq_one.2 ⟨n, _, hζ.pow_eq_one⟩`.  It produces
  `[MOD orderOf ζ]`; rewrite `← hζ.eq_orderOf` in the *hypothesis*, never in the goal, since `n`
  also occurs in the `ZMod n` of the conclusion.
* The two roots-of-unity comparison went through `eq_of_valued_sub_lt_one`
  (`Local/RootOfUnityValued.lean`) rather than the `divisionNorm` analogue
  `eq_one_of_pow_eq_one_of_divisionNorm_sub_lt_one` at `D = K`, which avoids ever mentioning
  `divisionNorm K K`.

### (d) What is left for reciprocity

The local side of the reciprocity computation is now **complete**: every ingredient of
`inv_v(⟨a, b⟩)` at a tame place is a power residue symbol with an explicit exponent.  What remains
is purely global, the assembly of §0.56(d):

1. base change of a cyclic algebra `(L/k, σ₀, a)` to a completion `k_v` is the cyclic algebra
   `(L_w/k_v, σ_v, a)` of the decomposition group, with the *same* `a`.  The intermediate-field
   case is `baseChangeHom_cyclicBrauerHom` (`Brauer/CyclicBaseChange.lean`); the completion case
   has to be routed through `decompositionFieldHom` / `localDecompositionEquiv`
   (`Units/DecompositionGalois.lean`) and `baseChangeHom_mk_csa_adicCompletion`
   (`Brauer/PlaceCrossedProduct.lean`).
2. `placeInvariant k v (cyclicBrauerHom hσ₀ a) = c_v · v(a) / n` at an unramified `v`, where
   `Frob_v = σ₀^{c_v}`, from `localInvariant_cyclicBrauerHom_pow`.
3. the tame place, from `localSymbol_uniformiser_eq_powerResidue` above.
4. `totalInvariant k (cyclicBrauerHom hσ₀ a) = 1` for the auxiliary prime `q ≡ 1 mod n` and the
   cyclic `L ⊆ ℚ(ζ_q)` of degree `N ∣ q − 1`.

Two arithmetic identities behind step 1 were checked by hand and should be recorded, because they
are the reason the base change is coefficient-preserving.  With `n = m·d`, `L/k` cyclic of degree
`n` with generator `σ₀`, and the decomposition subgroup at `v` generated by `σ₀^m` (so `d` is the
local degree):

* **carry cocycle.** `⌊(m·i + m·j)/n⌋ = ⌊(i + j)/d⌋` for `0 ≤ i, j < d`.  Hence the cyclic-algebra
  cocycle of `(L/k, σ₀, a)` restricted to `⟨σ₀^m⟩` is *literally* the cyclic-algebra cocycle of
  `(L_w/k_v, σ₀^m, a)`; the degree ratio disappears into the choice of generator.
* **invariant normalisation.** `localInvariant = baseInvariant(a)^s` with
  `divisionFrobenius = σ_v^s`; under `σ_v ↔ σ₀^m` and `d = n/m` this is
  `s·v(a)/d = (m·s)·v(a)/n = c_v·v(a)/n`, which is the classical `inv_v((χ, a)) = χ(Frob_v)·v(a)`.

Two shortcuts were **refuted** and should not be retried: reciprocity does not follow from
`globalReciprocityEquiv` (`Units/GlobalTate.lean`), whose fundamental class is an `Exists.choose`
and therefore not pinned to invariant `1/n`; and it does not follow from comparing indices, since
the image of `H²(G, I_K)` in `H²(G, C_K)` is generated by `1/lcm_v(n_v)`, not `1/n` (§0.55).
Nor does the elementary generator-by-generator argument of `CFT/Global/Reciprocity.lean` — which
proves quadratic Hilbert reciprocity over `ℚ` from Mathlib's quadratic reciprocity — generalise to
`n`-th powers, since the analogue of the input is Eisenstein reciprocity.
---

## 0.67 Status (2026-09-01) — localising a cyclic algebra, and the unramified places

`CFT/Brauer/PlaceCyclic.lean` and `CFT/Brauer/PlaceUnramified.lean`, sorry- and axiom-free.
Together they discharge steps 1 and 2 of the assembly listed in §0.66(d): the global-to-local
comparison of a cyclic algebra, and the vanishing of its invariant at the places that ought to
contribute nothing.

### (a) The base change is coefficient-preserving

```lean
baseChangeHom_cyclicBrauerHom_adicCompletion (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀)
    (hσ : ∀ x : Gal(K_w/k_v), x ∈ Subgroup.zpowers σ)
    (hres : (localDecompositionEquiv k w σ).restrictScalars k
      = σ₀ ^ (stabilizer Gal(K/k) w).index) (a : kˣ) :
    BrauerGroup.baseChangeHom k_v (cyclicBrauerHom hσ₀ a)
      = cyclicBrauerHom hσ (Units.map (algebraMap k k_v).toMonoidHom a)
```

The coefficient on the right is the image of the *same* `a`; nothing about the local degree enters
the coefficient.  The proof factors the base change `k → k_v` through the decomposition field `F`:
over `F` the extension `K/F` is cyclic with a generator inducing `σ₀^{[G : D_w]}`, and
`baseChangeHom_cyclicBrauerHom` applies with the carry identity of §0.66(d); from `F` to `k_v` the
fields `K` and `k_v` are linearly disjoint with compositum `K_w`, which is
`baseChangeHom_cyclicBrauerHom_compositum`.  The generator that makes `hres` true always exists —
`exists_forall_mem_zpowers_restrictScalars_eq` — because the subgroups of a finite cyclic group are
generated by the powers by the divisors of the order, and the decomposition group is the Galois
group of the completions.

Feeding this into `localInvariantHom_apply_of_unramified` gives the local formula in the shape the
reciprocity computation wants:

```lean
placeInvariant_cyclicBrauerHom … (hs : divisionFrobenius k_v K_w hur = σ ^ s) (a : kˣ) :
    placeInvariant k v (cyclicBrauerHom hσ₀ a) = baseInvariant hm (finrank k_v K_w) a_v ^ s
```

that is `inv_v (K/k, σ₀, a) = s · v(a) / n_v`, and with the normalisation identity of §0.66(d)
this is the classical `inv_v = χ(Frob_v) · v(a)`.

### (b) The unramifiedness the computation asks for

Both of the above carry a hypothesis `hur`, the shape in which the splitting theory of division
algebras states unramifiedness:

```
∀ z : K_w, z ≠ 0 → ∃ c : k_v, c ≠ 0 ∧ divisionNorm k_v K_w z = ‖c‖
```

`PlaceUnramified.lean` proves it from `ramIdx (𝓞 k) w = 1`, and nothing else:

```lean
exists_divisionNorm_eq_norm_adicCompletion (hram : ramIdx (𝓞 k) w = 1) (z : K_w) (hz : z ≠ 0) :
    ∃ c : k_v, c ≠ 0 ∧ divisionNorm k_v K_w z = ‖c‖
```

The route is Galois, not numerical.  `Algebra.norm_eq_prod_automorphisms` writes the norm of `z` as
the product of its conjugates; every `τ : K_w ≃ₐ[k_v] K_w` restricts to an element of the
decomposition group and therefore acts by an isometry (`valued_algEquiv_adicCompletion`, from
`adicCompletionAut_restrictToBase` and `valued_adicCompletionAut`); and the two valuations are
compared by `valued_adicCompletionComap`, whose exponent is the ramification index.  So

```lean
valued_algebraNorm_adicCompletion (hram : ramIdx (𝓞 k) w = 1) (z : K_w) :
    Valued.v (Algebra.norm k_v z) = Valued.v z ^ finrank k_v K_w
```

and `Valued.v` is surjective on `k_v`, so `Valued.v z` is already the value of a scalar `c`; the
degree-th root in the definition of `divisionNorm` then cancels the degree-th power.

This matters because it needs **neither the residue degree nor `e · f = n`**, neither of which
Mathlib has for adic completions — only ten Mathlib files mention `adicCompletion` at all.  The
converse is also true (`hur` is equivalent to `n ∣ ord_v N_{K_w/k_v}(z)` for all `z`, which is
`e = 1`), so nothing weaker than `hram` would have done.

The two combine into the statement the global sum needs:

```lean
placeInvariant_cyclicBrauerHom_eq_one_of_ramIdx_eq_one … (hram : ramIdx (𝓞 k) w = 1) {a : kˣ}
    (ha : Valued.v (algebraMap k k_v (a : k)) = 1) :
    placeInvariant k (primeUnder (𝓞 k) w) (cyclicBrauerHom hσ₀ a) = 1
```

— at a finite place unramified in `K/k` at which `a` is a unit, the cyclic algebra contributes
nothing.  The Frobenius is a power of any generator because the Galois group of the completions is
finite (`exists_divisionFrobenius_eq_pow_adicCompletion`), so the exponent `s` never has to be
named.

Two small lemmas were added along the way.  `norm_eq_of_valued_eq` in `Brauer/AdicUnramified.lean`
is the converse of the existing `valued_eq_of_norm_eq`: for a rank one valuation the comparison map
is monotone in both directions, so value and absolute value determine each other.  And
`forall_mem_zpowers_mulEquiv` transports a generator along a group isomorphism, which is used three
times to move a generator between `Gal(K_w/k_v)`, `Gal(K/F)` and `D_w`.

A dead end worth recording: `valued_algEquiv_of_norm` (`Local/NormValued.lean`) looks like the
isometry statement but asks for `Valued.v y = Valued.v (Algebra.norm K y)` for every `y`, which for
the completion tower would force `e = n`.  It is useless here; the decomposition-group route is the
right one.

### (c) What is left

Of the four-step assembly of §0.66(d), steps 1 and 2 are now done.  Step 2 leaves one gap that is
bookkeeping rather than mathematics: `hram` is a hypothesis, and a criterion producing it from
global unramifiedness of `w` over `k` still has to be written.  Step 3 (the tame place) has its
local statement from §0.66 but needs the identification of `L_w / ℚ_q` as the Kummer extension
`ℚ_q((−q)^{1/N})`, and the bridge `IsDivisionFrobenius → IsValuedFrobenius Q` so that
`IsValuedFrobenius.apply_rootOfUnity` gives `τ ζ_q = ζ_q^{N(v)}` without ever constructing a global
Frobenius element.  Step 4 is then the count over the auxiliary prime.

---

## 0.68 Status (2026-09-01) — the Frobenius as an element of the Galois group

`CFT/Brauer/PlaceFrobenius.lean`, `CFT/Brauer/ResidueCard.lean` and
`CFT/Local/RatResidueDegree.lean`, sorry- and axiom-free.  Together they turn the Frobenius
automorphism of a completion — which the splitting theory of division algebras defines by its effect
on the residues of a maximal order — into a *named element of the global Galois group*.  That is the
bridge step 2 of the assembly of §0.66(d) needs before it can speak of the exponent `c_v` in
`Frob_v = σ₀^{c_v}`, and it is also the half of step 3 that §0.67(c) asked for.

### (a) The two measures of an element of the completion

At a place `w` of `K` with `ramIdx (𝓞 k) w = 1` the two absolute values on `K_w` — the `divisionNorm`
of the division-algebra theory, which is the `n`-th root of `‖N_{K_w/k_v}(·)‖`, and the valuation
`K_w` carries as a completion — answer the same two questions:

```lean
divisionNorm_le_one_iff_adicCompletion (hram : ramIdx (𝓞 k) w = 1) (z : K_w) :
    divisionNorm k_v K_w z ≤ 1 ↔ Valued.v z ≤ 1
divisionNorm_lt_one_iff_adicCompletion (hram : ramIdx (𝓞 k) w = 1) (z : K_w) :
    divisionNorm k_v K_w z < 1 ↔ Valued.v z < 1
```

Both come from `valued_algebraNorm_adicCompletion` (§0.67), which says `v(N(z)) = v(z)^n` when
`e = 1`: a `n`-th power is `≤ 1` (resp. `< 1`) exactly when its base is, and `x ↦ x^{1/n}` is an
order isomorphism of the nonnegative reals.  Consequently

```lean
isValuedFrobenius_of_isDivisionFrobenius (hram) (hσ : IsDivisionFrobenius σ) :
    IsValuedFrobenius (Nat.card (DivisionResidue k_v k_v)) σ
```

— being an integer and being congruent to zero mean the same thing for the two measures, and those
are the only two notions `IsValuedFrobenius` mentions.

### (b) The cyclotomic description

`IsValuedFrobenius.apply_rootOfUnity` (`Local/RootOfUnityValued.lean`) then gives, with no choice
left and no *global* Frobenius element ever constructed,

```lean
divisionFrobenius_rootOfUnity_adicCompletion (hram) (hm : m ≠ 0)
    (hmv : Valued.v ((m : ℕ) : K_w) = 1) (hζ : ζ ^ m = 1) :
    divisionFrobenius k_v K_w _ ζ = ζ ^ Nat.card (DivisionResidue k_v k_v)
```

and, since `AlgEquiv.restrictNormal` commutes with the inclusion `K → K_w`, the same statement for a
root of unity of the number field itself (`restrictToBase_divisionFrobenius_rootOfUnity`).  The
hypothesis `hmv` is the invertibility of `m` in the residue field; over `K` it reads
`w.valuation K (m : K) = 1`, converted by `valued_natCast_adicCompletion`.

### (c) The exponent is the rational prime

Write `Q := Nat.card (DivisionResidue k_v k_v)` for the exponent above.  `Brauer/ResidueCard.lean`
identifies it whenever the residue field is no larger than the prime field, by an argument that
never mentions `CharP` or `ZMod`:

1. every residue is the residue of a rational integer, as soon as every integer of the field is
   congruent to one (`surjective_intCast_divisionResidue`);
2. the residue characteristic is congruent to zero, so reducing a rational integer modulo `p` leaves
   a surjection `Fin p → DivisionResidue K K`, giving `Q ≤ p`;
3. the residue of `1` has additive order exactly `p`, giving `p ∣ Q`.

Hence `natCard_divisionResidue_eq_prime : Q = p`, and via
`exists_intCast_sub_lt_one_of_inertiaDeg_eq_one` and `exists_hasResidueChar_of_liesOver`
(`Local/PrimeResidueField.lean`) its adic form

```lean
natCard_divisionResidue_adicCompletion_eq_prime (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (hdeg : (Ideal.span {(p : ℤ)}).inertiaDeg v.asIdeal = 1) :
    Nat.card (DivisionResidue (v.adicCompletion K) (v.adicCompletion K)) = p
```

`Local/RatResidueDegree.lean` supplies the hypothesis over the rationals for free.  A finite place
lies over the rational prime it contains (`liesOver_span_of_natCast_mem`: the span of that prime is
maximal and is contained in the proper ideal below the place), a finite place of `ℚ` contains the
prime `Rat.HeightOneSpectrum.natGenerator` attaches to it (`natCast_natGenerator_mem`), and over `ℚ`
the residue degree is squeezed between `1` and `finrank ℚ ℚ` by `Ideal.inertiaDeg_pos` and
`Ideal.inertiaDeg_le_finrank`, so `inertiaDeg_rat_eq_one`.  Therefore
`natCard_divisionResidue_adicCompletion_rat : Q = q`, the rational prime below the place.

### (d) The Frobenius as an element of the Galois group

Two automorphisms which agree on a generator of the extension are equal
(`AlgHom.ext_of_adjoin_eq_top`), so the cyclotomic description *determines* the Frobenius:

```lean
restrictToBase_divisionFrobenius_eq_of_adjoin (hram) (hm : m ≠ 0)
    (hmv : w.valuation K (m : K) = 1) (hζ : ζ ^ m = 1)
    (hgen : Algebra.adjoin k ({ζ} : Set K) = ⊤) {τ : Gal(K/k)} (hτ : τ ζ = ζ ^ Q) :
    restrictToBase k w (divisionFrobenius k_v K_w _) = τ
```

with the specialisation `restrictToBase_divisionFrobenius_eq_of_adjoin_rat` over `ℚ`, where `Q` is
replaced by the rational prime `q` the place contains.  For `K = ℚ(ζ_m)` and `q ∤ m` this is exactly
the classical statement `Frob_q = (ζ ↦ ζ^q)`, and it is what turns the invariant formula of §0.67
into a computation with the index character of `(ℤ/q)^×`.

### (e) Lean notes

* The generic theorems of `ResidueCard.lean` are stated purely with `‖·‖` and carry no `Valued`
  instance, so the mismatch of §0.55 (the `NormedField` instances on `v.adicCompletion k` and
  `w.adicCompletion K` use different normalisations) never arises; the adic specialisation converts
  by `have h : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := Valued.toNormedField.norm_le_one_iff` followed by `rw [h]`
  — rewriting with the Mathlib lemma directly does not fire.
* The additive name for `orderOf_eq_one_iff` is `AddMonoid.addOrderOf_eq_one_iff`, not
  `addOrderOf_eq_one_iff`.
* `RingCon.coe_mk' : (c.mk' : R → c.Quotient) = ((↑) : R → c.Quotient) := rfl`, so
  `(map_intCast c.mk' b).symm` followed by `rw [RingCon.coe_mk']` moves between `(b : c.Quotient)`
  and the residue of `(b : divisionIntegers K K)`.
* A file mentioning `DivisionResidue (v.adicCompletion K) (v.adicCompletion K)` needs *both*
  `Units/CompletionFinite` (for `NontriviallyNormedField`) and `Local/AdicLocalField` (for
  `ProperSpace`, which then supplies `CompleteSpace`, which `divisionIntegers` asks for).
* `Ideal.LiesOver` is built from `⟨(isMaximal_span_prime hq).eq_of_le hne hle⟩` with
  `hle : Ideal.span {(q : ℤ)} ≤ Ideal.under ℤ v.asIdeal` and `hne : Ideal.under ℤ v.asIdeal ≠ ⊤`.
* `natCard_divisionResidue_self` was already taken by a base-change statement in
  `Brauer/FrobeniusBaseChange.lean`; the new names avoid it.

### (f) What is left for reciprocity

Steps 1 and 2 of §0.66(d) are done, and the Frobenius half of step 3 is now done as well.  The next
brick is the translation of the exponent: `placeInvariant_cyclicBrauerHom` states the invariant as
`baseInvariant(a)^s` with `s` defined *locally* by `divisionFrobenius = σ^s`, while the arithmetic of
step 4 wants it in terms of `c_v` defined *globally* by `restrictToBase (divisionFrobenius) = σ₀^{c_v}`.
The two are related by `c_v = (stabilizer Gal(K/k) w).index · s`, since `restrictToBase` is
multiplicative and `hres` identifies `restrictToBase k w σ` with `σ₀^{index}`; the local degree is
`n / index`, so `s·v(a)/d = c_v·v(a)/n`, which is the classical `inv_v((χ, a)) = χ(Frob_v)·v(a)`.
After that: the criterion producing `hram` from global unramifiedness, the Kummer identification
`L_w/ℚ_q = ℚ_q((−q)^{1/N})` for the ramified place, and the count over the auxiliary prime.

---

## 0.69 Status (2026-09-01) — the local invariant from a global datum

`CFT/Brauer/PlaceExponent.lean`, sorry- and axiom-free.  This is the brick §0.68(f) named: the
invariant of a cyclic algebra at a finite place, expressed by the exponent of the *restricted*
Frobenius rather than by the local one.  It is the last purely formal step before the count over
places; from here on every remaining task is arithmetic input, not bookkeeping.

### (a) The value of a unit at a place

```lean
placeValue (v : HeightOneSpectrum (𝓞 k)) (a : kˣ) : ℤ :=
  unitValDiv (isUnitValGen_one (valued_adicCompletion_surjective v))
    (Additive.ofMul (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a))
```

The valuation of `a` in `k_v`, normalised so that a uniformiser has value `1`; the normalisation is
free because `Valued.v : k_v → ℤᵐ⁰` is surjective, so `1` generates the value group
(`isUnitValGen_one`).  `placeValue_eq_zero` records the case that matters for the count: a unit of
the ring of integers of `k_v` has value `0`, proved by `ker_unitValDiv` (dividing by a generator does
not change the kernel) together with `mem_ker_unitVal`.

### (b) Restriction is the decomposition identification

Two maps `(K_w ≃ₐ[k_v] K_w) → Gal(K/k)` are in play: `restrictToBase`, which restricts an
automorphism of the completion along `K → K_w`, and `localDecompositionEquiv`, which identifies the
Galois group of the completions with `Gal(K/Z_w)` for the decomposition field `Z_w`.  They agree:

```lean
restrictToBase_eq_restrictScalars_localDecompositionEquiv (τ) :
    restrictToBase k w τ = (localDecompositionEquiv k w τ).restrictScalars k
```

Both sides are determined by their effect on the image of `K` in `K_w`, so the proof is
`AlgEquiv.ext` composed with `FaithfulSMul.algebraMap_injective K K_w`, then
`toAdicCompletion_restrictToBase` on one side and `algebraMap_localDecompositionEquiv` on the other.
This is the statement that makes the hypothesis `hres` of `placeInvariant_cyclicBrauerHom` — which is
phrased with `localDecompositionEquiv` — usable for `restrictToBase`.

### (c) Index times local degree is the degree

```lean
index_mul_finrank_adicCompletion :
    (stabilizer Gal(K/k) w).index * finrank k_v K_w = Nat.card Gal(K/k)
```

`finrank k_v K_w = Nat.card (K_w ≃ₐ[k_v] K_w)` by `IsGalois.card_aut_eq_finrank` (stated with
`Nat.card`, not `Fintype.card`), then `localDecompositionEquiv` and `decompositionFieldEquiv`
transport that to `Nat.card ↥(stabilizer Gal(K/k) w)`, and `Subgroup.index_mul_card` finishes.  Note
that positivity of both factors then comes for free from `Nat.card_pos` and `Nat.mul_eq_zero`; there
is no need to invoke `Module.finrank_pos` and its instance burden.

### (d) The two exponents

With `e := (stabilizer Gal(K/k) w).index`, `d := finrank k_v K_w`, `n := Nat.card Gal(K/k)`:

```lean
restrictToBase_divisionFrobenius_eq_pow (hres) (hur) (hs : divisionFrobenius k_v K_w hur = σ ^ s) :
    restrictToBase k w (divisionFrobenius k_v K_w hur) = σ₀ ^ (e * s)
```

— `restrictToBase` is multiplicative because it is the underlying function of the monoid
homomorphism `restrictToBaseHom`, so `rw [hs, ← restrictToBaseHom_apply, map_pow]` moves the power
outside, and (b) plus `hres` turn `restrictToBase k w σ` into `σ₀ ^ e`.  Hence if the *global*
exponent `c` is defined by `restrictToBase k w (divisionFrobenius …) = σ₀ ^ c`, then `σ₀ ^ (e·s) =
σ₀ ^ c`, and since `orderOf σ₀ = n` (from `Subgroup.eq_top_iff'`, `Nat.card_zpowers` and
`Subgroup.topEquiv`), `pow_eq_pow_iff_modEq` gives `e·s ≡ c [MOD n]`.

### (e) The invariant

```lean
placeInvariant_cyclicBrauerHom_eq_intQModZ (hσ₀) (hσ) (hres) (hur) (hs) (hc) (a : kˣ) :
    placeInvariant k (primeUnder (𝓞 k) w) (cyclicBrauerHom hσ₀ a)
      = Multiplicative.ofAdd (intQModZ (Nat.card Gal(K/k))
          ((c : ℤ) * placeValue (primeUnder (𝓞 k) w) a))
```

This is the classical `inv_v (K/k, σ₀, a) = c_v · v(a) / n`.  The proof rewrites with
`placeInvariant_cyclicBrauerHom` (§0.67), `baseInvariant_apply`, `unitInvariant_apply` and
`← ofAdd_nsmul` to reach `s • ⟦V/d⟧ = ⟦c·V/n⟧` in `QModZ`, and then discharges that by hand: with
`c = e·s + n·t` and `n = e·d`,

```
s·V/d − c·V/n = s·V/d − (e·s·V)/(e·d) − t·V = −t·V ∈ ℤ.
```

### (f) Lean notes

* `set x := … with h` does **not** capture occurrences created by *later* rewrites, so a proof that
  first abbreviates and then rewrites ends up comparing `x` against its own unfolding.  The fix used
  here is the opposite order: unfold the definition in the goal first (`rw [placeValue_def]`), keep
  the arithmetic in a separate `private` lemma over plain integers, and let unification of that
  lemma's variables do the abbreviating.
* `QModZ` is an `abbrev` for `ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)`, so `QuotientAddGroup.mk`
  elaborates at it directly, but `n • ⟦x⟧ = ⟦n • x⟧` is not `rfl`; a two-line induction with
  `succ_nsmul` proves it (`nsmul_qModZ_mk`).
* `Nat.ModEq.dvd : a ≡ b [MOD n] → (n : ℤ) ∣ (b : ℤ) - (a : ℤ)` produces `↑(e * s)`, so a `push_cast`
  is needed before the hypothesis has the shape `(c : ℤ) - (e : ℤ) * (s : ℤ) = (n : ℤ) * t`.
* `restrictToBaseHom` lives in `Units/CompletionCyclic.lean`, which is *not* transitively imported by
  `Brauer/PlaceFrobenius.lean` nor by `Brauer/PlaceCyclic.lean`; the import is explicit.

### (g) What is left for reciprocity

Steps 1, 2 and the Frobenius half of step 3 of §0.66(d) are done, and the exponent translation is
now done too.  Remaining:

1. the criterion producing `hram : ramIdx (𝓞 k) w = 1` from global unramifiedness of `w` — the
   definition already *is* that statement, so what is needed is the supply of it for the places of a
   subfield of `ℚ(ζ_q)` away from `q`;
2. the ramified place: the Kummer identification `L_w/ℚ_q = ℚ_q((−q)^{1/N})` combined with
   `localSymbol_uniformiser_eq_powerResidue` (§0.66);
3. the count: `totalInvariant k (cyclicBrauerHom hσ₀ a) = 1` for the auxiliary prime `q ≡ 1 mod n`
   and cyclic `L ⊆ ℚ(ζ_q)` of degree `N ∣ q − 1`, together with triviality of the archimedean
   invariants.

---

## 0.70 Status (2026-09-01) — the unramified supply and the archimedean places

`CFT/Units/RatRamIdx.lean` and `CFT/Brauer/TotallyRealInvariant.lean`, sorry- and axiom-free.  They
discharge item 1 of §0.69(g) and the second half of item 3.

### (a) The ramification index over the rationals

The `hram : ramIdx (𝓞 k) w = 1` that every unramified-place statement of §0.67–§0.69 asks for is
stated relative to the *ring of integers of the base field*, whereas both Mathlib's
`Algebra.IsUnramifiedAt` and the cyclotomic computations of
`Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean` are stated relative to `ℤ`.  Over `ℚ` the
two agree, and the bridge is three lines of ideal theory:

* `Ideal.ramificationIdx f p P` is `sSup {n | Ideal.map f p ≤ P ^ n}`, so it depends on the base
  only through the *extended* ideal — `ramificationIdx_congr`.
* `algebraMap ℤ (𝓞 ℚ)` is `Rat.ringOfIntegersEquiv.symm` (any two ring maps out of `ℤ` agree), hence
  surjective, so `Ideal.map (algebraMap ℤ (𝓞 ℚ)) (Ideal.under ℤ P) = Ideal.under (𝓞 ℚ) P`.
* Therefore `ramIdx (𝓞 ℚ) w = Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.under ℤ w.asIdeal)
  w.asIdeal`, which is `1` as soon as `Algebra.IsUnramifiedAt ℤ w.asIdeal`.

Combined with the repo's existing `Cyclotomic/Ramified.lean` this gives, for a place `w` of any
number field embedded in the cyclotomic field of conductor `n`,

```lean
ramIdx_rat_eq_one_of_not_dvd (n) (E) [IsCyclotomicExtension {n} ℚ E] [Algebra F E] (p)
  (w : HeightOneSpectrum (𝓞 F)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] (hn : ¬ p ∣ n) :
  ramIdx (𝓞 ℚ) w = 1
```

together with the version quantified over the primes contained in `w`.  The same file records that
a natural number prime to the residue characteristic is a unit at the place
(`valuation_natCast_eq_one_of_not_dvd`), which is the remaining side condition `hmv` of
`restrictToBase_divisionFrobenius_eq_of_adjoin_rat`.

### (b) The archimedean places drop out for a totally real splitting field

`ℚ` is totally real, so its single infinite place `u` is real and `relative ℚ u.Completion` is
`relative ℚ ℝ` — the hypothesis `algebraMap ℚ ℝ = embedding_of_isReal hu` of
`relative_completion_eq_relative_real` is free, because `Subsingleton (ℚ →+* ℝ)`.  A ring
homomorphism `L →+* ℝ` is automatically a `ℚ`-algebra homomorphism (`RingHom.toRatAlgHom`), so the
monotonicity `relative_le_relative_of_algHom` gives

```lean
infinitePlaceInvariant_rat_eq_one_of_isTotallyReal (u : InfinitePlace ℚ)
  (hx : x ∈ BrauerGroup.relative ℚ L) : infinitePlaceInvariant ℚ u x = 1
```

for `L` a totally real number field — any infinite place of `L` is real and supplies the embedding.
Applied to `cyclicBrauerHom hσ₀ a`, whose class lies in `relative ℚ L` by construction, this leaves

```lean
totalInvariant_cyclicBrauerHom_rat (a : ℚˣ) :
  totalInvariant ℚ (cyclicBrauerHom hσ₀ a)
    = ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), placeInvariant ℚ v (cyclicBrauerHom hσ₀ a)
```

so the reciprocity statement for such an algebra is now purely a statement about the finite places.
This is exactly the shape wanted, because the field `F₀ ⊆ ℚ(ζ_q)` produced by
`exists_cyclic_totallyRamified_totallyReal_of_dvd` is totally real by construction.

### (c) Why the subfield cannot be traded for the whole cyclotomic field

There is a tempting simplification: `cyclicBrauerHom_restrictNormal` (`Brauer/CyclicTower.lean`)
says that for a tower `k ⊆ L ⊆ L'` with compatible generators,

```
(L/k, σ₀|_L, a) = (L'/k, σ', a ^ [L' : L])
```

in the Brauer group, so the invariants of `(F₀/ℚ, σ₀, a)` are the invariants of
`(ℚ(ζ_q)/ℚ, σ', a^{(q−1)/N})`, and the *only* Frobenius one ever has to identify is the cyclotomic
one, `ζ ↦ ζ^p`, for which `restrictToBase_divisionFrobenius_eq_of_adjoin_rat` already applies with
no tower functoriality.  This is worth using at the finite places.

It cannot, however, replace §(b): `ℚ(ζ_q)` is totally *complex* for `q > 2`, so it admits no real
embedding and the archimedean invariant of `(ℚ(ζ_q)/ℚ, σ', b)` need not vanish — the quaternion
algebra `(ℚ(ζ_3)/ℚ, σ, −1)` is a counterexample.  The vanishing is a property of the totally real
subfield, and has to be proven there.

### (d) Lean notes

* `Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ`; `algebraMap ℤ (𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm` by
  `RingHom.ext_int _ _`.
* `RingHom.toRatAlgHom` is stated for *arbitrary* `Algebra ℚ R`, `Algebra ℚ S` instances (its
  `commutes'` goes through `Subsingleton (ℚ →+* R)`), so it does not impose the `algebraRat`
  instance and cannot create a diamond with the algebra structure a caller already has.
* `Ideal.LiesOver.over` is the field `p = P.under R`, so it rewrites *forwards* from the ideal below
  to the span; `rw [← Ideal.LiesOver.over]` is the direction that turns membership in `under ℤ P`
  into membership in `span {(p : ℤ)}`.

### (e) What is left for reciprocity

Of §0.69(g) only the genuinely arithmetic item survives:

1. the ramified place `q`: the Kummer identification `L_w/ℚ_q = ℚ_q((−q)^{1/N})` combined with
   `localSymbol_uniformiser_eq_powerResidue`;
2. the count itself, `∏ᶠ v, placeInvariant ℚ v (cyclicBrauerHom hσ₀ a) = 1`, whose content is that
   the cyclotomic Frobenius exponent at `p` and the power residue symbol of `p` at `q` are negatives
   of each other modulo `1`.

---

## 0.71 Status (2026-09-01) — the invariant away from the conductor, and the count over places

`CFT/Brauer/PlaceCyclotomic.lean` and `CFT/Brauer/RatCount.lean`, sorry- and axiom-free (build green
at 9502 jobs, no warnings).  They discharge the *bookkeeping* half of §0.70(e) item 2: the total
invariant of the algebra reciprocity is about is now literally a product of **two** local invariants.

### (a) The unramified-place formula with nothing left to supply

§0.69 states the unramified-place invariant with four auxiliary inputs: a generator `σ` of the
Galois group of the *completions*, a proof `hres` that it restricts to `σ₀`, the exponent `s` of the
local Frobenius as a power of `σ`, and the exponent `c` of the *global* Frobenius as a power of
`σ₀`.  The first three are produced by the extension itself —
`exists_forall_mem_zpowers_restrictScalars_eq` (`Brauer/PlaceCyclic.lean`) gives `σ, hres`, and
`exists_divisionFrobenius_eq_pow_adicCompletion` (`Brauer/PlaceUnramified.lean`) gives `s` — so they
can be obtained inside the proof rather than asked of a caller.  (The two calls each mention the
norm-surjectivity witness `hur`, and the terms match because it is a proof.)  What is left is

```lean
placeInvariant_cyclicBrauerHom_eq_intQModZ_of_ramIdx_eq_one (k) (w) (hσ₀)
  (hram : ramIdx (𝓞 k) w = 1) (hc : restrictToBase k w (divisionFrobenius …) = σ₀ ^ c) (a : kˣ) :
  placeInvariant k (primeUnder (𝓞 k) w) (cyclicBrauerHom hσ₀ a)
    = Multiplicative.ofAdd (intQModZ (Nat.card Gal(K/k)) ((c : ℤ) * placeValue _ a))
```

and its corollary, the workhorse of the count, where the exponent never has to be named at all:

```lean
placeInvariant_cyclicBrauerHom_eq_one_of_valued_eq_one (k) (w) (hσ₀) (hram) (ha : Valued.v … = 1) :
  placeInvariant k (primeUnder (𝓞 k) w) (cyclicBrauerHom hσ₀ a) = 1
```

Over `ℚ`, feeding `restrictToBase_divisionFrobenius_eq_of_adjoin_rat` (§0.69) into the first gives
`placeInvariant_cyclicBrauerHom_rat_of_adjoin`, whose only remaining input is a *global* datum: an
automorphism `τ` with `τ ζ = ζ ^ q` for the rational prime `q` below the place, together with `τ =
σ₀ ^ c`.  Specializing the two side conditions to a subfield of a cyclotomic field via
`ramIdx_rat_eq_one_of_not_dvd` and `valuation_natCast_eq_one_of_not_dvd` (§0.70(a)) gives
`placeInvariant_cyclicBrauerHom_rat_of_adjoin_not_dvd`, which asks only `¬ q ∣ N` and `¬ q ∣ m`.

### (b) Everything but two places drops out

The vanishing statement is packaged for the rationals without any `LiesOver` instance in sight:

```lean
placeInvariant_cyclicBrauerHom_rat_eq_one_of_notMem (hσ₀) (N) (E) [IsCyclotomicExtension {N} ℚ E]
  [Algebra K E] (v : HeightOneSpectrum (𝓞 ℚ))
  (hN : ∀ ℓ, ℓ.Prime → ℓ ∣ N → ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) (ha : v.valuation ℚ (a : ℚ) = 1) :
  placeInvariant ℚ v (cyclicBrauerHom hσ₀ a) = 1
```

A place of `ℚ` is the place below a place of `K` (`exists_primeUnder_eq`), the unramifiedness comes
from the quantified form `ramIdx_rat_eq_one_of_forall_prime_not_dvd`, and the unit condition is read
off the valuation.  Combining with §0.70(b) — for a totally real `K` the archimedean invariants
vanish, so `totalInvariant` is the finite product over the finite places — and with
`finprod_eq_prod_of_mulSupport_subset`:

```lean
totalInvariant_cyclicBrauerHom_rat_eq_mul (hσ₀) (N) (E) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
  (hN : ∀ ℓ, ℓ.Prime → ℓ ∣ N → ℓ = q) (hap : (a : ℚ) = (p : ℚ)) :
  totalInvariant ℚ (cyclicBrauerHom hσ₀ a)
    = placeInvariant ℚ (ratPlace p hp) (cyclicBrauerHom hσ₀ a)
      * placeInvariant ℚ (ratPlace q hq) (cyclicBrauerHom hσ₀ a)
```

This is exactly the shape reciprocity is proved in: for `K = F₀ ⊆ ℚ(ζ_q)` cyclic totally real of
degree `N ∣ q − 1` and coefficient a rational prime `p ≠ q`, the whole of reciprocity is the
cancellation of two explicitly-named terms.

### (c) Lean notes

* **An algebra diamond at `ℚ`.**  Writing `algebraMap ℚ (v.adicCompletion ℚ) x` *literally at `ℚ`*
  elaborates with `DivisionRing.toRatAlgebra`, whereas a lemma stated generically in `k` and
  instantiated at `k := ℚ` carries `HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v`.  These
  are not syntactically equal, and the mismatch surfaces both as an `Application type mismatch` and,
  inside a `rw`, as a `(deterministic) timeout at whnf`.  The fix is never to write the `ℚ`-level
  `algebraMap` in a statement: state the hypothesis as `v.valuation ℚ x = 1` and bridge it with a
  *generically stated* lemma used as a rewrite on the goal, so the goal supplies the instance.
* `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x` proves
  `Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x` by direct term application —
  the algebra map and the completion coercion are definitionally equal.
* `ramIdx_rat_eq_one_of_forall_prime_not_dvd` needs no `LiesOver` instance, so it avoids having to
  extract the residue characteristic of a place that is not already known to lie over a named prime.
  Prefer it to `ramIdx_rat_eq_one_of_not_dvd` whenever the place is generic.
* Distinctness of two `ratPlace`s is cleanest through `natGenerator_eq_of_natCast_mem`, not through
  injectivity of the underlying equivalence (which would force unfolding the definition).

### (d) What is left for reciprocity

1. the ramified place `q`, unchanged from §0.70(e);
2. the *arithmetic* half of the count: the cyclotomic Frobenius `τ` with `τ ζ = ζ ^ p`, and the
   identity between its exponent and the power residue symbol.  For `τ`, Mathlib supplies
   `IsCyclotomicExtension.Rat.galEquivZMod n K : Gal(K/ℚ) ≃* (ZMod n)ˣ` together with
   `galEquivZMod_apply_of_pow_eq` and `galEquivZMod_restrictNormal_apply`
   (`Mathlib/NumberTheory/NumberField/Cyclotomic/Galois.lean`), so `τ` is the preimage of
   `ZMod.unitOfCoprime p _` and `hgen` comes from `IsPrimitiveRoot.powerBasis` and
   `PowerBasis.adjoin_gen_eq_top`.

## 0.72 Status (2026-09-01) — the cyclotomic Frobenius, and the blueprint for the ramified place

`CFT/Brauer/CyclotomicFrobenius.lean`, sorry- and axiom-free (build green at 9503 jobs, no
warnings).  It closes item 2 of §0.71(d) — the *arithmetic* half of the unramified term — and this
section also records, in full, the computation that item 1 (the ramified place) has to be built out
of.

### (a) The automorphism raising the roots of unity to a given power

`placeInvariant_cyclicBrauerHom_rat_of_adjoin_not_dvd` asks its caller for a global automorphism
`τ` with `τ ζ = ζ ^ q`, a generator `ζ` of the field, and an exponent `c` with `τ = σ₀ ^ c`.  For a
cyclotomic field the first two are supplied outright:

```lean
noncomputable def cyclotomicPowerAut (n) (K) [IsCyclotomicExtension {n} ℚ K] (hp : p.Coprime n) :
    Gal(K/ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod n K).symm (ZMod.unitOfCoprime p hp)

cyclotomicPowerAut_apply (hx : x ^ n = 1) : cyclotomicPowerAut n K hp x = x ^ p
adjoin_zeta_rat_eq_top : Algebra.adjoin ℚ {IsCyclotomicExtension.zeta n ℚ K} = ⊤
```

`galEquivZMod_apply_of_pow_eq` gives `σ x = x ^ (galEquivZMod n K σ).val.val` for *every* `x` with
`x ^ n = 1`, not only for a primitive root, and `ZMod.coe_unitOfCoprime` together with
`ZMod.val_natCast` turns the unit back into `p % n`; the exponent is then repaired by

```lean
pow_mod_eq_pow_of_pow_eq_one {M} [Monoid M] (hx : x ^ n = 1) (p) : x ^ (p % n) = x ^ p
```

which has to be stated at monoid level, because `ζ` is a field element and the existing
`Semiabelian.pow_mod_eq_pow` is a group lemma.  Feeding all three in:

```lean
placeInvariant_cyclicBrauerHom_cyclotomic (hσ₀) (w) [Fact q.Prime]
  [w.asIdeal.LiesOver (Ideal.span {(q : ℤ)})] (hqn : Nat.Coprime q n)
  (hc : cyclotomicPowerAut n K hqn = σ₀ ^ c) (a : ℚˣ) :
  placeInvariant ℚ (primeUnder (𝒪 ℚ) w) (cyclicBrauerHom hσ₀ a)
    = Multiplicative.ofAdd (intQModZ (Nat.card Gal(K/ℚ)) ((c : ℤ) * placeValue _ a))
```

Nothing local survives: the only hypotheses are `Nat.Coprime q n` and the discrete logarithm `hc`
of the cyclotomic Frobenius to the chosen generator.

### (b) Lean notes

* `IsCyclotomicExtension.isGalois` (`Mathlib/NumberTheory/Cyclotomic/Basic.lean:589`) is a
  **theorem** with the set `S` explicit, not an instance, so `IsGalois ℚ K` is *not* synthesised
  from `[IsCyclotomicExtension {n} ℚ K]`.  Making it a `local instance` is unsafe — synthesis would
  have to guess the conductor through a metavariable — so it is carried as an ordinary section
  variable `[IsGalois ℚ K]`, which callers discharge with `haveI := IsCyclotomicExtension.isGalois
  {n} ℚ K`.
* `IsCyclotomicExtension.adjoin_primitive_root_eq_top` (`:460`) gives `hgen` directly; there is no
  need to go through `IsPrimitiveRoot.powerBasis` and `PowerBasis.adjoin_gen_eq_top` as §0.71(d)
  guessed.
* A bare statement mentioning `cyclicBrauerHom` over a cyclotomic `K` times out at `isDefEq` with
  the default 200000 heartbeats; `set_option synthInstance.maxHeartbeats 1000000` and
  `set_option maxHeartbeats 1000000` at the top of the module clear it, as in
  `Brauer/TotalInvariant.lean` and `Brauer/RatCount.lean`.

### (c) The ramified place: the computation to formalise

This is the whole of what is left, written out so that it can be built brick by brick.  Fix an odd
prime `q`, a divisor `N ∣ q − 1`, and write `K = ℚ_q`, `ζ = ζ_q`, `λ = ζ − 1`.

1. **`λ` is a uniformiser of `K(ζ)`** and `∏_{a=1}^{q-1} (ζ^a − 1) = Φ_q(1) = q` (the sign is `+`
   because `q − 1` is even).  Each factor is `λ·u_a` with `u_a = 1 + ζ + ⋯ + ζ^{a-1} ≡ a (mod λ)`, so
   `q = λ^{q-1}·u` with `u ≡ (q−1)! ≡ −1 (mod λ)` by Wilson.  Hence `λ^{q-1} = −q·v` with
   `v ≡ 1 (mod λ)`.
2. **A unit `≡ 1` modulo the maximal ideal is a `(q−1)`-th power**, by Hensel: the residue equation
   `x^{q-1} = 1` has `x = 1` as a simple root because `q − 1` is prime to the residue
   characteristic.  Write `v = w^{q-1}` with `w ≡ 1 (mod λ)` and put `μ := λ / w`.  Then
   `μ^{q-1} = −q`, so **`K(ζ_q) = K((−q)^{1/(q-1)})` is a Kummer extension** — `K` contains the
   `(q−1)`-st roots of unity by Teichmüller.
3. **The Galois action on `μ` is the Teichmüller character.**  `σ_a(μ)/μ` is a `(q−1)`-st root of
   unity because `μ^{q-1} = −q` lies in `K`, and
   `σ_a(μ)/μ = (σ_a(λ)/λ)·(w/σ_a(w)) ≡ a·1 (mod 𝔪)`, since `w ≡ 1` forces `σ_a(w) ≡ 1`.  A root of
   unity of order prime to the residue characteristic is determined by its residue, so
   **`σ_a(μ) = ω(a)·μ`** with `ω` the Teichmüller lift.
4. **Descend to degree `N`.**  Put `ν := μ^{(q-1)/N}`, so `ν^N = −q` and
   `σ_a(ν) = ω(a)^{(q-1)/N}·ν`.  The stabiliser of `ν` is `{a : a^{(q-1)/N} ≡ 1} =` the `N`-th
   powers, which is the subgroup cutting out `F₀`, so `w.adicCompletion F₀ = K(ν)` is the Kummer
   level of `−q`, and for `g` a generator of `(ℤ/q)ˣ` the root of unity
   `ζ_N := ω(g)^{(q-1)/N}` is primitive and **`σ_g` restricts to the canonical Kummer generator
   `ν ↦ ζ_N ν`.**

Step 4 is exactly the `hcarry` hypothesis of `smoothBrauerHom_kummerSymbolUnits`
(`Brauer/SymbolCyclicAlgebra.lean`), which asks that `dlog σ₀` on the level agree with the Kummer
character.  So no generator mismatch survives, and

```
inv_q (cyclicBrauerHom hσ_g p) = inv ⟨p, −q⟩⁻¹ = inv ⟨−q, p⟩
```

by `localSymbol_mul_swap` (`Brauer/LocalSymbolUnits.lean:155`).  The right-hand side has a
uniformiser in the first slot and a unit in the second, which is precisely the shape of
`localSymbol_uniformiser_eq_powerResidue` (`Brauer/TameResidue.lean:238`, and its `hn : n.Prime` is
harmless because `N = ℓ` is prime in the Shafarevich application): it equals
`ofAdd (zmodQModZ N (−j))` where `ζ_N^j ≡ p^{(q-1)/N} (mod 𝔪)`.

The two terms then cancel by pure arithmetic: `ζ_N^j = ω(g)^{j(q-1)/N} ≡ g^{j(q-1)/N}` and
`p ≡ g^c (mod q)` for the exponent `c` of §0.72(a), so `j ≡ c (mod N)` and the invariants are
`ofAdd (c/N)` and `ofAdd (−c/N)`.

### (d) What is left for reciprocity

Only §0.72(c).  Its four steps are independent bricks: (1) is a cyclotomic identity that can be
proved in the number field and transported, (2) is Hensel for `x^{q-1} = v`, (3) is the
determination of a root of unity by its residue — the same lemma `eq_of_valued_sub_lt_one` that
`Brauer/TameResidue.lean` already uses — and (4) is a Galois-correspondence bookkeeping step
identifying `w.adicCompletion F₀` with a subfield of `K(ζ_q)`.

---

## 0.73 Status (2026-09-01) — bricks 1–3 of the ramified place, and the transport lemma

Bricks (1), (2), (3) of §0.72(c) are done.  Two new modules landed:

### (a) `CFT/Local/CyclotomicRadical.lean` — brick 3 (and the assembly of 1 + 2)

For a complete valued field `A` of residue characteristic `q` (odd) containing a primitive `q`-th
root of unity `ζ`:

* `exists_pow_eq_neg_natCast` : `∃ μ, μ^(q-1) = −q ∧ v (μ/(ζ−1) − 1) < 1`.  This is brick (1)
  (`exists_pow_sub_one_eq_neg_natCast_mul` from `Local/CyclotomicUniformiser.lean`) corrected by
  brick (2) (`exists_mem_unitFiltration_zero_pow_eq` from `Local/UnitPowRoot.lean`, which was
  already in the repo).  The extra conclusion — that `μ` is congruent to the uniformiser `ζ − 1` —
  is what makes brick (3) go through, so it is carried along rather than discarded.
* `pow_aut_div_eq_one` : `(σ μ / μ)^(q-1) = 1` for any ring automorphism `σ`, because `μ^(q-1)` is
  a rational integer.
* `valued_aut_div_sub_natCast_lt_one` : if `σ` preserves the valuation and `σ ζ = ζ^a`, then
  `v (σ μ / μ − a) < 1`.  The proof splits `σ μ / μ` as `(1 + ζ + ⋯ + ζ^{a-1}) · (σ w / w)` with
  `w := μ/(ζ−1)`, uses `valued_geomSum_sub_natCast_lt_one` on the first factor and `v (σ w/w − 1) < 1`
  on the second.
* `aut_eq_mul_of_pow_eq_one` : combining the two with `eq_of_valued_sub_lt_one`
  (`Local/RootOfUnityValued.lean:141`), **`σ μ = η · μ` for the unique `(q−1)`-st root of unity `η`
  whose residue is `a`** — i.e. `σ_a(μ) = ω(a)·μ`, the Teichmüller statement of brick (3).

The module is stated for an abstract `Valued A ℤᵐ⁰` with `HasResidueChar A q e`, so it applies
verbatim to `λ.adicCompletion ℚ(ζ_q)` once that is equipped with its `HasResidueChar` instance.

### (b) `CFT/Brauer/CyclicTransport.lean` — moving a cyclic algebra between splitting fields

`cyclicBrauerHom_congr` : given cyclic `L/K` and `L'/K` with chosen generators `σ₀`, `σ₀'` and an
isomorphism `φ : L ≃ₐ[K] L'` with `φ ∘ σ₀ = σ₀' ∘ φ`, the two cyclic algebras have the same Brauer
class.  The proof is `nonempty_algEquiv_cyclicAlgebra` applied to the copy of `L'` inside
`cyclicAlgebra hσ₀ a` obtained by composing the tautological copy of `L` with `φ.symm`; the unit
supplied by `exists_unit_cyclicAlgebra` implements `σ₀'` on that copy precisely because `φ`
intertwines the generators.  The degree-`< 2` case is handled separately, exactly as in
`Brauer/CyclicTower.lean`.

This is needed because the two sides of the ramified computation live in different types:
`baseChangeHom_cyclicBrauerHom_adicCompletion` produces the completion `w.adicCompletion F₀`, while
`smoothBrauerHom_kummerSymbolUnits` wants an `IntermediateField ℚ_q Ω`.

### (c) Two questions settled

* **The composite-`N` worry is moot.**  `localSymbol_uniformiser_eq_powerResidue`
  (`Brauer/TameResidue.lean:238`) carries `hn : n.Prime`, and §0.72(c) already notes that this is
  harmless: in the Shafarevich application `N = ℓ` is prime.  So there is no need to generalise the
  `TameValue.lean` chain to composite `n`, and no need to route the ramified place through the full
  cyclotomic field to dodge the hypothesis.  Work directly at `F₀_w = ℚ_q(ν)` with `ν^N = −q`.
* **How to identify `F₀_w` with a Kummer level, without building an isomorphism by hand.**  Pick
  *any* `ℚ_q`-embedding `ψ : F₀_w →ₐ[ℚ_q] Ω` and set `E := ψ.fieldRange`.  Then `AlgEquiv.ofInjective`
  supplies `F₀_w ≃ₐ[ℚ_q] ↥E` for free, and `E = kummerLevel h (−q)` because `h.root (−q)` and `ψ ν`
  differ by a `N`-th root of unity, which already lies in `ℚ_q`.  This replaces the
  Galois-correspondence bookkeeping of §0.72(c) step 4 by a one-line construction plus a
  degree count.

### (d) Brick 4: the chain that is left

1. `λ.adicCompletion ℚ(ζ_q)` is a complete valued field of residue characteristic `q` containing a
   primitive `ζ_q` — a `HasResidueChar` instance plus the image of `ζ_q`.
2. §0.73(a) gives `μ` with `μ^{q-1} = −q` and `σ_a μ = ω(a)·μ`.
3. `ν := μ^{(q-1)/N}` satisfies `ν^N = −q` and `σ_g ν = ζ_N·ν` with `ζ_N := ω(g)^{(q-1)/N}`
   primitive.
4. `F₀_w = ℚ_q(ν)`: `X^N + q` is Eisenstein at `q`, hence irreducible, so `[ℚ_q(ν):ℚ_q] = N`; the
   local Galois group of `ℚ_q(ζ_q)/ℚ_q` is cyclic, so its subfield of degree `N` is unique, and both
   `F₀_w` and `ℚ_q(ν)` are such a subfield.
5. `E := ψ.fieldRange` for an embedding `ψ` as in §0.73(c); `E = kummerLevel h (−q)`; transport the
   Brauer class along `cyclicBrauerHom_congr`.
6. `hcarry` follows from step 3 through `carry_iff_of_dlog_eq`; then
   `smoothBrauerHom_kummerSymbolUnits`, `localSymbol_mul_swap` (`Brauer/LocalSymbolUnits.lean:155`)
   and `localSymbol_uniformiser_eq_powerResidue` (`Brauer/TameResidue.lean:238`) evaluate
   `inv_q = ofAdd (−c/N)`.
7. The arithmetic cancellation of §0.72(c) against `inv_p = ofAdd (c/N)` finishes `totalInvariant`.

---

## 0.74 Status (2026-09-01) — **global reciprocity over ℚ in odd prime degree is proven**

`InverseGalois.CFT.totalInvariant_eq_one_of_pow_eq_one` (`CFT/Brauer/RatReciprocity.lean`):

```lean
theorem totalInvariant_eq_one_of_pow_eq_one {N : ℕ} (hN : N.Prime) (hNodd : Odd N)
    {x : BrauerGroup.{0, 0} ℚ} (hx : x ^ N = 1) : totalInvariant ℚ x = 1
```

Sorry-free and axiom-free.  Full build green, 9535 jobs, zero warnings.  This is the sum-of-local-
invariants half of Albert–Brauer–Hasse–Noether over ℚ, for every class of odd prime order — no
longer restricted to the subcyclotomic family of §0.71–0.73.

### (a) The three layers

**Layer 1 — the direct route** (`Brauer/SubcyclotomicSplit.lean`, on top of
`Cyclotomic/AuxiliarySubfield.lean`).  Fix an odd prime `N` and a class `x` with `x^N = 1`.  Choose
an auxiliary prime `q` with `2N ∣ q − 1` and let `F ⊆ ℚ(ζ_q)` be the subfield of degree `N`.  Then:

* `F` is totally real (`2N ∣ q − 1` puts complex conjugation inside the fixing subgroup) and
  totally ramified at `q`, so §0.71–0.73 applies verbatim and every cyclic algebra over `F` with
  rational coefficient has vanishing total invariant;
* a rational prime `p ≠ q` splits completely in `F` exactly when `p^{(q−1)/N} ≡ 1 (mod q)`;
* if no bad prime of `x` splits completely in `F`, then the local degree at each bad place is the
  full `N`, which kills an invariant of order dividing `N`; the real places split `x` because its
  order is odd; so `x ∈ BrauerGroup.relative ℚ F` by the Hasse principle, hence `x` *is* such a
  cyclic algebra and `totalInvariant ℚ x = 1`.

So: **if all bad primes of `x` are `N`-th power non-residues mod one common `q`, reciprocity holds
for `x`.**  This is `totalInvariant_eq_one_of_forall_pow_ne_one`.

**Layer 2 — the corrector** (`Brauer/SubcyclotomicCorrector.lean`).  The direct route cannot be
applied to an arbitrary `x`: with three or more bad primes there need be no single `q` making them
all non-residues.  Instead one *moves* invariants.  For a prime `p` that is a non-residue mod `q`
and any prescribed `t` with `t^N = 1`, `exists_placeInvariant_eq_of_pow_ne_one` produces

```lean
y : BrauerGroup ℚ,  y^N = 1,  totalInvariant ℚ y = 1,
  placeInvariant ℚ (ratPlace p) y = t,  and  placeInvariant ℚ v y = 1 for v ∉ {p, q}.
```

`y` is a power of the cyclic algebra `(F/ℚ, σ_g, p)`.  Its invariant at `p` is
`ofAdd(−c/N)` where `p ≡ g^c (mod q)`, by the ramified computation of §0.72–0.73; non-residuality
of `p` says exactly `N ∤ c` (`not_dvd_of_natCast_pow_ne_one`, via Fermat), and for `N` prime that
makes `ofAdd(−c/N)` a *generator* of the `N`-torsion of `ℚ/ℤ`, so a suitable power hits any `t`
(`exists_pow_ofAdd_intQModZ_eq`, which inverts `c` in the field `ZMod N`).  Its invariants away from
`p` and `q` vanish because the coefficient `p` is a unit there and `F` is unramified there.  Its
total invariant vanishes by layer 1 applied to itself.

**Layer 3 — the descent** (`Brauer/RatReciprocity.lean`).  Induct on `|S|`, where `S` is any finite
set of rational primes containing all bad primes of `x`.

* `|S| ≤ 1`: one auxiliary prime `q ∉ S` with the single bad prime a non-residue suffices — layer 1.
  (`exists_prime_two_mul_dvd_sub_one_pow_ne_one` supplies it: this is `AuxPrimePair` /
  `SplitDensityPair` instantiated at the cyclotomic field `ℚ(ζ_N)`, which is where the
  `2 < N` hypothesis and the nilpotency of `Gal(ℚ(ζ_N)/ℚ)` are used.)
* `|S| ≥ 2`: pick `p₁ ≠ p₂ ∈ S` and an auxiliary `q ∉ S` making **both** non-residues — this is the
  *pair* statement, and it is exactly why `SplitDensityPair`'s two-at-once density bound was built.
  Correctors `y₁, y₂` cancel the invariants at `p₁` and `p₂`.  The new class `x·y₁·y₂` has the same
  total invariant as `x`, still `N`-torsion, and its bad set is inside `insert q (S \ {p₁, p₂})`,
  of cardinality `≤ |S| − 1`.  Apply the inductive hypothesis.

The reason a *pair* is needed, and not one prime at a time, is the accounting: each corrector
introduces one new bad prime `q`, so killing one bad prime keeps the count flat.  Killing two at a
cost of one is what makes the induction terminate.

### (b) New modules

| module | content |
| --- | --- |
| `CFT/Cyclotomic/AuxiliarySubfield.lean` | `exists_nat_primitiveRoot_of_prime`; `exists_intermediateField_subcyclotomic` — the totally real, totally ramified degree-`d` subfield of `ℚ(ζ_q)` with its power-residue splitting law |
| `CFT/Brauer/SubcyclotomicSplit.lean` | `mem_relative_of_forall_not_splitsCompletely`; `totalInvariant_eq_one_of_mem_relative_subcyclotomic`; `totalInvariant_eq_one_of_forall_pow_ne_one` |
| `CFT/Brauer/SubcyclotomicCorrector.lean` | `exists_pow_ofAdd_intQModZ_eq`; `not_dvd_of_natCast_pow_ne_one`; `exists_placeInvariant_eq_of_pow_ne_one` |
| `CFT/Brauer/RatReciprocity.lean` | `exists_prime_two_mul_dvd_sub_one_pow_ne_one`; the induction; `totalInvariant_eq_one_of_pow_eq_one` |

### (c) What is left on the reciprocity line

1. **`N = 2`.**  Every step above uses oddness twice: the real places split a class of odd order
   (`OddArchimedean`), and the subfield of `ℚ(ζ_q)` of degree `N` is totally real only when
   `2N ∣ q − 1`, which for `N = 2` forces `4 ∣ q − 1` but leaves the archimedean invariant alive.
   For `N = 2` the archimedean term must be *computed*, not discarded: the total invariant of a
   quaternion algebra over ℚ has a genuine contribution at the real place.  The repo already has
   `Brauer/RealInvariant.lean` and `Brauer/QuadraticExt.lean`; the missing piece is the real-place
   analogue of the ramified computation.
2. **Prime power and arbitrary order.**  `BrauerGroup ℚ` is torsion (`relative_le_brauerTorsion`),
   so it is the direct sum of its `p`-primary parts; reciprocity for each `x` of order `p^k`
   follows from the prime case only after the corrector is generalised to prescribe an invariant of
   order `p^k`, which needs `2p^k ∣ q − 1` and `ZMod (p^k)`-invertibility of `c` — the latter is
   again just `p ∤ c`, so the argument goes through with `ZMod N` a local ring rather than a field.
   That is the cheapest generalisation and should be done before `N = 2`.  **The local half of it
   is done, see §0.75.**
3. **General number field `k`.**  Base change alone does *not* suffice: the ramified-place
   computation needs the residue degree of the auxiliary place over the rational prime below it to
   be prime to `N`, and over a general `k` that fails.  What is needed is the corestriction
   `Cor : Br(k) → Br(ℚ)` compatible with the local invariants (or, equivalently, a Lubin–Tate
   construction of the local invariant over an arbitrary local field).  The base-change remark that
   `F₀ · k` is cyclic of degree `N` over `k` when `k ∩ ℚ(ζ_q) = ℚ` is still true and still useful,
   but it is not by itself a proof.

### (d) Where this feeds

Reciprocity over ℚ is the last input to the **fundamental class / invariant map** of global class
field theory over ℚ, which is what row 5 (Poitou–Tate) and row 8 (the eight-term sequence) of the
Schmidt–Wingberg tower consume.  It also completes the `Ш²` story of row 3 in the one degree where
the local–global principle for the Brauer group is used directly.

---

## 0.75 Status (2026-09-01) — the local layer of reciprocity now runs at an arbitrary odd exponent

Commit `94944fa`.  Build green, 9536 jobs, no warnings, no sorries, no axioms.

### (a) The new abstraction

`InverseGalois.CFT.IsRadicalExponent n` (in `CFT/Local/RadicalUnramified.lean`) says: for every
field `F` and every `a : F`, `X ^ n - C a` is irreducible exactly when `a` is a power of no prime
order dividing `n`.  Two proofs that it holds:

* `isRadicalExponent_of_prime` — from `X_pow_sub_C_irreducible_iff_of_prime`;
* `isRadicalExponent_of_odd` — from Mathlib's `X_pow_sub_C_irreducible_iff_forall_prime_of_odd`.

Every place in the tame-symbol chain that used to demand a *prime* exponent now demands only
`IsRadicalExponent`: `irreducible_X_pow_sub_C_residue`, `exists_divisionNorm_eq_of_radical_unit`,
`card_gal_kummerLevel_eq_of_not_isPow`, `exists_divisionNorm_eq_kummerLevel`,
`localKummerSymbol_uniformiser_eq_kummerChar`, `localSymbol_uniformiser_eq_kummerChar`,
`localSymbol_uniformiser_eq_powerResidue`.  The "no hypothesis at all" theorem
`localSymbol_uniformiser_eq_powerResidue_of_valued_eq_one` stays prime-gated on purpose: for
composite `n` a unit can be an `ℓ`-th power without being an `n`-th power, and the case split in
its proof collapses.

### (b) The replacement interface: `CFT/Brauer/TameOdd.lean`

Instead of "the power residue exponent of `b`", the symbol is now computed against a *single*
reference unit `u` whose power residue value is a primitive `n`-th root of unity:

* `not_isPow_of_valued_sub_pow_lt_one` — such a `u` is a power of no prime order dividing `n`
  (a root of order `ℓ` would make `ζ ^ (n / ℓ) = 1`);
* `localSymbol_uniformiser_eq_powerResidue_of_exponent_one` — its symbol against a uniformiser is
  `−1/n`;
* `localSymbol_uniformiser_eq_powerResidue_of_congr` — any `b` with `v(b − u^c) < 1` differs from
  `u^c` by a unit congruent to `1`, which is an exact `n`-th power, so its symbol is `−c/n`;
* `localSymbol_eq_powerResidue_of_congr`, `localSymbol_unit_eq_powerResidue_of_congr` — the two
  remaining sign normalisations.

`PlaceRamified`, `PlaceRamifiedAut` and `PlaceConductor` now take the congruence datum `(u, hu,
hu1, hj)` rather than a power residue value, and
`totalInvariant_cyclicBrauerHom_subcyclotomic{,_eq_one}` require only `Odd N`.

### (c) What still gates arbitrary odd `N` at the global layer

Two items, both in the *global* half:

1. `mem_relative_of_forall_not_splitsCompletely` (`CFT/Brauer/SubcyclotomicSplit.lean`) turns
   "`p` does not split completely in `F`" into "`N` divides the local degree" via
   `prime_dvd_finrank_adicCompletion_of_not_splitsCompletely`, and that step is exactly where
   primality is used: for cyclic `Gal(F/ℚ)` of order `N` a proper decomposition subgroup is only
   excluded when `N` is prime.  For `N = ℓ^k` the right hypothesis is "`p` does not split
   completely in the degree-`ℓ` subfield of `F`", i.e. "`p` is not an `ℓ`-th power residue mod
   `q`" — the *same* density input the prime case already uses, so `SplitDensityPair` need not
   change.  What is missing is the group-theoretic transport: the decomposition subgroup of a
   cyclic group of order `ℓ^k` is everything as soon as its image in the quotient of order `ℓ` is
   nontrivial.
2. `exists_pow_ofAdd_intQModZ_eq` (`CFT/Brauer/SubcyclotomicCorrector.lean`) inverts `c` in
   `ZMod N` as a field.  For `N = ℓ^k` replace `hc : ¬ (N : ℤ) ∣ c` by `IsUnit ((c : ZMod N))` and
   `inv_mul_cancel₀` by `ZMod.inv_mul_of_unit`; `not_dvd_of_natCast_pow_ne_one` is then applied at
   the exponent `ℓ` rather than at `N`.

Composite `N` with several prime factors additionally needs simultaneous non-residuality for every
prime divisor, which *is* a new density statement; the prime-power case does not.

---

## 0.76 Status (2026-09-01) — **global reciprocity over ℚ holds for every class of odd order**

Full build green, 9537 jobs, no warnings, no sorries, no axioms.

```lean
theorem totalInvariant_eq_one_of_pow_eq_one {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓodd : Odd ℓ)
    {x : BrauerGroup.{0, 0} ℚ} (hx : x ^ ℓ ^ e = 1) : totalInvariant ℚ x = 1

theorem totalInvariant_eq_one_of_pow_eq_one_odd :
    ∀ n : ℕ, Odd n → ∀ x : BrauerGroup.{0, 0} ℚ, x ^ n = 1 → totalInvariant ℚ x = 1
```

Both in `CFT/Brauer/RatReciprocity.lean`.  This closes both items of §0.75(c) and item 2 of
§0.74(c).

### (a) Prime power: what actually had to change

The global half turned out to need *no new density input at all*.  The point is the arithmetic
identity

```
ℓ^(e-1) · ((q − 1) / ℓ^e)  =  (q − 1) / ℓ ,
```

so a prime `p` that is not an `ℓ`-th power residue mod `q` is, a fortiori, not an `ℓ^e`-th power
residue, and the *decomposition group* of `p` in the cyclic group `Gal(F/ℚ)` of order `ℓ^e` is
already the whole group: `card_stabilizer_under_dvd_iff_mem_fixingSubgroup` reads the order of that
group off the power residue condition (`CFT/Cyclotomic/SubfieldFrobenius.lean`,
`CFT/Cyclotomic/AuxiliarySubfield.lean` conjunct 6), and
`primePow_dvd_finrank_adicCompletion_of_not_dvd` turns it into `ℓ^e ∣ [F_w : ℚ_p]`.  So the density
theorem is invoked at the *prime* exponent `ℓ`, over the field `cycSubfield (ℓ^e)`: splitting
completely there gives `ℓ^e ∣ q − 1` (which is what the subcyclotomic construction needs) while the
non-residue clause is at exponent `ℓ` (which is what the local degree needs).

Concretely, `exists_prime_two_mul_dvd_sub_one_pow_ne_one` now feeds
`exists_prime_splitsCompletely_pow_ne_one₂` with `A = cycSubfield (ℓ^e)` and the primitive `ℓ`-th
root `cycRoot (ℓ^e) ^ ℓ^(e-1)`, and the corrector's coefficient inversion uses

```lean
theorem isUnit_intCast_zmod_of_primePow {ℓ e : ℕ} (hℓ : ℓ.Prime) {c : ℤ} (hc : ¬ (ℓ : ℤ) ∣ c) :
    IsUnit ((c : ZMod (ℓ ^ e)))
```

(`ZMod.unitOfIsCoprime` on `IsCoprime c (ℓ^e)`) in place of the field inverse.  `ZMod (ℓ^e)` is a
local ring, and `c` prime to `ℓ` is exactly a unit of it, so `ofAdd(−c/ℓ^e)` still generates the
`ℓ^e`-torsion of `ℚ/ℤ` and a suitable power hits any prescribed `t`.

### (b) Arbitrary odd order: primary decomposition

`BrauerGroup ℚ` is abelian, so a class killed by `n = ℓ^e · m` with `gcd(ℓ^e, m) = 1` splits as
`x = (x^{ℓ^e})^A · (x^m)^B` for a Bézout pair `1 = ℓ^e A + m B`; `x^m` is killed by `ℓ^e` and
`x^{ℓ^e}` is killed by `m < n`.  Strong induction on `n` at `ℓ = n.minFac` (odd because `n` is),
with `Nat.ordProj_mul_ordCompl_eq_self` and `Nat.coprime_ordCompl` — the same idiom as
`iSup_primaryComponent_eq_top` in `CFT/Brauer/Primary.lean`.

### (c) What is left on the reciprocity line

Only the 2-part, and it is genuinely harder than the odd part; two independent places where
oddness was load-bearing:

1. **The archimedean invariant.**  For odd order the real place is discarded (`OddArchimedean`) and
   the auxiliary subfield of `ℚ(ζ_q)` is chosen totally real.  A class of 2-power order can have
   `inv_∞ = 1/2`, and then no totally real `F` splits it: the Hasse-principle step needs
   `[F_w : ℝ] = 2`, i.e. an *imaginary* `F`.  Taking `q ≡ 3 (mod 4)` and `F = ℚ(√−q) ⊂ ℚ(ζ_q)`
   keeps the ramification at the odd prime `q`, so the tame machinery of §0.71–0.73 still applies —
   but the place count has to grow an archimedean term: `inv_∞ (F/ℚ, σ, a) = 1/2` exactly when
   `a < 0`.  That is the missing computation, and it is the whole of the `N = 2` case.
2. **`IsRadicalExponent 2^k` is false for `k ≥ 2`** (`X⁴ + 4` is reducible while `−4` is not a
   square), so the tame-symbol chain of §0.75(a) does not run at exponent `4`.  For a *totally
   tamely ramified* extension the radical generator is a uniformiser and `X^n − π` is Eisenstein,
   so the irreducibility hypothesis is avoidable there; the unit half of the chain
   (`card_gal_kummerLevel_eq_of_not_isPow`) is the part that really fails and would have to be
   restated for the uniformiser case only.

---

## 0.77 Status (2026-09-02) — **global reciprocity over ℚ, unconditionally, in every degree**

Full build green, 9541 jobs, no warnings, no sorries, no axioms.

```lean
theorem totalInvariant_eq_one (x : BrauerGroup.{0, 0} ℚ) : totalInvariant ℚ x = 1
```

in `CFT/Brauer/RealCorrector.lean`.  This closes §0.76(c) — both obstacles listed there are gone,
and neither was removed the way that section predicted.

### (a) The archimedean obstacle was dodged, not solved

§0.76(c)1 proposed computing `inv_∞` of a cyclic algebra over an imaginary quadratic subfield of
`ℚ(ζ_q)`, `q ≡ 3 (mod 4)`.  That is a real computation and it was not needed.  What the 2-part
actually needs is only *one* class that the reals do not split and whose total invariant is
already known to vanish; multiplying by it is then a bijection of the two cosets of
`BrauerGroup.relative ℚ ℝ`, and the reduction of §0.76 (`totalInvariant_eq_one_of_mem_relative_real`
— the old prime-power proof, with `x ∈ relative ℚ ℝ` promoted from a by-product of oddness to a
hypothesis) applies to the corrected class.

The corrector is the quaternion algebra `z = (−1, ℚ(ζ₃)/ℚ, σ)`, ramified at 3 and at ∞.  Two
observations make it free:

1. Its invariant **at 3** is `1/2`.  This is `placeInvariant_cyclicBrauerHom_conductor`, the
   ramified-place brick of §0.73, at `q = 3`, `N = 2`, `F = L = ℚ(ζ₃)` — the *whole* cyclotomic
   field, not a proper subfield, so no `IsTotallyReal` plumbing and no `⊤`-subfield instances are
   involved.  It evaluates to `((q − 1)/2 : ZMod N) = (1 : ZMod 2)`, i.e. `ofAdd(1/2)`.  Note that
   the hypothesis `2N ∣ q − 1` of `totalInvariant_cyclicBrauerHom_subcyclotomic_neg_one` fails here
   (`4 ∤ 2`) — that failure is exactly why this class is *not* already known to be reciprocal, and
   is what makes it useful.
2. Therefore the reals **do not** split it.  If they did, the reduction would give
   `totalInvariant ℚ z = 1`; but `z` is unramified away from 3 and ∞ (`hunit`: `−1` is a unit at
   every finite place), so the total invariant is the product of just those two factors, and the
   archimedean one would be trivial, leaving `ofAdd(1/2) = 1`.  Contradiction.

Given that, `inv_∞(z)` is a non-trivial square root of `1` in `Multiplicative ℚ/ℤ`, hence is
`ofAdd(1/2)` as well — `QModZ.eq_half_of_add_self_eq_zero`, an elementary parity argument on a
representative — and the two halves cancel: `totalInvariant ℚ z = 1`.

### (b) The radical-exponent obstacle never arose

§0.76(c)2 worried that `IsRadicalExponent (2^k)` is false for `k ≥ 2`.  It is not consumed: the
2-power case is proved by *correcting into* `relative ℚ ℝ` and then invoking the already-built
`totalInvariant_eq_one_of_mem_relative_real` at `ℓ = 2`, whose auxiliary-prime input is
`hasAuxPrimes_two` and whose local layer is the `ℓ = 2` instance of §0.75 — all of which was
already green.  The exponent-`2^k` radical statement is never needed because the *corrector* has
order two, not order `2^k`.

### (c) Assembly

`totalInvariant_eq_one_of_pow_eq_one_two_pow` handles `x^{2^e} = 1`: split on whether the reals
already split `x`; if not, `x · z` lies in `relative ℚ ℝ` (the quotient by it has order two, by
`sq_eq_one_brauerGroup_real`) and is killed by `2^{max e 1}`.
`totalInvariant_eq_one_of_pow_eq_one_nat` splits `n = 2^k · m` by
`Nat.ordProj_mul_ordCompl_eq_self` and recombines the two-power and odd parts by Bézout.  Finally
`Monoid.IsTorsion (BrauerGroup ℚ)` (`exists_pow_eq_one`, valid over any perfect field) removes the
order hypothesis entirely.

### (d) What is left on the reciprocity line

Only §0.76(c)3, the **general number field** `k`: the ramified-place computation needs the residue
degree of the auxiliary place over the rational prime below it to be prime to `N`, which fails over
a general `k`.  The fix is corestriction `Cor : Br(k) → Br(ℚ)` compatible with local invariants, or
a Lubin–Tate construction of the local invariant over an arbitrary local field.  Rows 5 and 8 of
the §0.36 table (Poitou–Tate, the eight-term sequence) consume reciprocity over the base field of
the Schmidt–Wingberg tower, so this is now the next item on the critical path.

---

## 0.78 Plan (2026-09-02) — global reciprocity over a general number field, by norm comparison

This section records the chosen route for §0.77(d) so that it survives context loss.  Target:

```lean
theorem totalInvariant_eq_one_general (k : Type) [Field k] [NumberField k]
    (x : BrauerGroup.{0, 0} k) : totalInvariant k x = 1
```

### (a) Routes considered and rejected

1. **Cohomological corestriction on `Br(k) = H²(G_k, k̄ˣ)`.**  `CFT/GroupCohomology/Corestriction.lean`
   already has `cor` with `res ≫ cor = [G:S] • id`.  But Mathlib's `BrauerGroup` is
   central-simple-algebra based; connecting it to `H²(G_k, k̄ˣ)` *and* proving the global
   Mackey/Shapiro compatibility `res_{ℚ_p} ∘ Cor_{k/ℚ} = Σ_{v|p} Cor_{k_v/ℚ_p} ∘ res` is strictly
   more work than the direct route below.
2. **Class formation / fundamental class.**  `Units/GlobalTate.lean` and `Units/BaseFundamental.lean`
   give the class formation over an arbitrary base, but `globalFundamentalClass` is an
   `Exists.choose`, so the invariant map is not pinned to `Σ_v inv_v`.  Order counting cannot break
   the circle; only a genuine computation can.
3. **Restriction only.**  `totalInvariant k (Res y) = [k:ℚ] · totalInvariant ℚ y = 0` is cheap
   (via `Ideal.sum_ramification_inertia`) but `Res : Br(ℚ) → Br(k)` is not surjective.
4. **Rational coefficients over `k`.**  The invariant vectors reachable with `a ∈ ℚˣ` are too
   constrained; "two places suffice" is a ℚ-specific accident of `RatCount.lean`.

### (b) The norm-comparison route

Let `F ⊆ ℚ(ζ_q)` be the totally real cyclic subfield of degree `M` used on the ℚ side, and let
`a ∈ kˣ`.  Compare

```
totalInvariant k (cyclicBrauerHom (F·k / k) a)   vs.   totalInvariant ℚ (cyclicBrauerHom (F/ℚ) (N_{k/ℚ} a))
```

place by place.  The right-hand side is `1` by `totalInvariant_eq_one` (§0.77).  Hand check:

* **`p ≠ q`** (so `F/ℚ_p` is unramified).  Left side at `v | p`:
  `χ(Frob_v|_F) · w_v(a) = f_v · χ(Frob_p) · w_v(a)`, because `Frob_v|_F = Frob_p^{f_v}`.
  Right side at `p`: `χ(Frob_p) · v_p(N_{k/ℚ} a) = χ(Frob_p) · Σ_{v|p} f_v · w_v(a)`.  Equal after
  summing over `v | p`.
* **`p = q`** (`F/ℚ_q` totally tamely ramified of degree `M | q − 1`, `k_v/ℚ_q` unramified of
  degree `f`).  The tame symbol over `𝔽_{q^f}` is `ā^{(q^f − 1)/M}`; the ℚ side is
  `(N̄a)^{(q − 1)/M} = ā^{(1 + q + ⋯ + q^{f−1})(q − 1)/M} = ā^{(q^f − 1)/M}`.  Literally equal.
* **archimedean**: both trivial, `F` being totally real (`2 · deg | q − 1`).

**Reduction.**  Take `M = ℓ^{e+t}` with `t = v_ℓ([k:ℚ])`; choose `q` by the existing ℚ-side density
theorem `exists_prime_two_mul_dvd_sub_one_pow_ne_one` (`RatReciprocity.lean`) with `T` containing
the primes ramified in `k` and the bad primes.  Then `k ∩ ℚ(ζ_q) = ℚ` automatically, because every
nontrivial subfield of `ℚ(ζ_q)` is ramified at `q`.  No non-residue condition over `k` is needed.

**Grouping.**  The place-by-place comparison needs a sum over the places of `k` above each rational
prime.  Since `Ideal.inertiaDeg p P = 0` whenever `P` does not lie over `p` (it is the `else`
branch of the definition), that sum can be written as a plain `∑ᶠ W : HeightOneSpectrum (𝓞 K)` with
no `if` and no explicit "primes over" `Finset`.  Downstream, `Finset.prod_fiberwise_of_maps_to`
converts the `finprod` over places of `k` into a product over rational primes.

### (c) Brick decomposition

1. `CFT/Brauer/NormPlaceValue.lean` — **landed 2026-09-02**.  `primeCount` and its API,
   `primeCount_relNorm`, `placeOrd` and its API, `placeOrd_norm`, `placeValue_normUnit`:
   *the value at a place of the base of the norm of a unit is `Σ_W f_W · (value at W)`*.
2. Frobenius compatibility: `Frob_v|_F = Frob_p^{f_v}` under `Gal(F·k/k) ≅ Gal(F/ℚ)`.
   **Landed 2026-09-02** as `CFT/Brauer/ResidueCardDegree.lean` + `CFT/Brauer/PlaceFrobeniusDegree.lean`.
3. Place-by-place comparison at the unramified primes, plus the fibrewise grouping.
   **Landed 2026-09-02** as `CFT/Brauer/PlaceSubcyclotomicBase.lean`.
4. The tame place at `q`: the general-`k` analogue of `PlaceConductor.lean` /
   `PlaceSubcyclotomic.lean`, for `k_v/ℚ_q` unramified of degree `f_v`.
   **Landed 2026-09-02** as `CFT/Brauer/ResidueGenerator.lean` (4a) +
   `CFT/Brauer/PlaceConductorBase.lean` (4b).  4b assumes the coefficient is a **unit at `v`**; see
   the note on that hypothesis below.
5. Archimedean triviality for totally real `F`.  **Landed 2026-09-02** as
   `CFT/Brauer/TotallyRealInvariantBase.lean`.
6. The norm dictionary between the residue fields above `q` and the prime field.  **Landed
   2026-09-02** as `CFT/Brauer/NormReduction.lean` (the norm of an element of a product is the
   product of the norms; the norm reduces modulo a maximal ideal of the base to the norm of the
   reduction) and `CFT/Brauer/NormFactors.lean` (the Chinese remainder splitting of the reduction,
   hence `N(a) mod q = ∏_{v|q} N_{κ(v)/𝔽_q}(ā_v)`; and `x^{(Q_v−1)/N} = N_{κ(v)/𝔽_q}(x)^{(q−1)/N}`).
7. The `Fk` setup: `K = k(ζ_q)`, `Gal(K/k)` cyclic of order `q − 1`, the subfield `F` of degree `N`,
   totally real, totally ramified at `q`.
8. Norm comparison assembly; the split criterion over `k` (the analogue of `SplitLocalDegree.lean`
   and `mem_relative_of_forall_not_dvd_primePow`); and the reduction of a general `x ∈ Br(k)` of
   `ℓ`-power order (primary decomposition and Bézout, as in §0.77(c)).

### (d) The unit hypothesis at `q` is free

Brick 4b computes the invariant at `v | q` only for a coefficient `a` that is a **unit at `v`**, and
over a general `k` the `a` produced by `exists_cyclicBrauerHom_eq` has arbitrary, non-uniform
valuations at the places above `q`.  Over `ℚ` this never arose, because `ℚˣ` is generated by `−1`
and the primes and each generator is handled separately; over `k` there is no such generation, and
`kˣ / (q-units · ℚˣ) ≅ (⊕_{v|q} ℤ)/diagonal` is nontrivial as soon as two places lie over `q`.

The hypothesis costs nothing all the same, because **`cyclicBrauerHom` kills norms**: if
`c ∈ N_{Fk/k}((Fk)ˣ)` then `cyclicBrauerHom a = cyclicBrauerHom (a · c)`, so `a` may be replaced by
any element of its coset.  For `w` the unique place of `Fk` over `v | q` (the extension is totally
ramified there) one has `ord_v(N_{Fk/k} β) = ord_w(β)`, and `ord_w` is surjective onto `ℤ`; by the
approximation theorem in the Dedekind domain `𝓞_{Fk}` there is a single `β` realising any
prescribed vector of valuations at the finitely many places over `q`.  So one may always arrange
that `a` is a unit at every place above `q`.  This is why the local–global norm decomposition
`k ⊗_ℚ ℚ_q ≅ ∏_{v|q} k_v` — which is absent from Mathlib — is **not** needed: the reduction
`N(a) mod q = ∏_{v|q} N_{κ(v)/𝔽_q}(ā_v)` of brick 6, valid for `q`-units, suffices.

---

## 0.79 Status (2026-09-02) — **global reciprocity over an arbitrary number field is proven**

Commit `bd1779b`, full build green at **9586 jobs**, no warnings, and

```lean
theorem InverseGalois.CFT.totalInvariant_eq_one_base (k : Type) [Field k] [NumberField k]
    (x : BrauerGroup.{0, 0} k) : totalInvariant k x = 1
```

in `CFT/Brauer/BaseReciprocity.lean`, with axioms `[propext, Classical.choice, Quot.sound]`.
**Row 6 of the §0.36 table is closed.**  Every brick of the §0.78 plan is landed; what this section
records is the last stage, the two-primary part, which §0.78 had not planned in detail.

### (a) Why the odd part did not finish the job

`totalInvariant_eq_one_of_pow_eq_one_odd_base` (§0.78, `BaseOddReciprocity.lean`) covers a class of
odd order because the auxiliary prime argument needs the class to be split at every infinite place,
and a class of odd order in `Br(ℝ) ≅ ℤ/2` is automatically split.  For a class of two-power order
the archimedean invariants are genuinely there and have to be cleared first.  Concretely,
`totalInvariant_eq_one_of_forall_pow_ne_one_primePow_base` takes an explicit hypothesis

```lean
(harch : ∀ u : InfinitePlace k, infinitePlaceInvariant k u x = 1)
```

so what the `ℓ = 2` case needs is a way to *modify* `x` by something of known total invariant until
`harch` holds.

### (b) The correction: sign correctors and sign approximation

Two inputs, both new.

1. **A sign corrector** (`CFT/Brauer/BaseSignCorrector.lean`, `exists_signCorrector_base`).  For a
   prime `q ≡ 3 (mod 4)` unramified in `k`, the quadratic subfield of `ℚ(ζ_q)` is *imaginary*, so
   the cyclic algebra attached to `(F·k)/k` and a coefficient `a ∈ kˣ` has invariant at a real
   place `u` equal to the **sign** of `a` under the real embedding of `u`.  It has order dividing
   two and total invariant `1`, the latter by the odd-order reciprocity already proven (the class
   is of order two, but the *coefficient* side is what the odd machinery consumes — see
   `RealCyclicSign.lean` and `FibreTotal.lean`).  So

   ```lean
   Y : kˣ →* BrauerGroup k,   Y a ^ 2 = 1,   totalInvariant k (Y a) = 1,
   infinitePlaceInvariant k u (Y a) = realCyclicInvariant (sign of a at u)
   ```

2. **Sign approximation** (`NumberTheory/SignApproximation.lean`,
   `exists_units_pos_iff_notMem_set`).  *Every* pattern of signs at the real places of a number
   field is realised by a unit.  Mathlib v4.28 has **no** weak-approximation lemma for infinite
   places, so this was built from scratch and elementarily: a primitive element `θ` takes pairwise
   distinct real values at the real places (two ring homs `k →+* ℝ` agreeing on `θ` agree
   everywhere, via `RingHom.toRatAlgHom` and `AlgHom.ext_of_adjoin_eq_top`); with
   `δ := min (insert 1 {|θ_w − θ_{u₀}|})` positive, two rationals `c < d` straddling `θ_{u₀}`
   inside `δ` make `(θ − c)(θ − d)` negative at `u₀` and positive at every other real place; a
   `Finset.induction_on` multiplies these together.  This is worth remembering as a **reusable
   substitute** for infinite-place approximation anywhere else in the tree.

Given `x`, apply (2) to `S = {u | infinitePlaceInvariant k u x ≠ 1}` and multiply: since `Br(ℝ)`
has order two, "`x` and `Y a` are split at `u` together" already forces `inv_u(x · Y a) = 1`
(`infinitePlaceInvariant_mul_eq_one_of_isReal`).  The product has two-power order, is split at
every infinite place, and has the same total invariant as `x`.

### (c) The auxiliary prime `q ≡ 3 (mod 4)`

Mathlib has no usable Dirichlet-in-progressions statement, and the repo's dyadic family produces
`q ≡ 1 (mod 2^d)` — the wrong congruence.  The fix: `q ≡ 3 (mod 4)` is exactly "`q` does not split
completely in `ℚ(ζ_4)`", and `infinite_setOf_splitsCompletely_not_splitsCompletely ℚ (ℚ(ζ_4))`
(degrees `1 < 2`) supplies infinitely many such primes.  That is
`exists_prime_three_mod_four_notMem`.

For the auxiliary prime of the two-power argument itself, the bookkeeping with
`L := Nat.log 2 (finrank ℚ k)` is: take `M := P.card + 3` (so `3 ≤ M` and `P.card < 2^{M−1}`) and
`d := e + L + P.card + 2` (so `d − e − L + 1 = M`), and call the dyadic family at `d + 1` so that
`2 · 2^d ∣ q − 1`.

### (d) Assembly

`totalInvariant_eq_one_of_pow_eq_one_nat_base` splits an arbitrary finite order `n = 2^c · m` with
`m` odd, uses Bézout to write `x = (x^{2^c})^α · (x^m)^β`, and applies the two-power case to `x^m`
and the odd case to `x^{2^c}`.  `exists_pow_eq_one` (every Brauer class of a perfect field has
finite order) then gives the unconditional statement.

### (e) What this unblocks

Rows 5 and 8 of the §0.36 table — the Poitou–Tate input — consume reciprocity over the base field
of the tower, not just over `ℚ`.  That hypothesis is now discharged.  The next brick is row 5,
`Ш²(k, A) ≅ Ш¹(k, A′)^∨`, and then row 8, the eight-term sequence for `μ_p` over `k_S`.

---

## 0.80 Status (2026-09-02) — row 6 packaged: the product formula in usable form, and the local factor

`CFT/Brauer/CyclicProduct.lean`, full build green at **9587 jobs**, no warnings, axioms
`[propext, Classical.choice, Quot.sound]`.  §0.79 proved global reciprocity as a statement about
`totalInvariant`; this section turns it into the statements a *consumer* wants, and identifies what
a single local factor means.

### (a) The product formula, in three shapes

`totalInvariant` is by definition `(∏ᶠ v, placeInvariant k v x) * ∏ u, infinitePlaceInvariant k u x`,
so `totalInvariant_eq_one_base` gives immediately

```lean
theorem finprod_placeInvariant_mul_prod_infinitePlaceInvariant_eq_one (x : BrauerGroup.{0,0} k) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x) *
        ∏ u : InfinitePlace k, infinitePlaceInvariant k u x = 1
```

and, composed with the general-base `finprod_placeInvariant_eq_prod` of `RatCount.lean`, the form
that SW Theorem 13 consumes — a genuine `Finset.prod` over any finite set of finite places outside
which the invariants vanish, times the finitely many archimedean terms:

```lean
theorem prod_placeInvariant_mul_prod_infinitePlaceInvariant_eq_one (x : BrauerGroup.{0,0} k)
    (S : Finset (HeightOneSpectrum (𝓞 k))) (h : ∀ v ∉ S, placeInvariant k v x = 1) :
    (∏ v ∈ S, placeInvariant k v x) * ∏ u : InfinitePlace k, infinitePlaceInvariant k u x = 1
```

Specialised to the classes that carry the arithmetic these are one-liners, because the Brauer class
is all that reciprocity sees: `totalInvariant_cyclicBrauerHom` for a cyclic algebra
`(K/k, σ₀, a)`, `totalInvariant_smoothBrauerHom` for the Brauer class of a smooth `H²`, and

```lean
theorem totalInvariant_smoothBrauerHom_kummerSymbolUnits (h : IsKummerData k Ω M ι n)
    (Φ : M →* M →* M) (a b : kˣ) :
    totalInvariant k (smoothBrauerHom (kummerSymbolUnits h Φ a b)) = 1
```

which is `∏_v (a, b)_v = 1`, the product formula for the `n`-th power residue symbol over an
arbitrary number field — the last unproved input of the `p = 2` half of SW Theorem 13 that was not
a duality statement.

### (b) What a single local factor is

The same base change that proves the formula also says what one factor measures.  Over the
completion the cyclic algebra becomes the cyclic algebra of the decomposition group with the *same*
coefficient (`baseChangeHom_cyclicBrauerHom_adicCompletion`, §0.67), and a cyclic algebra is split
exactly when its coefficient is a norm (`mem_ker_cyclicBrauerHom_iff`).  Chaining those through
`placeInvariant_eq_one_iff` (which unfolds `BrauerGroup.relative` to a kernel membership) gives, in
five rewrites,

```lean
theorem placeInvariant_cyclicBrauerHom_eq_one_iff (w : HeightOneSpectrum (𝓞 K))
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) (a : kˣ) :
    placeInvariant k (primeUnder (𝓞 k) w) (cyclicBrauerHom hσ₀ a) = 1 ↔
      ∃ b : (w.adicCompletion K)ˣ,
        Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) (b : w.adicCompletion K)
          = algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k) (a : k)
```

So the product formula is exactly the statement that the failures of `a` to be a local norm cancel.
Combined with ABHN (`eq_one_of_forall_invariant_eq_one`) this is one archimedean lemma short of the
**Hasse norm theorem** for cyclic extensions; the missing piece is the infinite-place mirror of
`PlaceCyclic.lean`, for which `Units/InfiniteDecompositionField.lean` already supplies the whole
decomposition-field plumbing (`localInfiniteDecompositionEquiv`,
`algebraMap_localInfiniteDecompositionEquiv`), so it is a transcription rather than a new argument.

### (c) Where this leaves the table

Row 6 is now closed *and packaged*.  Rows 5 and 8 — Poitou–Tate — are untouched and remain the
wall; row 7's `p = 2` leftover ("every `S`-ideal class contains a prime") still waits on ray-class
`L`-functions that Mathlib does not have.

---

## 0.81 Status (2026-09-02) — **the Hasse norm theorem is proven**

Commit: build green at **9589 jobs**, zero warnings, zero errors; all seven new theorems have
axioms `[propext, Classical.choice, Quot.sound]`.

The archimedean lemma flagged as missing in §0.80(b) is now in place, and with it the Hasse norm
theorem for cyclic extensions of number fields.

### (a) `InverseGalois/CFT/Brauer/InfiniteCyclic.lean` — the infinite-place mirror

A transcription of `PlaceCyclic.lean` with `HeightOneSpectrum (𝓞 K)` replaced by
`InfinitePlace K`, `adicCompletion` by `Completion`, `primeUnder (𝓞 k)` by
`comap (algebraMap k K)`, and the decomposition-field plumbing taken from
`Units/InfiniteDecompositionField.lean`.  Three theorems:

* `exists_forall_mem_zpowers_restrictScalars_eq_infinite` — the decomposition group at `w` is a
  subgroup of a finite cyclic group, hence `Subgroup.zpowers (σ₀ ^ (stabilizer Gal(K/k) w).index)`
  (`subgroup_eq_zpowers_pow` fed by `Subgroup.index_mul_card`), and
  `localInfiniteDecompositionEquiv` identifies it with
  `w.Completion ≃ₐ[(w.comap (algebraMap k K)).Completion] w.Completion`.  So the local Galois group
  has a generator whose restriction to `K` is that power.
* `baseChangeHom_cyclicBrauerHom_infiniteCompletion` — factor the base change through the
  decomposition field: `baseChangeHom_cyclicBrauerHom` for the first step (coefficient untouched),
  `baseChangeHom_cyclicBrauerHom_compositum` for the second (coefficient untouched), and
  `IsScalarTower.algebraMap_apply` to compose the two coefficient maps.
* `infinitePlaceInvariant_cyclicBrauerHom_eq_one_iff` — the same five-rewrite chain as at a finite
  place, ending in `rfl` to reconcile `↑(Units.map ↑(algebraMap k M) a)` with `algebraMap k M ↑a`.

The whole file typechecked on the first attempt; there was genuinely no new mathematics in it,
which is a good sign that the finite/infinite split in the invariant layer is drawn in the right
place.

### (b) `InverseGalois/CFT/Brauer/HasseNorm.lean`

Both directions are statements about the single Brauer class `cyclicBrauerHom hσ₀ a`.

*Forward.*  If `a` is a global norm then `mem_ker_cyclicBrauerHom_iff` makes the class trivial, so
every local invariant is `map_one`, so by the two `…_eq_one_iff` lemmas `a` is a local norm at
every finite and every infinite place.

*Converse.*  If `a` is a local norm everywhere then every local invariant vanishes — the quantifier
is over places of `K`, and every place of `k` is hit, by `exists_primeUnder_eq` at the finite
places and `NumberField.InfinitePlace.comap_surjective` at the infinite ones — so
`eq_one_of_forall_invariant_eq_one` (ABHN, §0.72) kills the class, and
`mem_ker_cyclicBrauerHom_iff` returns the global norm.

```lean
theorem exists_norm_eq_of_forall_local (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 K), ∃ b : (w.adicCompletion K)ˣ,
      Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) (b : w.adicCompletion K)
        = algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k) (a : k))
    (hinf : ∀ w : InfinitePlace K, ∃ b : (w.Completion)ˣ,
      Algebra.norm (w.comap (algebraMap k K)).Completion (b : w.Completion)
        = algebraMap k (w.comap (algebraMap k K)).Completion (a : k)) :
    ∃ b : Kˣ, Algebra.norm k (b : K) = (a : k)
```

`exists_norm_eq_iff_forall_local` packages the two directions as a single `Iff`.

### (c) Where this leaves the table

Rows 6 and 7 (modulo the `p = 2` leftover) are closed and packaged, and the Hasse norm theorem is
a bonus consequence that costs nothing further.  Rows 5 and 8 — Poitou–Tate — remain the wall, and
`SplitPrimePowerEP` is still the sole remaining hypothesis of `Shafarevich/Main.lean`.

Worth noting for the Poitou–Tate work: the Hasse norm theorem is precisely the `H⁰`-level statement
that `Ш(k, N_{K/k})` vanishes for a *cyclic* `K/k`, i.e. the cyclic case of the local–global
principle for a norm torus.  Its proof here goes through the Brauer group rather than through
duality, so it does not by itself give any of the Ш machinery; but it does confirm that the
invariant layer is now strong enough to state and prove local–global principles, which is the
shape everything in rows 5 and 8 will take.

---

## 0.82 Status (2026-09-02) — the idele-generation layer no longer needs a principal ideal ring, and §0.36(a) was stale

Two housekeeping items, one a genuine generalization and one a correction to this document.

### (a) `Units/IdeleGen.lean` and `Units/IdeleQuotCyclic.lean` work over any number field

`exists_sub_adicPlaceIdele_mem_sup` used to carry `[IsPrincipalIdealRing (𝓞 k)]`, purely so that a
prescribed system of orders `n : HeightOneSpectrum (𝓞 k) → ℤ` of cofinite support could be realized
by a single element of `kˣ`.  Over a base with a nontrivial class group that is false, but it is
false only on a *finite* set of primes: `Units/ClassSet.lean` already proves

```lean
exists_finite_ord_repr (K) : ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧
  ∀ n, (∀ᶠ v in Filter.cofinite, n v = 0) → ∃ a : Kˣ, ∀ v ∉ T, ord K v (a : K) = n v
```

so the hypothesis to carry is the conclusion of that lemma, not the principality.  The signature now
takes an exceptional set `T`, requires the distinguished place `q ∉ T`, and *weakens* the local-norm
hypothesis `hfin` at the places of `T`: outside `T` one still only needs units of the valuation ring
to be norms, but at a place of `T` every element of the base completion must be one, because after
subtracting the principal idele the component there need not be a unit.  Concretely `hfin` becomes

```lean
(hfin : ∀ w : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) w ≠ q →
  ∀ b : ((primeUnder (𝓞 k) w).adicCompletion k)ˣ,
    (primeUnder (𝓞 k) w ∉ T → unitVal (Additive.ofMul b) = 0) →
      b ∈ normSubgroup ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K))
```

The same replacement runs through the four theorems of `Units/IdeleQuotCyclic.lean`
(`forall_mem_multiples_ideleQuot`, `addOrderOf_ideleQuot_eq`,
`exists_addOrderOf_H2_ideleClassRep_eq`, `exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep`), and
`Units/RatFundamentalClass.lean` instantiates `T := ∅` — over `ℚ` the ring of integers is principal,
so the exceptional set is empty and `hfin`'s new premise is discharged by `Set.notMem_empty`.

Two Lean notes.  `Rigidity.RET.ord` lives in the **top-level** `Rigidity` namespace
(`Rigidity/RET/Genus/Ord.lean:46`), so a file that does not `open Rigidity.RET` silently turns `ord`
into an auto-bound implicit and reports "Function expected at `ord` but this term has type `?m.8`".
And Mathlib v4.28 spells it `Set.notMem_empty`, not `Set.not_mem_empty`.

### (b) §0.36(a) is stale: the general-base class formation was already built

§0.36(a) said that a class formation over an arbitrary number field base "needs only" the compositum
`k·F₀` with a cyclic totally real `F₀ ⊂ ℚ(ζ_q)`, and called that a bounded mechanical project.  That
project is unnecessary: `InverseGalois/CFT/Units/BaseFundamental.lean` already proves

```lean
theorem exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_base (k K) :
    ∃ α : ↥(H2 (ideleClassRep k K)), ∀ m : ℤ, m • α = 0 → (Nat.card Gal(K/k) : ℤ) ∣ m
```

for every pair of number fields `k ⊆ K` with `K/k` Galois, and it does so **without** constructing
any auxiliary cyclic extension of `k`.  The route is restriction followed by inflation:

* `exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_of_rat` restricts the `ℚ`-fundamental class of a
  Galois `L/ℚ` to the subgroup `S = (galRestrictScalarsHom ℚ k L).range ≅ Gal(L/k)`, using
  `tateRes` and `exists_zsmul_eq_zero_imp_dvd_H2_of_addEquiv`;
* `exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_of_top` inflates from `Gal(L/k)` to `Gal(K/k)` for
  `k ⊆ K ⊆ L`, via `mem_range_inflTwo_of_resTwo_eq_zero` and `eq_zero_H1_res_subgroup`;
* the base theorem takes `L = ↥(IntermediateField.normalClosure ℚ K (AlgebraicClosure K))` and
  composes the two.

So the generalization of (a) is a convenience for the *statement* of the idele-generation lemmas,
not a prerequisite for anything; the class formation over an arbitrary number field is already
unconditional, and `BaseTate.lean` / `BaseArtin.lean` already carry Tate's theorem and the Artin map
over that base.

Build green at **9589 jobs**, zero warnings, zero errors; the three touched theorems have axioms
`[propext, Classical.choice, Quot.sound]`.

---

## 0.83 Status (2026-09-02) — Chebotarev for cyclic prime-power extensions, with no analysis

`InverseGalois/CFT/Units/InertPlace.lean` is new.  It is a purely group-theoretic reading of a
theorem the repository already had, and it removes what §0.79 called the blocking sub-task of the
fundamental exact sequence.

### (a) The input

`Units/DecompositionOutside.lean` proves, for a Galois `K/k` of number fields with **solvable**
Galois group and any *finite* set `S` of places of `k`,

```lean
decompositionSubgroupOutside_eq_top (hS : S.Finite) :
  Subgroup.closure {σ | ∃ v : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) v ∉ S ∧ σ • v = v} = ⊤
```

— the decomposition groups of the places lying over the primes *outside* `S` generate everything.
That is the whole analytic content one usually imports from Chebotarev, and it was obtained here
from the class-formation machinery, not from a density theorem.

### (b) What it gives, by pure group theory

Reading the generation statement contrapositively yields four consequences, each in the new file.

* `exists_stabilizer_not_le`: for `H ≠ ⊤` there is a place outside `S` whose stabilizer is **not**
  contained in `H`.  (A subgroup containing every generator is everything.)
* `exists_mem_stabilizer_pow_ne_one`: if `G = ⟨σ₀⟩` is cyclic and `σ₀ ^ m ≠ 1`, some place outside
  `S` carries a decomposition element `τ` with `τ ^ m ≠ 1`.  Here the abelian case does not even
  need the solvability hypothesis to be supplied — `isSolvable_of_comm` produces it.
* `exists_card_stabilizer_not_dvd`: the same statement about orders, i.e. **the local degrees of a
  cyclic extension have the global degree as their lcm**, and every exponent that fails to kill a
  generator is missed by some local degree.  This is exactly the surjectivity input for
  `Σ_v inv_v : ⊕_v Br(K_w/k_v) → (1/n)ℤ/ℤ`.
* `exists_stabilizer_eq_top_of_isPGroup`: for `G` cyclic of **prime-power** order, some place
  outside `S` has decomposition group all of `G`.  The proof takes `m = p^(a-1)` where
  `p^a = orderOf σ₀`, extracts a `τ` of order not dividing `p^(a-1)`, hence of order `p^a`, hence a
  generator.

### (c) The packaged form

Discarding, in addition, the finitely many ramified primes (`finite_relRamifiedSet`) turns the last
item into a genuine density statement:

```lean
exists_arithFrobAt_zpowers_eq_top (hp : p.Prime) (hσ₀ : ∀ x, x ∈ Subgroup.zpowers σ₀)
    (hne : σ₀ ≠ 1) (hpG : IsPGroup p Gal(K/k)) (hT : T.Finite) :
  ∃ v ∉ T, v ∉ relRamifiedSet k K ∧ ∃ P …,
    stabilizer Gal(K/k) P = ⊤ ∧ Subgroup.zpowers (arithFrobAt (𝓞 k) Gal(K/k) P) = ⊤
```

For a cyclic extension of prime-power degree, avoiding any prescribed finite set of primes, there is
an unramified prime whose **arithmetic Frobenius generates the Galois group** — Chebotarev in the
only case Scholz–Reichardt and the Schmidt–Wingberg tower ever use it, obtained with no `L`-function
and no analysis.  It supersedes `exists_relStabilizer_eq_zpowers`
(`CFT/RelativeFrobenius.lean:273`), which was restricted to `(orderOf σ).Prime`.

### (d) Three Poitou–Tate shortcuts that do not work

Recorded so they are not retried.

1. A pairing `Ш²(k,A) × Ш¹(k,A′) → ℚ/ℤ` by itself does not give the direction that is needed,
   `Ш¹(k,A′)^∨ ↠ Ш²(k,A)`; nondegeneracy on both sides (or one side plus a cardinality comparison)
   is the honest content of the duality, and there is no cheaper packaging of it.
2. `H²(G, I_K) → H²(G, C_K)` is **not** surjective for general non-cyclic `G` — an everywhere
   unramified `(ℤ/2)²` extension is a counterexample — so "cyclic" is essential in the fundamental
   exact sequence and cannot be relaxed to reach the general case.
3. The route through `Ĥ³(G, K^×) ≅ Ĥ¹(G, K^×) = 1` needs odd-degree cyclic periodicity, which
   `Units/CyclicTate.lean` does not have (it carries only `tateH0AddEquivH2`).

Two Lean notes.  The divisibility-of-prime-powers lemma must be spelled
`Nat.pow_dvd_pow_iff_le_right`; the unqualified name is visible only inside `namespace Nat`.  And
the *relative* ideal action `MulAction Gal(K/k) (Ideal (𝓞 K))` needs `open scoped Pointwise`, the
same requirement already recorded for `Ideal (𝓞 F)` under `Gal(F/ℚ)`.

Build green at **9590 jobs**, zero warnings, zero errors; all five theorems have axioms
`[propext, Classical.choice, Quot.sound]`.

---

## 0.84 Status (2026-09-02) — the local degrees of a cyclic extension, and a route that avoids Poitou–Tate altogether

`InverseGalois/CFT/Units/LocalDegreeLcm.lean`.

### (a) The degree is the least common multiple of the local degrees

The order of the decomposition group at `v` is the local degree `n_v = [K_w : k_v]`, and it divides
`n = [K:k]`.  §0.83(b)'s `exists_card_stabilizer_not_dvd` gives the converse prime by prime, and the
new module collects the places:

* `exists_finset_dvd_lcm_card_stabilizer` — for cyclic `Gal(K/k)` with generator `σ₀` and any finite
  set `S` of primes of the base, there is a `Finset F` of places of `K`, all lying over primes
  outside `S`, with `n ∣ F.lcm (fun v => n_v)`.
* `exists_finset_gcd_localDegree_eq_one` — for the same `F`, `Nat.gcd n (F.gcd fun v => n / n_v) = 1`.
* `exists_finset_intCombination_localDegree_modEq` — hence there are integers `c_v` with
  `∑_{v ∈ F} c_v · (n / n_v) ≡ 1 (mod n)`.

The first proof runs over `p ∈ n.primeFactors`, applying `exists_card_stabilizer_not_dvd` with
exponent `n / p` (legitimate because `orderOf σ₀ = n`, so `σ₀ ^ (n/p) ≠ 1`), and then uses the
elementary fact that a divisor `L ∣ n` with `L ≠ n` divides `n / p` for `p` any prime factor of
`n / L`.  No `p`-adic valuations appear anywhere.  The second proof is equally valuation-free: if
`g` divides `n` and every `n / n_v`, then every `n_v` divides `n / g`, so the least common multiple
does too, so `n ∣ n / g` and therefore `g = 1`.  The third is Bézout, via a general auxiliary lemma
`exists_intCombination_eq_finsetGcd` (a greatest common divisor of a `Finset`-indexed family of
naturals is an integral linear combination of it, by induction on the `Finset` from
`Nat.gcd_eq_gcd_ab`), which Mathlib v4.28 does not have.

This is exactly the arithmetic input for **surjectivity of `Σ_v inv_v : ⊕_v Br(K_w/k_v) → (1/n)ℤ/ℤ`**:
the image of `Br(K_w/k_v)` in `(1/n)ℤ/ℤ` is the subgroup generated by `(n/n_v)·(1/n)`, and the third
theorem says those subgroups generate.

### (b) Middle exactness of the cyclic fundamental sequence needs no `H³`

The fundamental exact sequence for a cyclic extension,

    0 → Br(K/k) → ⊕_v Br(K_w/k_v) --Σ inv_v--> (1/n)ℤ/ℤ → 0,

decomposes into three independent statements, and the repository's distance to each is now known.

* **Injectivity** is Albert–Brauer–Hasse–Noether, `brauerToCompletions_injective`
  (`Brauer/HasseNoether.lean:126`) — done.
* **`im ⊆ ker`** is global reciprocity, `totalInvariant_eq_one_base` — done.
* **Surjectivity** needs only `lcm_v n_v = n`, which is (a) — done.
* **Middle exactness** is the long exact sequence of `0 → K^× → I_K → C_K → 0` together with
  injectivity of the invariant map on `H²(G, C_K)`.  It does **not** require `Ĥ³(G, K^×) = 1`.

That last point corrects the framing of §0.83(d) item 3: the odd-degree periodicity `Ĥ³ ≅ Ĥ¹` is
needed only if one insists on *deriving* surjectivity from `H³(G,K^×) = 1`, and (a) supplies
surjectivity directly.  So the missing piece for the fundamental exact sequence is the idele-class
long exact sequence plus invariant-map injectivity, both of which are ordinary work — not duality.

### (c) Poitou–Tate looks avoidable: Hochschild–Serre in degree two does the same job

Row 5 of §0.36 asks for `Ш²(k,A) ≅ Ш¹(k,A′)^∨`, but Schmidt–Wingberg only ever *use* the surjection
`Ĥ^{-2}(G, E(-1)) ↠ Ш²(k, E)` to kill a class `z ∈ Ш²(k, E(m,τ))` after applying `θ_a`, and Prop 6
(`Shafarevich/GenericCohomology.lean`) is what does the killing.  For that argument an **injection**
of `Ш²(k,E)` into a *finite-group* cohomology group of the right shape works just as well as the
surjection: Prop 6 kills the image, and injectivity then kills the class.  Write
`1 → G_K → G_k → G → 1` with `G = Gal(K/k)` the group already realised, `E` the layer, an
`𝔽_p[G]`-module of finite dimension, on which `G_K` acts trivially.

1. `z ∈ Ш²(k,E)` restricts to a locally trivial class over `K`, and `Ш²(K, E) = 0` because
   `E ≅ μ_p^r` as a `G_K`-module and the repository has `eq_one_of_mem_sha2` (row 3, §0.79).  So
   `z ∈ F¹ = ker(res)` for the Hochschild–Serre filtration.
2. Degree-two Hochschild–Serre gives `F¹/F² ↪ H¹(G, H¹(G_K, E))`, and `H¹(G_K,E)` is
   `Hom_cont(G_K, 𝔽_p) ⊗_{𝔽_p} E = E ⊗ T` with the diagonal `G`-action — exactly the shape
   `Layer ⊗ T` that Prop 6 consumes.
3. `T = Hom_cont(G_K, 𝔽_p)` is infinite dimensional, but that does not matter: a class in
   `H¹(G, E ⊗ T)` is represented by a cocycle on the *finite* group `G`, so it has finitely many
   values, each a finite sum of pure tensors; the `𝔽_p`-span `T₀` of the `G`-orbit of the finitely
   many `T`-components appearing is finite dimensional and `G`-stable, and the cocycle already takes
   its values in `E ⊗ T₀`.  So the class is inflated from `H¹(G, E ⊗ T₀)` with `T₀` finite
   dimensional, which is what Prop 6 requires.
4. Prop 6 with `c = 1`, `t = 1`, `H = G`, `f = id`, `T = T₀` kills the image of `z`; so after the
   shrink `z` lies in `F² = im(inf : H²(G,E) → H²(k,E))`.
5. Prop 6 again, with `c = 2`, `t = 1`, `H = G`, `f = id`, `T` the trivial one-dimensional
   representation, kills the class of `H²(G,E)` it comes from.  Hence `z = 0`.

Step 3 is what removes the gap that this section originally recorded.  The earlier plan was to make
`T` finite by inflating from `G_S = Gal(k_S/k)`, which needed `Ш²(k,A) = Ш²(k_S/k,A)` (NSW 9.1.x) —
a statement whose standard proof may itself use duality — and needed `H¹(K_S/K, ℤ/p)` finite.
Neither is required: **finite-dimensional approximation inside the coefficients does the same work,
because `G` is finite.**

It is worth being precise about what Prop 6 is, since the shape of the argument depends on it.
`exists_operatorHom_res_cohomology_eq_zero` is *not* a cohomological-triviality statement about the
layer; it is a counting statement — given `t` classes in `H^c(H, Layer_j ⊗ T)` with `H` finite and
`T` finite dimensional, a large enough shrink kills all `t` of them at once.  So the coefficients
must be finite dimensional and the family of classes finite, which is exactly what steps 3–5
arrange.

Required inputs, with verdicts:

| input | status |
| --- | --- |
| (C) degree-two Hochschild–Serre / transgression for a closed normal subgroup of finite index | **the remaining wall**; see (d) |
| `Ш²(K, E) = 0` for `E ≅ μ_p^r` over `K` | **have it** (`eq_one_of_mem_sha2`) |
| `H¹(G_K, E) ≅ Hom_cont(G_K,𝔽_p) ⊗ E` as `G`-modules | ordinary work |
| finite-dimensional approximation in the coefficients | elementary, step 3 above |
| Prop 6 with coefficients | **have it** (`exists_operatorHom_res_cohomology_eq_zero`) |
| naturality of the filtration under the shrink `θ_a` | ordinary work |

If this holds up, **row 5 and row 8 of the §0.36 table are not needed at all** and the critical path
for `GenericSplitEP` becomes degree-two Hochschild–Serre rather than Poitou–Tate.  Recorded as the
current best route, not yet as a proven reduction: the pieces above have been checked
mathematically but none of the new ones is formalised.

### (d) Transgression is available at the level of cochains

The repository already has a degree-two inflation–restriction theorem,
`mem_range_inflTwo_of_resTwo_eq_zero` (`GroupCohomology/InfResTwo.lean`), whose only use of the
blanket hypothesis "`H¹(N,A) = 0`" is inside `exists_twist_eq_one_of_mem_of_section`
(`GroupCohomology/InflationRestriction.lean`), at exactly one line:

```lean
choose T hT using fun σ : G =>
  hH1 (fun m : G => a (σ, σ⁻¹ * m * σ)) (isMulCocycle₁_conj_of_eq_one ha h1 σ)
```

That is, it is applied only to the family of conjugation 1-cocycles `n ↦ a (σ, σ⁻¹ n σ)`, one per
coset representative `σ` — which *is* the transgression datum.  Replacing the blanket hypothesis by
"these particular classes vanish in `H¹(N,A)`" therefore yields a **relative** degree-two
inflation–restriction theorem with no need to build the `G/N`-action on `H¹(N,A)`, the seven-term
sequence, or any spectral sequence.  Because `θ_a` transports the chosen cochains, naturality in the
module comes for free.  This is the cheapest available form of input (C), and it is a modification
of existing code rather than new infrastructure.

Step 2 of (c) needs slightly more than the relative theorem: it needs the transgression as a *map*
into `H¹(G/N, H¹(N,A))`, so that a class which is not inflated is sent to a nonzero target that
Prop 6 can then kill.  The cochain-level construction above supplies the underlying cochain
`σ ↦ [n ↦ a (σ, σ⁻¹ n σ)]`; what has to be added is that it is a 1-cocycle for the conjugation
action of `G/N` on `H¹(N,A)` and that its class does not depend on the twist used to normalise `a`.
Both are cochain computations of the same kind as the ones already in
`GroupCohomology/InflationRestriction.lean`, and the relative theorem is precisely the statement
that a vanishing transgression class means inflated.  The remaining, genuinely new ingredient is the
profinite bookkeeping: `G_k` is not a finite group, so the argument has to be run in the
repository's continuous-cochain framework rather than for abstract groups.

Two Lean notes.  `(s.gcd f : ℤ)` elaborates as `Finset.gcd s (fun b => (f b : ℤ))`, not as a cast of
the natural-number gcd; the cast has to be spelled `((s.gcd f : ℕ) : ℤ)`.  And `choose!` does not
strip the membership argument when the target type has no `Nonempty` instance, so a choice over
`p ∈ n.primeFactors` has to be pushed through `Finset.attach` rather than `Finset.image f`.

Build green at **9591 jobs**, zero warnings, zero errors; all four new theorems have axioms
`[propext, Classical.choice, Quot.sound]`.

---

## 0.85 Status (2026-09-02) — the relative inflation–restriction theorem, and the transgression as a one-cocycle of the quotient

Input (C) of §0.84(c) — degree-two Hochschild–Serre — is now proven for abstract groups, in the only
form the Shafarevich argument needs.  Two files changed.

**(a) `GroupCohomology/InflationRestriction.lean`: the blanket hypothesis is gone.**  The engine of
that file corrects a two-cocycle `a` by three successive twists.  Only the third consumed anything
about the first cohomology of `N`, through the single line

```lean
choose T hT using fun σ : G =>
  hH1 (fun m : G => a (σ, σ⁻¹ * m * σ)) (isMulCocycle₁_conj_of_eq_one ha h1 σ)
```

so the hypothesis `hH1 : H¹(N,M) = 0` was doing far more work than required: what is used is only
that each member of the family `x ↦ a (σ, σ⁻¹ x σ)` is a coboundary.  `exists_twist_eq_one_of_mem_of_section`
now takes exactly that,

```lean
(hTr : ∀ σ : G, ∃ t : M, ∀ x ∈ N, x • t / t = a (σ, σ⁻¹ * x * σ))
```

and the `choose` collapses to `choose T hT using hTr`.

That is still a pointwise condition, and what a vanishing transgression *class* gives is weaker: a
single one-cocycle `φ` of `N` with `a (σ, σ⁻¹ x σ) = σ • φ (σ⁻¹ x σ) / φ x` up to a coboundary, for
every `σ` at once.  The gap is closed by one further twist, `exists_twist_conj_eq_smul_div`: extend
`φ` to `G` by `u g = φ (g (s g)⁻¹)`, reading the decomposition of `g` along its coset, and twist by
`u`.  Two computations, both two lines, do it — `u (n y) = n • u y * φ n` for `n ∈ N`, which keeps
the twisted cocycle trivial at every pair whose first entry lies in `N`, and `u (x σ) = x • u σ * φ x`
for `x ∈ N`, which turns the transgression into `x ↦ x • (t · u σ) / (t · u σ)`.  No cocycle
hypothesis on `a` is needed for either.  Assembling gives

```lean
theorem exists_twist_inflated_of_transgression
    {a : G × G → M} (ha : IsMulCocycle₂ a)
    (hres : ∃ b : G → M, ∀ x ∈ N, ∀ y ∈ N, a (x, y) = x • b y / b (x * y) * b x)
    (htr : ∀ c : G × G → M, IsMulCocycle₂ c → (∀ n ∈ N, ∀ y : G, c (n, y) = 1) →
      ∃ φ : G → M, (∀ x ∈ N, ∀ y ∈ N, φ (x * y) = x • φ y * φ x) ∧
        ∀ σ : G, ∃ t : M, ∀ x ∈ N,
          c (σ, σ⁻¹ * x * σ) = σ • φ (σ⁻¹ * x * σ) / φ x * (x • t / t)) :
    ∃ u : G → M, (inflated) ∧ (fixed)
```

The transgression is asked to be a coboundary for every *normalised* cocycle rather than for `a`
itself, because the correction proceeds by twists; this is honest and costs nothing downstream,
since the vanishing will come from a statement about `H¹(G/N, Hom(N,E))` that applies to any
representative.  The old `exists_twist_inflated` is now a two-line corollary, taking `φ = 1`, so its
single caller (`InfResTwo.lean:226`) is untouched.

Also proven there: `transgression_mul`, the composition law

`a (στ, (στ)⁻¹ x στ) = σ • a (τ, τ⁻¹ (σ⁻¹ x σ) τ) · a (σ, σ⁻¹ x σ) · (x • a (σ,τ) / a (σ,τ))`,

from two applications of the cocycle identity plus `smul_apply_of_mem_left`.  The last factor is the
coboundary of `a (σ,τ)`, which is exactly why the transgression is a cocycle only modulo `B¹(N,M)`
in general.

**(b) `GroupCohomology/Transgression.lean` (new): the trivial-action case, where the transgression
is an honest one-cocycle of the quotient.**  This is the case of the Shafarevich embedding problem:
`N = G_K` acts trivially on the kernel `E`, because `K` splits it.  With `htriv : ∀ n ∈ N, ∀ m : M, n • m = m`
the picture collapses pleasantly.

* `transgression a σ x = a (σ, σ⁻¹ x σ)`, and `transgression_mul_mem` says it is *multiplicative* on
  `N`: the one-cocycle condition `f (xy) = x • f y · f x` loses its twist.
* `transgression_conj`: it is invariant under conjugation by `N`.  The reason is one line — a
  homomorphism into an abelian group kills conjugation — and it is the concrete form of "inner
  automorphisms act trivially on `H¹(N,M)`".
* `transgression_smul_left`: hence `transgression a (nσ) = transgression a σ` for `n ∈ N`, so the
  transgression is a function on `G/N`.
* `transgression_mul_left`: the coboundary factor of `transgression_mul` is `x • a(σ,τ) / a(σ,τ) = 1`,
  so the composition law becomes the exact one-cocycle identity
  `transgression a (στ) x = σ • transgression a τ (σ⁻¹ x σ) · transgression a σ x`
  for the action of `G` on `Hom (N, M)` translating source and target.

So the obstruction to a class being inflated is a class in `H¹(G/N, Hom(N,M))` — a cohomology group
of a *finite* group, no matter how enormous `N` is.  `exists_twist_inflated_of_transgression_trivial`
packages the criterion in that language.

**(c) What this leaves.**  Against the table of §0.84(c): input (C) is now **done for abstract
groups**.  What remains on that route is
1. the profinite version — the same statements for `G_k` with continuous cochains, which should be
   the existing `Profinite/InfRes.lean` machinery (`exists_comapH2_eq` already turns "constant on
   kernel cosets" into "inflated") plus smoothness of the three twisting cochains;
2. `H¹(G_K, E) ≅ Hom_cont(G_K, 𝔽_p) ⊗_{𝔽_p} E` as `Gal(K/k)`-modules, which is now visibly the same
   object as `Hom (N, M)` above;
3. the finite-dimensional approximation of §0.84(c) step 3;
4. Prop 6 applied to the resulting class, and naturality of the whole picture under the shrink `θ_a`.

Rows 5 and 8 of §0.36 (Poitou–Tate, Ш¹ duality) remain unneeded on this route.

One Lean note: `rw [← transgression_apply]` fails, because the reversed pattern
`?a (?σ, ?σ⁻¹ * ?x * ?σ)` has a metavariable in head position; the arguments have to be given
explicitly, `rw [← transgression_apply a σ (n⁻¹ * x * n)]`.

Build green at **9592 jobs**, zero warnings, zero errors; every new theorem has axioms among
`[propext, Classical.choice, Quot.sound]`.

---

## 0.86 Status (2026-09-02) — the relative inflation–restriction theorem, for continuous cochains

Item 1 of §0.85(c) is done.  `CFT/Profinite/Transgression.lean` proves

```lean
theorem exists_comapH2_eq_of_transgression (hsm : IsSmoothHom π) (hsurj : Function.Surjective π)
    (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a)
    {b : G → M} (hbs : IsSmooth₁ b)
    (hb : ∀ x ∈ π.ker, ∀ y ∈ π.ker, a (x, y) = x • b y / b (x * y) * b x)
    (htr : ∀ c : G × G → M, IsMulCocycle₂ c → IsSmooth₂ c →
      (∀ n ∈ π.ker, ∀ y : G, c (n, y) = 1) →
      ∃ φ : G → M, IsSmooth₁ φ ∧ (∀ x ∈ π.ker, ∀ y ∈ π.ker, φ (x * y) = φ x * φ y) ∧
        ∀ σ : G, ∀ x ∈ π.ker, transgression c σ x = σ • φ (σ⁻¹ * x * σ) / φ x) :
    ∃ x : SmoothH2 Q M, comapH2 π hπ hsm x = smoothH2Mk a ha has
```

for `π : G →* Q` a smooth surjection onto a discrete group, in the repository's continuous-cochain
framework (`SmoothH2`, `comapH2`).  Both trivialisations are asked to be smooth, and both hypotheses
come out smooth in the intended application: `b` from `Ш²(K,E) = 0` read at a finite level, and `φ`
from a class of `H¹(G, Hom_cont(G_K, E))`, whose cocycles are smooth by construction.

**(a) Why the smoothness cannot be recovered after the fact.**  `smoothH2Mk (twist a u) = smoothH2Mk a`
requires `IsSmooth₁ u`, not merely that `a` and `twist a u` are both smooth.  Suppose `∂u` is
`N₁`-bi-invariant.  Then for `n ∈ N₁`, `u (g n) = g • ψ n * u g` with `ψ x = u x / u 1`, and `ψ|N₁`
is a one-cocycle — a homomorphism when `N₁` acts trivially.  It need not vanish, and it cannot be
cancelled by multiplying `u` by a global one-cocycle, since `coboundary₂ w = 1` exactly when `w` is
a one-cocycle.  **So `∂u` smooth does not imply `u` smooth**, and each of the four corrections has to
be *built* smooth.

**(b) The correction is tracked, not repaired.**  Each of the four twisting cochains of
`InflationRestriction.lean` is defined by decomposing an element along its coset:
`u₁ = b` extended by `1`, `u₂ g = (a (g (s g)⁻¹, s g))⁻¹`, `u₃ g = φ (g (s g)⁻¹)`, and `u₄` likewise.
Consequently each is constant along any normal `N₀ ≤ N` acting trivially along which *its own data*
is constant — for `u₁` that is `b`, for `u₂` it is `a`, for `u₃` it is `φ`, and for `u₄` nothing
beyond triviality of the action.  The recurring computation is

`g n (s g)⁻¹ = (g (s g)⁻¹) · (s g · n · (s g)⁻¹)`, with the conjugate again in `N₀`,

together with `s (g n) = s g`.  Each of the four existence lemmas now carries that invariance as an
extra `∀ N₀, N₀ ≤ N → … → ∀ g n, u (g n) = u g` conjunct of its conclusion, so existing callers only
gained an `_` in their `obtain` pattern.  The new helper `twist_eq_of_mem` propagates constancy of a
two-cochain across a twist, which is what feeds the constancy of `a` forward from one correction to
the next.

**(c) The proof shrinks twice.**  This is forced.  The hypothesis `htr` is a ∀-statement over
normalised cocycles, and each instance returns its *own* `φ` with its own smoothness subgroup; so
the open normal subgroup cannot be fixed before `φ` is known, and the tempting alternative — descend
to a finite quotient `G/N'` first and quote the abstract theorem there — is circular.  Instead:

1. `R = N₁ ⊓ N₂ ⊓ K` where `N₁` is a smoothness subgroup for `a`, `N₂` one for `b`, and `K ≤ π.ker`
   is open normal (which exists: apply `hsm` to `⊥`, since `(⊥ : Subgroup Q).comap π = π.ker`, so
   `π.ker` itself need not be assumed open).  Along `R`, `u₁` and `u₂` are constant, hence so is
   `twist a (u₁ * u₂)`, which makes it smooth and lets `htr` be applied to it.
2. `R' = R ⊓ N₃` with `N₃` a smoothness subgroup for the `φ` just produced.  Along `R'` all four
   corrections are constant, so the total correction is smooth and
   `twist a (u₁ u₂ (u₃ u₄))` is constant on the cosets of `π.ker`, which `exists_comapH2_eq` turns
   into "inflated".

The last step passes from `twist` to `coboundary₂` through `eq_twist_mul_coboundary₂` and
`smoothH2Mk_eq_iff`.

**(d) What this leaves.**  Of §0.85(c): item 1 done; items 2–4 remain.  A note on the interface for
item 4: Prop 6 (`exists_operatorHom_res_cohomology_eq_zero`) lives in Mathlib's `Rep`/`groupCohomology`
framework, while everything above is in the repository's elementary multiplicative-cochain framework,
so the class in `H¹(G, Hom_cont(G_K, E))` has to be moved between the two.

Build green at **9593 jobs**, zero warnings, zero errors; the new theorem has axioms
`[propext, Classical.choice, Quot.sound]`.

---

## 0.87 Status (2026-09-02) — step 3 of §0.84(c) is circular, and Poitou–Tate is back

With the inflation–restriction machinery in hand the §0.84(c) route can be checked against the
actual statement of Prop 6, and **step 3 does not survive**.  §0.36(c) already recorded the failure
mode; §0.84(c) walked into it.

### (a) The refutation

`exists_genericShrink_res_cohomology_eq_zero` reads, in order of binders,

```lean
(T : Rep (ZMod ℓ) U) [Module.Finite (ZMod ℓ) T]
(hr : (j + 1) * (t * Nat.card H ^ c *
  Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T)) < r)
(x : Fin t → groupCohomology ((Action.res _ f).obj (genericLayerTensor U (r * n) S ℓ j T)) c)
```

so `T` is fixed **before** `r`, and `r` has to exceed a constant times `dim T`; only then is the
class `x`, which lives over `m = r · n`, supplied.  Step 3 chooses `T = T₀`, the `𝔽_p`-span of the
`G`-orbit of the `T`-components of a cocycle representing the transgression of `z`.  A one-cocycle
on `G` with values in `E(m) ⊗ T` has `#G` values, each with `dim E(m)` components, so

`dim T₀ ≤ #G² · dim E(m,τ)`,   and `m = r·n`.

The bound then demands `r > (j+1) · #G · dim E(n,τ) · #G² · dim E(rn,τ)`, and `dim E(m,τ)` grows
with `m` — already linearly for `j = 1`, since `Generic U m S` is relatively free on `m` orbits of
generators.  The requirement is circular; step 3 is exactly the "represent the class by boundedly
many elements, where *boundedly* means independently of `m`" trap of §0.36(c).

Everything else in §0.84(c) stands.  Step 1 (`Ш²(K,E) = 0`, so `z ∈ F¹`) is proven; step 2
(degree-two Hochschild–Serre) is proven, abstractly in §0.85 and for continuous cochains in §0.86;
step 5 (Prop 6 on `H²(G,E)` with `T` the trivial representation, which *is* fixed a priori) is fine.
What fails is only the passage `F¹ → F²`, and it fails for one reason: **`T` has to be finite
dimensional and known before `m`.**

### (b) What would repair it

The route is repaired by any statement that makes the coefficient module of the transgression a
priori finite dimensional.  Two candidates, both classical:

* `Ш²(k, E) ⊆ inf H²(k_S/k, E)` for a fixed finite `S ⊇ S_∞ ∪ S_p ∪ Ram(K/k)`.  Then
  `T = Hom_cont(Gal(K_S/K), 𝔽_p)` is finite dimensional and depends only on `K` and `S`, both fixed
  before the induction starts.  This is the "earlier plan" §0.84(c) discarded; it is back.
* Poitou–Tate, which is what Schmidt–Wingberg use, and which makes `T = 𝔽_p(-1)` — one dimensional.

So **rows 5 and 8 of the §0.36 table are again the wall**, and the honest reading is that §0.85 and
§0.86 built a genuinely useful piece of machinery (a relative, continuous-cochain Hochschild–Serre)
without removing the duality requirement.

### (c) A byproduct worth keeping: the transgression of a locally trivial class is locally a
coboundary

Let `a` be a two-cocycle of `G_k` normalised so that `a (n, y) = 1` for `n ∈ G_K` and all `y`, let
`D ≤ G_k` be a decomposition group, and suppose `a` restricted to `D` is the coboundary of a cochain
`c` on `D`.  Because `a` vanishes at every pair whose first entry lies in `G_K`, the restriction
`χ = c|_{D ∩ G_K}` is a homomorphism, and for `σ ∈ D`, `x ∈ D ∩ G_K`,

`transgression a σ x = σ • χ (σ⁻¹ x σ) / χ x`.

That is: the transgression class of an everywhere locally trivial class lies in the everywhere
locally trivial part of `H¹(G, Hom(G_K, E))`.  The computation is three lines of cochain algebra —
`∂c (x, σ) = a (x, σ) = 1` gives `c (x σ) = χ x · c σ`, and substituting into `∂c (σ, σ⁻¹ x σ)`
cancels `c σ` — and it is what any repair of the route will need, on either candidate above.  It is
also, in the duality language, precisely the assertion that the map `Ш² → H¹(G, H¹(G_K, E))` lands
in `Ш¹`, which is the group Poitou–Tate computes.

---

## 0.88 Status (2026-09-02) — `Ш¹` from the idele sequence: the lattice case is done, the `p`-torsion case is Poitou–Tate

§0.87(c) ends at the group `Ш¹(G, Hom_cont(G_K, E))`.  This section computes it, in the one case
where the existing class-formation machinery suffices, and pins down exactly what is missing in the
case the route actually needs.

### (a) The reduction that costs nothing

Kummer theory identifies the coefficient module.  With `μ_p ⊆ K` and `W := Hom(μ_p, E) = E(-1)`,

`Hom_cont(G_K, E) ≅ (K^×/K^{×p}) ⊗_{𝔽_p} W = K^× ⊗_ℤ W`   as `G = Gal(K/k)`-modules,

so the group of §0.87(c) is `Ш¹(G, K^× ⊗ W)`, the kernel of `Ĥ¹(G, K^×⊗W) → Ĥ¹(G, I_K⊗W)` — the
target being `⊕'_v Ĥ¹(G_w, K_w^×⊗W)` by Shapiro's lemma.

Now tensor the idele sequence `0 → K^× → I_K → C_K → 0` with any coefficient module `M` for which
it stays exact.  The long exact sequence of complete cohomology gives, **in every degree at once**,

`Ш^{i+1}(G, K^×⊗M) = im(δ : Ĥ^i(G, C_K⊗M) → Ĥ^{i+1}(G, K^×⊗M)) = coker(Ĥ^i(G, I_K⊗M) → Ĥ^i(G, C_K⊗M))`.

That is the whole trick: **the locally trivial classes of the units are a quotient of the cohomology
of the idele classes one degree lower**, and the idele class group is the module of a class
formation, so its cohomology is computable by Tate–Nakayama.  No duality is used.

### (b) The lattice case, in Lean

For `M = N` a `G`-lattice (flat over `ℤ`) the tensored sequence is exact because flatness is exactly
what preserves injectivity, and `tateNakayamaIdeleClass` gives `Ĥ^i(G, C_K⊗N) ≅ Ĥ^{i-2}(G, N)`.
`CFT/Units/IdeleTorusSha.lean` assembles this:

```lean
theorem range_shaTorusMap (n : ℤ) :
    LinearMap.range (shaTorusMap α hα N hN n)
      = LinearMap.ker (tateMap (tensorHomLeft N (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom
```

where `shaTorusMap α hα N hN n : Ĥ^n(G, N) →ₗ Ĥ^{n+3}(G, K^×⊗N)` is Tate–Nakayama followed by the
connecting map.  In words: **the everywhere locally trivial part of `Ĥ^{n+3}(G, K^×⊗N)` is exactly
the image of `Ĥ^n(G, N)`.**  Sorry- and axiom-free.

The hypotheses `α`, `hα` — a class of order divisible by `#G` in `Ĥ²(G, C_K)` — are *not* an extra
assumption: §0.82(b) closed the fundamental-class brick, so `baseFundamentalClass k K` exists for
every Galois extension of number fields (`CFT/Units/BaseTate.lean`).  Instantiating gives the
unconditional form, also in `IdeleTorusSha.lean`:

```lean
theorem range_baseShaTorusMap (n : ℤ) :
    LinearMap.range (baseShaTorusMap N hN n)
      = LinearMap.ker (tateMap (tensorHomLeft N (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom

theorem range_baseShaTorusMap_one :
    LinearMap.range (baseShaTorusMap N hN (-2))
      = LinearMap.ker (tateMap (tensorHomLeft N (globalUnitsToIdele k K)) 1).hom
```

so for **any** Galois extension of number fields and **any** `ℤ`-flat `N : Rep ℤ Gal(K/k)`, the
everywhere locally trivial classes in `Ĥ¹(G, K^×⊗N)` are a quotient of `Ĥ^{-2}(G, N) = H_1(G, N)`.

Sanity checks.  `n = -2` gives `Ш¹(G, K^×⊗N)` as a quotient of `Ĥ^{-2}(G,N) = H_1(G,N)`, which is
finite while `H¹(G, K^×⊗N)` need not be.  For `N = ℤ` trivial the source is `G^ab` and the target is
`Ш¹(G, K^×) ⊆ H¹(G,K^×) = 0` (Hilbert 90) — consistent, not tight.  For `N = ℤ[G]` both sides
vanish.  And the statement is the exact dual of the classical `Ш¹(k,T) ≅ Ш²(k, X̂)^∨` of Ono and
Sansuc: `Ĥ^{-2}(G,N) ≅ Ĥ¹(G, Hom(N,ℚ/ℤ))^∨ ≅ Ĥ²(G, X̂)^∨` for `X̂ = Hom(N,ℤ)` the character lattice,
since `X̂⊗ℚ` is cohomologically trivial.  So the brick is the torsion-free half of global duality for
tori, obtained from the class formation alone.

### (c) The `p`-torsion case: where the content really is

The route needs `M = W`, which is `p`-torsion, not a lattice.  Two things have to be checked.

**Exactness of the tensored sequence** — this one is free.  `Tor_1(C_K, W) = C_K[p] ⊗ W`, and the
connecting map `C_K[p] → K^×/K^{×p}` is zero: the snake of `0 → K^× → I_K → C_K → 0` gives

`0 → μ_p(K) → I_K[p] → C_K[p] → K^×/K^{×p} → I_K/I_K^p`,

and `I_K[p] = ∏_w μ_p(K_w) = ∏_w μ_p` (roots of unity are units at every place), so the image of
`C_K[p]` in `K^×/K^{×p}` lies in `Ш¹(K, μ_p)`, which vanishes by Grunwald–Wang — in the repository,
`exists_pow_eq_of_forall_localPow_outside_of_prime` (`CFT/GrunwaldWang.lean`), prime exponent, no
roots-of-unity hypothesis, so the `p = 2` special case never arises.  **So `0 → K^×⊗W → I_K⊗W →
C_K⊗W → 0` is exact and the reduction of (a) applies verbatim.**

**Tate–Nakayama with `p`-torsion coefficients** — this one is not free, and it is the whole
difficulty.  The theorem in its honest form computes `Ĥ^n(G, M ⊗^L C_K)`, and for `M` with torsion
the derived tensor product has `H_1 = Tor_1(C_K, M) = C_K[p]⊗M`, so the naive statement acquires an
error term measured by `Ĥ^*(G, C_K[p] ⊗ W)`.  The repository already has the `p`-torsion
Tate–Nakayama gated on exactly one hypothesis:

```lean
def tateNakayamaPTorsionEquiv (A : Rep ℤ G) (α : tateModule A 2) (M : Rep ℤ G)
    (hM : ∀ v : ↥M.V, p • v = 0)
    (hE : ∀ P : Sylow p G, Limits.IsZero (groupCohomology (resObj (P : Subgroup G)
      (modNsmul (cocycleObj (shiftObj A) (tateTwoCocycle A α)) p)) 1)) (n : ℤ) :
    tateModule M n ≃ₗ[ℤ] tateModule (tensorObj A M) (n + 1 + 1)
```

(`CFT/TateCohomology/TensorPTorsion.lean`).  Unwinding the dimension shift for `A = C_K`, the
hypothesis `hE` is the vanishing of a Tate group of `C_K[p]` over each Sylow subgroup — and that
group does **not** vanish in general: `Ĥ²(P, I_K[p]) = ∏_{orbits} Ĥ²(P_w, μ_p)` maps into it and is
nonzero as soon as some decomposition group is nontrivial.  This is not a defect of the Lean
statement; it is the reason Poitou–Tate is a theorem about `Ш` and not a corollary of the class
formation.  **The `p`-torsion case of (a) is Poitou–Tate.**

This is the same obstruction §0.29(ii) hit from the other direction: presenting `E(-1)` by a lattice
and chasing the resulting sequence stalled on `Ĥ²(G, C_K[p]⊗E(-1)) = ∏_𝔭 Ĥ²(G_𝔭, E) ≠ 0`, and
§0.29(iii) already concluded "the Claim really is Poitou–Tate".  What (b) adds is that the *other*
half — everything torsion-free — is now a theorem in the repository rather than a plan, so the
`C_K[p]` term is the entire remaining content, not one difficulty among several.

### (d) What this changes

Row 5 of the §0.36 table stands, but its shape is now precise rather than a slogan:

* The **torsion-free** half of global duality for tori is *done*, from the class formation, with no
  duality input at all and no hypothesis on the extension (`range_baseShaTorusMap`).
* The **`p`-torsion** half reduces, by (c), to controlling `Ĥ^*(G, C_K[p] ⊗ W)` — equivalently, to
  the derived correction in Tate–Nakayama.  That is a single, sharply stated object, and it is the
  first place where a genuine Poitou–Tate input is unavoidable.
* Grunwald–Wang has now found its first real use downstream: it is what makes the tensored idele
  sequence exact for `p`-torsion coefficients.

Bricks available for the next step, all present and sorry-free: `ideleClassShortComplex_shortExact`,
`tensorSeq_shortExact`, `tateδ`/`tateExact_δ_map`, `tateNakayamaIdeleClass`,
`tateNakayamaPTorsionEquiv`, `isZero_tateModule_tensorObj_of_nsmul`, and the Grunwald–Wang power
theorem.  What is *not* present: the Kummer identification
`Hom_cont(G_K,E) ≅ (K^×/K^{×p}) ⊗ Hom(μ_p,E)` as `G`-modules, Shapiro for `I_K ⊗ M`, and any handle
on `C_K[p]` as a `G`-module.

---

## 0.89 Status (2026-09-03) — the Cartier dual and its pairing; row 6 was already done; and `C_K[p]` is a quotient of a coinduced module

### (a) Two new modules

`CFT/PoitouTate/Dual.lean` and `CFT/PoitouTate/CupDual.lean`, both sorry- and axiom-free.

* `CartierDual A μ` is `A →* μ` with the action `(g • f) a = g • f (g⁻¹ • a)`, a `CommGroup` with a
  `MulDistribMulAction`.  `evalPairing A μ : A →* CartierDual A μ →* μ` is evaluation and
  `evalPairing_smul` is its equivariance; `toDoubleDual` is the comparison with the double dual.
  `IsSmoothAction G (CartierDual A μ)` is an instance: an open normal subgroup acting trivially on
  `A` and on `μ` acts trivially on `A →* μ`.  So the dual of a smooth module is a smooth module and
  `SmoothH1 G (CartierDual A μ)` is defined.
* `cupDual A μ : SmoothH1 G A →* SmoothH1 G (CartierDual A μ) →* SmoothH2 G μ` is
  `cupSmoothH1 (evalPairing A μ)`.  It commutes with restriction (`resH2_cupDual`) and carries the
  everywhere locally trivial classes of either factor into `sha2` (`cupDual_mem_sha2_left/right`).
* `dualSymbolUnits A ιμ hιμ` pushes the pairing into `Ωˣ` along an equivariant `ιμ : μ →* Ωˣ`, and
  `totalInvariant_smoothBrauerHom_dualSymbolUnits` is **the product formula: the local invariants
  of the pairing of a class with a dual class multiply to one over all places of a number field.**
  There is a finite-set form with the same proof shape as the power residue symbol's.

In Poitou–Tate terms this is the *easy* half of the central exactness: the image of `H¹(k,A)` in
the restricted product of the `H¹(k_v,A)` is contained in the annihilator of the image of
`H¹(k,A^D)`.  The hard half is the reverse inclusion.

### (b) Row 6 of the §0.36 table is stale: it is done

The row reads "the repo has the *quadratic* symbol over `ℚ`".  That predates
`CFT/Profinite/Symbol.lean`, which builds `kummerSymbol h Φ : kˣ →* kˣ →* SmoothH2 Gal(Ω/k) M` for
any Kummer data of any exponent `n` over any base, together with `resH2_kummerSymbol` and
`kummerSymbolUnits`, and `CFT/Brauer/CyclicProduct.lean`, which proves
`totalInvariant_smoothBrauerHom_kummerSymbolUnits` and
`prod_placeInvariant_mul_prod_infinitePlaceInvariant_kummerSymbolUnits`.  That is the `p`-th power
symbol over a number field and its product formula.  **Row 6 should be marked DONE.**

### (c) `C_K[p]` is a quotient of a coinduced module, and its Tate cohomology is local

§0.88(c) named "any handle on `C_K[p]` as a `G`-module" as missing.  The handle is already in the
sequence §0.88(c) writes down.  With `μ_p ⊆ K`,

`0 → μ_p(K) → I_K[p] → C_K[p] → Ш¹(K, μ_p) = 0`,

the last vanishing by Grunwald–Wang, so

**`C_K[p] ≅ (∏_w μ_p) / μ_p(K)`**, the product over *all* places `w` of `K`.

Now `∏_w μ_p` is not an opaque module.  Group the places over the places of `k`: for each place `v`
of `k` the set `{w | v}` is one `G`-orbit, and `∏_{w|v} μ_p` is the module of sections of a
constant family over that orbit.  That is exactly the situation of `CFT/Tate/FamilyCoind.lean`
(2026-09-02): **the sections of a family over a transitive orbit are coinduced from the stabiliser
of a base point**, so by Shapiro

`Ĥ^n(G, ∏_{w|v} μ_p) ≅ Ĥ^n(D_w, μ_p)` for every `n : ℤ`,

`D_w` the decomposition group.  `CFT/Units/AdicOrbitTate.lean` (2026-09-02/03) already instantiates
this for the units of the completions at the finite places and at the infinite ones,
`adicOrbitTateEquiv` and `infiniteOrbitTateEquiv`, with no cyclicity hypothesis.

So the error term of `p`-torsion Tate–Nakayama, `Ĥ^*(G, C_K[p] ⊗ W)`, is computed by the long exact
sequence of `0 → μ_p(K) ⊗ W → (∏_w μ_p) ⊗ W → C_K[p] ⊗ W → 0` — exact because everything in sight
is an `𝔽_p`-vector space — out of `Ĥ^*(G, μ_p ⊗ W)` and a product of **local** groups
`Ĥ^*(D_w, μ_p ⊗ W)`.  That is the shape of the Poitou–Tate sequence, and it is reachable with the
bricks in the repository rather than with a fresh duality theory.

### (d) What this makes the next steps

1. **Tate cohomology of a finite group commutes with products.**  True for arbitrary index sets
   (products are exact in `Ab` and the complete resolution is a fixed complex of finitely generated
   free modules), absent from the repository, and needed to turn the per-place Shapiro statement
   into a statement about `I_K[p]`.  This is the one genuinely missing general lemma and it is
   small.
2. **`I_K[p] = ∏_w μ_p` as a `G`-module**, in the repository's idele language, and the resulting
   `Ĥ^*(G, I_K[p] ⊗ W) ≅ ∏_v Ĥ^*(D_w, μ_p ⊗ W)`.
3. **`C_K[p] ≅ I_K[p]/μ_p(K)`** from the snake sequence and `Ш¹(K,μ_p) = 0`
   (`exists_pow_eq_of_forall_localPow_outside_of_prime`).
4. The long exact sequence, and then the error term in `tateNakayamaPTorsionEquiv`.

Row 5 is then a computation rather than a wall.  Row 8, the eight-term sequence itself, remains a
separate and larger object; nothing here shortens it, but nothing in rows 5 and 9 evidently needs
it in full once (1)–(4) are in place.

---

## 0.90 Status (2026-09-04) — §0.89(d) items 1–4 are all landed, and row 5 is now one sharp statement

### (a) The four next steps of §0.89(d) are done

All four are in the repository, sorry- and axiom-free.  Full build green at 9636 jobs.

1. **Tate cohomology commutes with products** — `CFT/TateCohomology/Product.lean`
   (`tatePiEquiv`, `isZero_tateModule_piRep`), and its tensored refinement
   `CFT/TateCohomology/TensorPi.lean` (`tensorSectionsIso`, `isZero_tateModule_tensorObj_piRep`).
   The tensored form needs the coefficients to be of finite rank over the prime field, because `⊗`
   does *not* commute with infinite products; the bridging lemma is
   `nsmul_eq_zero_of_equivPi : (W ≃+ (Fin d → ZMod p)) → ∀ x, p • x = 0`.
2. **`I_K[p] = ∏_w μ_p` and the local decomposition** — `CFT/Tate/FamilyTensorOrbit.lean`
   (`tateTensorOrbitsEquiv`, `tateTensorTorsionEquiv`), `CFT/TateCohomology/TensorPair.lean`,
   `CFT/Units/IdeleTorsionTensor.lean` (`ideleTorsionTensorTateEquiv`,
   `isZero_tateModule_tensor_ideleTorsion`).  So
   `Ĥ^n(G, I_K[p] ⊗ W) ≅ ∏_v Ĥ^n(D_w, μ_p ⊗ W)`, one factor per place of the base field.
3. **`C_K[p] ≅ I_K[p]/μ_p(K)`** — already present as
   `ideleClassTorsionShortComplex_shortExact` (`CFT/Units/IdeleClassTorsionSES.lean`), which is
   exactly the snake sequence with `Ш¹(K,μ_p) = 0` folded in.
4. **The long exact sequence** — `CFT/Units/IdeleClassTorsionLocal.lean` (2026-09-04):
   `ker_tateδ_tensor_ideleClassTorsion` and `exists_localTorsion_tateMap_eq`, so a class of
   `Ĥ^n(G, C_K[p] ⊗ W)` is the image of a family of local classes exactly when the connecting map
   into `Ĥ^{n+1}(G, μ_p(K) ⊗ W)` kills it, and `exists_localTorsion_tateMap_eq_of_isZero` when that
   target vanishes.  **The error term of `tateNakayamaPTorsionEquiv` is now a global group presented
   by local ones.**

Two further bricks landed on top:

* `CFT/Units/IdeleTorusShaLocal.lean` reads the obstruction of §0.88(c) one place at a time.  The
  local module is killed by `p` and the complete cohomology of a decomposition group is killed by
  its order, so **a place with `p ∤ #D_w` contributes nothing**
  (`isZero_tateModule_tensor_adicTorsion_of_coprime`, and the archimedean twin).  A decomposition
  group at an archimedean place has order one or two
  (`NumberField.InfinitePlace.nat_card_stabilizer_eq_one_or_two`), so **for odd `p` the archimedean
  places drop out of the criterion entirely** (`range_shaTorusPTorsionMap_of_isZero_adic`), leaving
  a condition at the finite places and one on `Ĥ^{n+5}(G, μ_p(K) ⊗ W)`.
* `CFT/TateCohomology/TensorPTorsion.lean` gained `isZero_tateModule_tensorObj_of_coprime` and its
  primed twin: a tensor product one of whose factors is killed by a number prime to `#G` has no
  complete cohomology.

### (b) Row 5, sharply

The sufficient condition of §0.88(c) — "the obstruction group vanishes" — is *false* in general, and
saying so is not enough.  `CFT/Units/IdeleTorusShaSharp.lean` replaces it by a necessary **and**
sufficient one.  The unconditional statement is `range_shaTorusPTorsionMap`:

`im(shaTorusPTorsionMap) = δ(ker obs)`,  while  `Ш = δ(⊤)`,

with `obs = baseTateNakayamaPTorsionRight : Ĥ^{n+2}(G, C_K⊗W) → Ĥ^{n+4}(G, C_K[p]⊗W)`.  A map's
image of a submodule is all of its image exactly when the submodule and the kernel span
(`map_eq_range_iff_sup_ker_eq_top`), and `ker δ` is what comes from the ideles
(`ker_tateδ_tensor_ideleClass`).  Hence

```lean
theorem range_shaTorusPTorsionMap_eq_iff' (n : ℤ) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
        = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K))
          (n + 1 + 1 + 1)).hom ↔
      Submodule.map (baseTateNakayamaPTorsionRight k K W hW n)
          (LinearMap.range (tateMap (tensorHomLeft W (ideleToIdeleClass k K)) (n + 1 + 1)).hom)
        = LinearMap.range (baseTateNakayamaPTorsionRight k K W hW n)
```

In words: **the everywhere locally trivial classes of `K^× ⊗ W` are exactly the image of
`Ĥ^n(G, W)` if and only if the obstruction of Tate and Nakayama takes no value on the idele classes
that it does not already take on the ideles.**  The units and `Ш` have been eliminated; what is left
is a statement about the obstruction and the places, which is the shape any duality input has to
take.

### (c) What is still missing, and what is unexpectedly present

Missing, for row 5:

* The comparison of the *global* Tate–Nakayama obstruction with the *local* ones — i.e. that the
  global fundamental class restricts to the local fundamental classes, giving a commuting square
  between `obs` and the per-place error maps.  With (a)4 and (b) in place this is the only step
  between the criterion and a theorem, and it is where the sum-of-invariants (reciprocity) enters.
* The Kummer identification `Hom_cont(G_K, E) ≅ (K^×/K^{×p}) ⊗ Hom(μ_p, E)` as `G`-modules
  (§0.88(c) already flagged this), which is what connects all of the `K^×⊗W` work to `Ш²(k,E)`.

Present, and worth remembering because it removes a large chunk of what "Poitou–Tate" usually costs:

* **Tate duality for a finite group in every degree, for `p`-torsion coefficients**, is already a
  theorem here — `Tate.tateDualEquiv` in `CFT/TateCohomology/DualityShift.lean`:
  `Ĥ^n(G, Hom(A,C)) ≅ Hom(Ĥ^{-n-1}(G,A), C)`.  So the *formal* half of local duality is done; only
  the identification of the local coefficient dual with the class formation's `Hom(M, K_w^×)` is
  not.  If `μ_p ⊆ k` — which the Shafarevich induction can arrange — the dual has trivial action and
  the identification is immediate.
* The product formula for the `p`-th power symbol and for the Cartier-dual pairing
  (`totalInvariant_smoothBrauerHom_kummerSymbolUnits`,
  `totalInvariant_smoothBrauerHom_dualSymbolUnits`), which is the global input.

So the remaining content of row 5 is *one* comparison square, not a duality theory.

---

## 0.91 Status (2026-09-04, later) — coefficient naturality, the free presentation, and the one structural gap that blocks every remaining route into row 5

### (a) What landed

Four commits, all sorry- and axiom-free.

* `b343cb0` — cyclic periodicity of complete cohomology (`CFT/TateCohomology/Cyclic.lean`).
* `38e1066` — the comparison of Tate and Nakayama is **natural in the representation**
  (`CFT/TateCohomology/NakayamaNatural.lean`).
* `4e9aad0` — the comparison of Tate and Nakayama is **natural in the coefficients**
  (`CFT/TateCohomology/NakayamaCoeff.lean`).  The payoff lemma is
  `range_tateMap_tensorHomRight_le`: if the comparison is onto for coefficients `M`, then
  everything a map `ψ : M ⟶ N` induces two degrees higher is already a value of the comparison
  for `N`.
* `3a797d8` — **the free presentation** (`CFT/TateCohomology/FreePresentation.lean`) and what it
  produces for the idele class group (`CFT/Units/BaseTateCoeff.lean`).  `freeRep W` is the free
  module on the *elements* of `W` with the group permuting the generators, `freeCounit W` reads a
  formal combination as the combination itself; `flat_freeRep` and `freeCounit_surjective` present
  every representation by a flat one.

Two facts worth keeping from `BaseTateCoeff.lean`:

* `⇑(baseTateNakayamaEquiv k K M hM n) = tateNakayamaTwoMap (ideleClassRep k K)
  (baseFundamentalClass k K) M n` is provable by **plain `rfl`** (`coe_baseTateNakayamaEquiv`), so
  the comparison is onto whenever the coefficients are flat over `ℤ`
  (`surjective_baseTateNakayamaTwoMap`).
* Hence `range_shaTorusPTorsionMap_of_free`: **row 5 holds for `W` as soon as the free presentation
  and the ideles together span `Ĥ^{n+2}(G, C_K ⊗ W)`.**  No Tate–Nakayama obstruction appears in
  that statement at all.

A fifth brick landed with this section: `CFT/TateCohomology/SylowSurjective.lean`, the companion of
`SylowInjective.lean`.  Writing `1 = u·[G:H] + v·m` with `m` killing a class exhibits the class as
`cor(u · res x)`, so `mem_range_tateCor_of_coprime`; coefficients killed by `m` have complete
cohomology killed by `m` (`nsmul_eq_zero_tateModule_of_nsmul`, from `tateMap_nsmul_id_apply`); so
**corestriction from a Sylow subgroup is onto the complete cohomology of coefficients killed by a
power of that prime** (`surjective_tateCor_sylow`).

### (b) Row 5 restated, and why the free presentation is a reformulation and not a closure

`exact_baseTateNakayamaPTorsionRight` says `ker obs = range TN`.  Combined with §0.90(b):

> **row 5 for `W` ⟺ `range ι_* ⊔ range TN = ⊤` in `Ĥ^{n+2}(G, C_K ⊗ W)`**,

where `ι_*` is induced by `I_K ↠ C_K` and `TN` is the Tate–Nakayama comparison.  Two things were
settled about this:

1. **An idelic fundamental class is a dead end.**  If one had a class `α_I ∈ Ĥ²(G, I_K)` inducing
   an isomorphism in the Tate–Nakayama style, `range ι_*` would already be everything, which forces
   `Ш = 0` for *every* coefficient module — false.  So the extra generators cannot come from
   repeating the class-formation argument on the ideles.
2. **The free presentation restates the problem.**  With `π : W₀ ↠ W`, `W₀` free over `ℤ`,
   `range TN ⊇ range (1 ⊗ π)_*`, so `range (1⊗π)_* ⊔ range ι_* = ⊤` is *sufficient*.  Chasing it
   through δ-naturality, that condition is equivalent to the surjectivity
   `Ш^{n+3}(G, K^× ⊗ W₀) ↠ Ш^{n+3}(G, K^× ⊗ W)`, and the cokernel is controlled by
   `0 → Tor₁(C_K, W) → C_K ⊗ R → C_K ⊗ W₀ → C_K ⊗ W → 0`, which lands back on
   `Ĥ^*(G, C_K[p] ⊗ W)` — the group §0.90(c) already names.  So the presentation buys a cleaner
   statement, not a proof.

### (c) The structural gap: `tateRes` and `tateCor` are not known to commute with `tateδ`

`tateRes` and `tateCor` (`CFT/TateCohomology/Restrict.lean`) are defined by **recursion on the
degree** through `resShiftEquiv`/`resCoshiftEquiv`, with `res0`/`resm1` (resp. `cor0`/`corm1`) as
base cases.  `tateModule` and `tateδ` (`Graded.lean:64`, `Graded.lean:120`) are likewise glued from
four different Mathlib constructions (`H0`, `groupCohomology`, `Hm1`, `groupHomology`; and
`H0toH1`, `groupCohomology.δ`, `deltaMid`, `H1toHm1`, `groupHomology.δ`).

The repository has **no** lemma saying that `tateRes` (or `tateCor`) commutes with `tateδ` of a
general short exact sequence.  What exists is `tateShiftEquiv_naturality`
(`ShiftNatural.lean:133`), which is naturality in the *representation map*, and
`tateδ_naturality_apply` (`DeltaNatural.lean:195`), naturality of `tateδ` in a map of short exact
sequences.  Neither gives the required square, and proving it needs

* a 3×3 lemma — the connecting map of the rows and the connecting map of the shifting columns
  commute up to sign — for which the repository has no bicomplex, and
* explicit cochain base cases in degrees `0` and `-1`, where the gluing happens.

This one missing square is what blocks, simultaneously:

1. the **local–global comparison** of §0.90(c) item 1 (the global fundamental class restricting to
   the local ones is a statement in degree two, but comparing `obs` with the per-place error maps
   needs res–δ in *every* degree);
2. the **Sylow reduction** of the criterion in (b): the reduction needs
   `cor ∘ TN^P = TN_G ∘ cor`, i.e. corestriction compatible with the two connecting maps hidden in
   `tateNakayamaTwoMap`.  `SylowSurjective.lean` supplies the *other* half (`cor` from a Sylow
   subgroup is onto), so this is the only obstacle;
3. Poitou–Tate in any form that mixes restriction with dimension shifting.

### (d) A near-miss: `Ш²(k, μ_p) = 0` over an arbitrary base

Row 3 (`eq_one_of_mem_sha2`, `CFT/Units/HasseTwoDecomposition.lean:533`) needs a primitive `n`-th
root **in the base field** and a trivial action.  `eq_one_of_mem_sha2_of_isPrimitiveRoot_intermediate`
(`CFT/Units/DecompositionRestrict.lean:172`) already removes that over an intermediate field `K`
containing the roots of unity, together with `decompositionSubgroups_le_galRestrictScalarsHom` and
`comapH2_mem_sha2_decompositionSubgroups`.  The **only** missing step for an arbitrary base is:

> `resH2 : SmoothH2 G_k μ_p → SmoothH2 G_K μ_p` is injective on `p`-torsion when `[K:k]` is prime
> to `p`,

i.e. **corestriction/transfer in the smooth (profinite) layer**.  Three things were checked about
this, and all three are worth recording because each looks like it should work and does not:

* `CFT/GroupCohomology/InfResTwoInjective.lean` is about **inflation**, not restriction.
* `CFT/GroupCohomology/Corestriction.lean` *does* build `cor`, `res` and `res_comp_cor` in every
  degree for a discrete group, and `eq_zero_of_res_eq_zero_of_prime_pow` is exactly the statement
  wanted — **but its `res` is the Shapiro composite** `H^n(G,A) → H^n(G, Coind_S^G Res A) ≅
  H^n(S, Res A)`, not the honest cochain restriction `groupCohomology.map S.subtype (𝟙 _)`.
  `map_subtype_id_eq` reduces the identification of the two to
  `groupCohomology.coindIso.hom = groupCohomology.map S.subtype (counit)`, which Mathlib v4.28 does
  **not** state.  Until that is proved, `eq_zero_of_res_eq_zero_of_prime_pow` cannot be applied to
  a hypothesis about genuine restriction.
* `mem_range_inflTwo_of_resTwo_eq_zero` (`CFT/GroupCohomology/InfResTwo.lean:187`) *is* exactness of
  inflation–restriction in degree two — but it assumes `H¹(S, A) = 0`, and for `S = G_K`,
  `A = μ_p` that group is `K^×/(K^×)^p ≠ 0`.  The sequence one would need is the seven-term
  Hochschild–Serre, where `ker(res)` is squeezed between `H²(Q, A^S)` and `H¹(Q, H¹(S,A))`, both of
  which vanish here because `#Q` is prime to `p`.
* `CFT/Profinite/InfRes.lean`'s `exists_comapH2_eq` is only the "cocycle literally constant on the
  cosets of the kernel" version, not exactness.

Also recorded, because it removes one apparent route: the Kummer bridge
`CFT/Profinite/KummerTwo.lean` gives `coeffH2_injective` — `H²(G_k, μ_n) ↪ H²(G_k, Ω^×)` with **no**
hypothesis that `ζ_n ∈ k` — and `kummerH2Equiv` identifies the image with the `n`-torsion of
`H²(G_k, Ω^×)`.  This does **not** reduce the problem to Albert–Brauer–Hasse–Noether for `Ω^×`,
because `Br(k) → Br(K)` is not injective either; the transfer is needed on both sides.

**However**, this whole item is probably *not* on the critical path: the Shafarevich induction can
arrange `μ_p ⊆ k` (see §0.90(c)), and with that hypothesis row 3 is already the theorem needed.

### (e) Lean notes from these commits

* `include hW` in a section does **not** add `hW` to the signature of a `def` whose body does not
  mention it — `baseTateNakayamaPTorsionMap k K W n` takes four explicit arguments while
  `baseTateNakayamaPTorsionLeft k K W hW n` takes five.
* `rw` can fail on a goal whose function coercion goes through a `ModuleCat.of`-carrier instance
  that is defeq but not syntactically equal to the plain one (`Module k ↥(freeRep W).V` versus
  `Module k (↥W.V →₀ k)`).  Insert an explicit `show <plain form>` before the `rw`.
* `Module.Flat.of_free` is an instance in Mathlib, so `inferInstanceAs (Module.Flat k (α →₀ k))`
  works directly.
* `Rep.ofMulDistribMulAction` + `cocyclesOfIsMulCocycle₂` + `H2π_eq_zero_iff` +
  `isMulCoboundary₂_of_mem_coboundaries₂` is the additive ↔ multiplicative `H²` dictionary; the
  pattern to copy is `isMulCoboundary₂_pow_natCard` (`Corestriction.lean:280`).
* A full root build is now **9643 jobs**.

---

## 0.92 Status (2026-09-04, night) — §0.91(c) is **closed**: res and cor commute with `tateδ`, and the Sylow reduction of the row-5 criterion is a theorem

### (a) The θ-trick, and why no bicomplex was needed

§0.91(c) said the missing square needed "a 3×3 lemma … for which the repository has no bicomplex,
and explicit cochain base cases in degrees `0` and `-1`".  Both halves of that estimate were wrong.
The square follows from **dimension shifting alone**, provided the extension is split as a sequence
of modules — and the two defining sequences are.

The trick, in the direction of the shift.  Let `X : 0 → X₁ → X₂ → X₃ → 0` be a short exact sequence
of representations and suppose `r : X₂ → X₁` is a module retraction of `X.f` and `s : X₃ → X₂` a
module section of `X.g`.  Read an element of `X₂` along all of its translates and apply `r`:

```
retractMid r : X₂ → Ind(X₁),   (retractMid r x)(g) = r (ρ_{X₂}(g) x).
```

This *is* equivariant (the retraction is applied after the translation, so no equivariance of `r`
is used), it restores `coindEmb` on `X₁`, and modulo the translates of `X₁` its value depends only
on the image in `X₃`.  So it assembles into a map of short exact sequences `X ⟶ shiftSeq X₁` whose
first component is the **identity**, and `tateδ_eq_tateShiftEquiv` (already in `DeltaShift.lean`)
turns the connecting map into an induced map followed by `tateShiftEquiv`.  Dually, from a section
`s` alone, the trace `tr(f) = augMap (s ∘ f)` gives `coshiftSeq X₃ ⟶ X` with third component the
identity, and `tateδ_eq_tateCoshiftEquiv` turns the connecting map into `tateCoshiftEquiv` followed
by an induced map.

Restriction is a functor, so both comparisons survive passage to a subgroup with their identity
components intact; the two `resSeq` versions of those identities are `tateδ_res_eq_resShiftEquiv`
and `tateδ_res_eq_resCoshiftEquiv` (`RestrictSplit.lean`).

### (b) The degree analysis

`tateRes`/`tateCor` are defined by recursion: for `n ≥ 0` through `resShiftEquiv`, for `n ≤ −1`
through `resCoshiftEquiv`.  Gotcha **1094**: `tateResNat H (m+1) A` is *literally*
`resShiftEquiv ∘ tateResNat H m (shiftObj A) ∘ (tateShiftEquiv A m).symm`, so the res/shift square
commutes **definitionally** for `n ≥ 0`, and dually the res/coshift square for `n ≤ −2`.  Hence:

| degree | route |
| --- | --- |
| `n ≥ 0` | the shift θ-trick + `tateRes_tateShiftEquiv` (definitional) |
| `n = −1` | `RestrictDelta.lean`, the honest cochain computation, already present |
| `n ≤ −2` | the coshift θ-trick + `tateRes_tateCoshiftEquiv` (definitional) |

which is `tateRes_tateδ` / `tateCor_tateδ` in **every integer degree** for any module-split
extension.  Feeding the two defining sequences back in (they are module-split, `ShiftSplit.lean`)
removes the degree restriction from the identifications themselves:
`tateRes_tateShiftEquiv_int`, `tateCor_tateShiftEquiv_int`, `tateRes_tateCoshiftEquiv_int`,
`tateCor_tateCoshiftEquiv_int`.

Commit `a78bb26`, three new modules: `ShiftSplit.lean`, `DeltaRetract.lean`, `RestrictSplit.lean`.

### (c) Tate–Nakayama against restriction, and the Sylow reduction

`cocycleTensorSeq A b M` is a product as a sequence of modules — `X₁` is the first coordinate
(`LinearMap.fst`), `X₃` the second (`cocycleTensorInr`) — and, crucially,

```lean
resSeq H (cocycleTensorSeq S b M)
  = cocycleTensorSeq (resObj H S) (resCocycles₁ H S b) (resObj H M) := rfl
```

so `tateRes_tateδ` applies verbatim.  `tateNakayamaMap` is that connecting map followed by
`shiftTensorIso` and `tateShiftEquiv`, both compatible with res/cor, so (commit `fe915dd`,
`NakayamaRestrict.lean`)

> **`tateRes ∘ TN_G = TN_H ∘ tateRes` and `tateCor ∘ TN_H = TN_G ∘ tateCor`, in every integer
> degree**, where `TN_H := resTateNakayamaMap H A b M n` is built from the restricted cocycle.

Two consequences are packaged: `surjective_tateNakayamaMap_of_cor` and
`sup_range_eq_top_of_cor` (what `TN` and a second map reach together is everything as soon as it is
everything on a subgroup from which corestriction is onto).

Applied to the idele class group (commit `f208286`, `BaseTateCoeff.lean`), with `W` killed by `p`
so that `C_K ⊗ W` is too and `surjective_tateCor_sylow_of_prime` applies:

```lean
theorem range_shaTorusPTorsionMap_of_sylow (P : Sylow p Gal(K/k)) (n : ℤ)
    (h : LinearMap.range (resTateNakayamaTwoMap (P : Subgroup Gal(K/k)) (ideleClassRep k K)
          (baseFundamentalClass k K) W n)
        ⊔ LinearMap.range (tateMap (resHom (P : Subgroup Gal(K/k))
            (tensorHomLeft W (ideleToIdeleClass k K))) (n + 1 + 1)).hom = ⊤) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom
```

**Item 2 of §0.91(c) is therefore closed**: row 5 for `Gal(K|k)` reduces to row 5 read on a Sylow
`p`-subgroup, i.e. to an extension of `p`-power degree.

### (d) What item 1 of §0.91(c) actually needs, now that the square is available

Not the square.  `baseFundamentalClass k K` is produced by `.choose` from
`exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_base` and is characterised **only** by its
annihilator; nothing ties it to the invariant maps.  `isTateClassTwo_baseFundamentalClass` holds for
every subgroup, which is all Tate's theorem needs, but "the global class restricts to the local
classes" is a statement about invariants and cannot even be formulated against the present
definition.  So item 1 of §0.91(c) is really two steps:

1. give the fundamental class an **invariant-theoretic characterisation** (`inv_v ∘ res_{D_w}`
   computes `1/[K_w:k_v]`), which means rebuilding it out of `localInvariantHom` and the
   reciprocity law rather than choosing it; then
2. the comparison square, which the new res/δ machinery now supplies for free.

### (e) Lean notes

* **1109.** `rw [resHom_id] at h` fails on `tateMap (resHom H (𝟙 X.X₃)) n` when the implicit
  arguments are `A := (coshiftSeq X.X₃).X₃`, `B := X.X₃`: defeq but not syntactically equal, and
  `resHom_id`'s pattern needs `A = B` syntactically.  Prove a side lemma and combine with
  `congrArg`/`Eq.trans`, letting `exact` absorb the difference.
* **1110.** `exact calc <term>` puts the `calc` keyword at a large column and silently parses the
  later `_ = … := …` steps *outside* the block — the errors that result ("Missing cases",
  "left-hand side is true : Bool") point nowhere near the cause.  Use the bare `calc` **tactic** on
  its own line.
* **1113.** The subgroup machinery is already phrased with `resObj H (shiftObj_G A)`, never
  `shiftObj_H (resObj H A)`, so the feared `indRestrict`/`indExtend` bridge is not needed.
* **1114.** `resSeq_cocycleSeq`, `resObj_cocycleObj`, `resObj_tensorObj`, `resSeq_cocycleTensorSeq`
  are all `rfl`.
* **1115.** `ShortComplex.ShortExact` is `Prop`-valued, so two proofs of the short-exactness of the
  same complex give defeq `tateδ`s.
* **1102 (performance).** Pass the sequence explicitly as a named argument
  (`traceSubHom (X := cocycleTensorSeq A b M) …`) to avoid whnf blowups.
* A full root build is now **9651 jobs**.

---

## 0.93 Status (2026-09-04, late) — the comparison square is **landed**, and it proves the *opposite* of what §0.90(c) hoped

### (a) What landed

Two commits.

**`TateCohomology/RestrictShiftBridge.lean` + `TateCohomology/NakayamaSubgroup.lean`** (commit
`5c4d380`, 9669 jobs).  The comparison of Tate and Nakayama *defined on a subgroup by restricting
the ingredients built on the whole group* is the same map as the comparison the subgroup builds for
itself out of the restricted representation and the restricted class:

```lean
theorem resTateNakayamaTwoMap_eq (n : ℤ) :
    resTateNakayamaTwoMap H A α M n
      = tateNakayamaTwoMap (resObj H A) (tateRes H A 2 α) (resObj H M) n
```

The proof is the cohomologous-cocycle argument: the cocycle of the shift read on `H`, pushed along
`resShiftHom H A`, and the cocycle `H` chooses for `tateRes H A 2 α` have the same class in degree
one (`exists_resShiftHom_tateTwoCocycle`), so `tateδ_cocycleTensorSeq_naturality` carries one
connecting map to the other; the remaining compatibility (`resShiftHom_shiftTensorIso`) is on the
nose.

The consequence is the usable form.  If a representation `A'` **of the subgroup** maps to
`resObj H A` and carries a class `β : tateModule A' 2` to `tateRes H A 2 α`, then

```lean
theorem range_resTateNakayamaTwoMap_le (φ : A' ⟶ resObj H A) (β : tateModule A' 2)
    (hβ : tateMap φ 2 β = tateRes H A 2 α) (n : ℤ) :
    LinearMap.range (resTateNakayamaTwoMap H A α M n)
      ≤ LinearMap.range (tateMap (tensorHomLeft (resObj H M) φ) (n + 1 + 1)).hom
```

**`Units/DecompositionNakayama.lean`** (commit `7692bc8`, 9670 jobs) is the arithmetic instance:
`H := D_w = stabilizer Gal(K/k) w`, `A := ideleClassRep k K`, `α := baseFundamentalClass k K`,
`A' := decompositionUnitsRep k w`, `φ := decompositionPlaceIdeleClass k w`,
`β := localizedFundamentalClass k w`.  The hypothesis `hβ` is *exactly*
`map_localizedFundamentalClass k w` from `Units/DecompositionLocalization.lean` — no bridging lemma
was needed, because `tateMap φ 2` and `((groupCohomology.functor ℤ H 2).map φ).hom` are
definitionally equal (gotcha 1272).  Composing with `decompositionPlaceIdele k w` gives

```lean
theorem range_resTateNakayamaTwoMap_le_idele (M : Rep ℤ Gal(K/k)) (n : ℤ) :
    LinearMap.range (resTateNakayamaTwoMap (stabilizer Gal(K/k) w) (ideleClassRep k K)
        (baseFundamentalClass k K) M n)
      ≤ LinearMap.range (tateMap (resHom (stabilizer Gal(K/k) w)
          (tensorHomLeft M (ideleToIdeleClass k K))) (n + 1 + 1)).hom
```

So §0.92(d) is closed as originally scoped: step 1 by the localisation route
(`localizedFundamentalClass`, which needs no invariant-theoretic rebuild of the global class), step
2 by the res/δ square.

### (b) The negative result this proves — §0.90(c) was too optimistic

§0.90(c) said "the remaining content of row 5 is *one* comparison square, not a duality theory".
That is now **refuted by the square itself**.

The Sylow criterion `range_shaTorusPTorsionMap_of_sylow` (`Units/BaseTateCoeff.lean`) asks, for a
subgroup `S ≤ Gal(K|k)`,

```
range (TN restricted to S)  ⊔  range (ι_* restricted to S)  =  ⊤
```

in `Ĥ^{n+2}(S, C_K ⊗ W)`.  The new brick says that on `S = D_w` the **first** summand is contained
in the **second**:

```
range TN|_{D_w}  ≤  range ι_*|_{D_w}.
```

Hence on a decomposition group the sup *collapses* to `range ι_*|_{D_w}`, and demanding that it be
`⊤` is demanding `Ш = 0`.  A decomposition group therefore cannot discharge the criterion.  The
criterion genuinely wants a **Sylow** subgroup, and a Sylow `p`-subgroup of `Gal(K|k)` is not a
decomposition group.  There is no cheap substitution.

This is worth stating sharply because it kills the shortcut: the square is a *local* statement, and
row 5 is a *global* one.  The square says everything the obstruction sees at one place comes from
that place; it says nothing about how the places fit together.  What glues them is reciprocity, and
reciprocity in the form needed here **is** Poitou–Tate.

### (c) Where row 5 actually stands

Row 5 is `Ш²(k,A) ≅ Ш¹(k,A′)^∨`.  In the repo's idelic form it is (§0.90, gotcha 1076)

> `range ι_* ⊔ range TN = ⊤` in `Ĥ^{n+2}(G, C_K ⊗ W)`, `W` the `p`-torsion coefficient module.

Since `TensorTorsionError.lean` gives `ker obs = range TN` for the obstruction map
`obs = tateNakayamaPTorsionErrorRight`, this is equivalent to

> `obs (range ι_*) = range obs`,

which is a *restatement* of row 5, not a proof of it.  Genuinely new mathematical input is required.

Schmidt–Wingberg's "Claim" (SW Prop. 16 / Thm 14) is precisely: **a surjection
`Ĥ^{-2}(G, E(-1)) ↠ Ш²(k,E)`, natural in `E`.**  Four inputs go into it, of which the repo already
has three:

1. the Hasse principle `Ш¹(k,E′) ↪ H¹(G,E′)` — `Units/SplitNorm.lean`;
2. dualising — `Cartier`/`Dual` layer;
3. `H¹(G,M)^∨ ≅ Ĥ^{-2}(G,M^∨)` — `h1DualEquiv`/`h1TwistEquiv`;
4. **the surjection `Ш¹(k,E′)^∨ ↠ Ш²(k,E)`** — the hard direction of Poitou–Tate.  *Missing.*

### (d) Two candidate routes, and the choice

**Route 1 — Poitou–Tate proper, via the `p`-torsion half of `IdeleTorusSha`.**  The torsion-free
half is done (`IdeleTorusSha.lean`, `IdeleTorusShaLocal.lean`).  The `p`-torsion obstruction chain
is (gotcha 1280):

* `Tor₁(C_K, W) = C_K[p] ⊗ W`;
* `C_K[p] ≅ I_K[p] / μ_p(K)` (`ideleClassTorsionShortComplex_shortExact`);
* `Ĥ^*(G, I_K[p] ⊗ W) ≅ ∏_v Ĥ^*(D_w, μ_p(K_w) ⊗ W)` by Shapiro — and Shapiro works for *any*
  subgroup, so on a Sylow `P` the product runs over `P`-orbits of places with stabilisers
  `P ∩ D_w`.

This is where the new decomposition square *does* pay: it identifies the local factor of the
obstruction with the localised fundamental class at `w`, which is what the sum-of-invariants formula
is about.

**Route 2 — §0.87(b) repair candidate A.**  Prove `Ш²(k,E) ⊆ inf H²(k_S/k, E)` for a fixed finite
`S ⊇ S_∞ ∪ S_p ∪ Ram(K/k)`.  That makes the transgression coefficient module
`T = Hom_cont(Gal(K_S/K), 𝔽_p)` finite-dimensional *a priori*, which removes Poitou–Tate from SW's
step 2 entirely and dissolves the `T`-before-`r` circularity of §0.87(a).  The cost is a different
classical theorem (finiteness of the `S`-class group and `S`-units, plus the standard
`Ш` ⊆ `S`-ramified argument).

**Choice: Route 1.**  It is the route the repo is already instrumented for — every brick from
`DecompositionIdele` through `DecompositionLocalization` to `DecompositionNakayama` was built for
it, and it is the route the user's directive ("work on Poitou–Tate … make sure it feeds
appropriately into 5/6") names.  Route 2 is kept as the fallback if the sum-of-invariants step
stalls.

### (e) Next brick

Both routes need the **subgroup form of the obstruction ladder**: that the obstruction map on a
subgroup is the restriction of the global one, i.e. that

```
Ĥ^n(H,W) --TN_H--> Ĥ^{n+2}(H, C ⊗ W) --obs_H--> Ĥ^{n+4}(H, C[p] ⊗ W)
```

is the `tateRes` of the global ladder, with `ker obs_H = range TN_H`.  `TensorTorsionError.lean` is
already stated for an arbitrary finite group and an arbitrary Tate class, so the `H`-instance exists
by substitution (`A := resObj H C`, `α := tateRes H C 2 α`); what is missing is the *compatibility*
with `tateRes`, i.e. the commuting square between `obs_G` and `obs_H`.

### (f) Lean notes

* **1272 (verified).** `tateMap φ 2 β` and `((groupCohomology.functor ℤ H 2).map φ).hom β` are
  **definitionally equal**: Mathlib's `groupCohomology.functor n`
  (`RepresentationTheory/Homological/GroupCohomology/Functoriality.lean:483`) has
  `map φ := map (MonoidHom.id _) φ n`, matching `tateMap`'s `.ofNat (m+1)` branch.  So
  `map_localizedFundamentalClass k w` is accepted verbatim as a proof of the `tateMap`-phrased
  statement.
* **1273.** `tensorHomLeft_comp` (`TensorFunctor.lean:73`) is oriented
  `tensorHomLeft M Φ ≫ tensorHomLeft M Ψ = tensorHomLeft M (Φ ≫ Ψ)`, so pushing a composite
  *inside* needs `rw [← tensorHomLeft_comp]`.
* **1274.** `resHom H (tensorHomLeft M ψ) = tensorHomLeft (resObj H M) (resHom H ψ)` is `rfl`; it is
  now the named lemma `Tate.resHom_tensorHomLeft` in `NakayamaSubgroup.lean`.
* **1275.** To conclude `range (tateMap (f ≫ g) n).hom ≤ range (tateMap g n).hom`, use
  `rw [tateMap_comp, ModuleCat.hom_comp]; exact LinearMap.range_comp_le_range _ _`.  The direct
  `rintro _ ⟨x, rfl⟩; exact ⟨_, (tateMap_comp_apply _ _ _ x).symm⟩` fails with unsolved metavariables
  and a `ConcreteCategory.hom` vs `ModuleCat.Hom.hom` mismatch.
* **1276.** `lake build InverseGalois.CFT.Units.DecompositionNakayama` = **8652 jobs** (~47 s); the
  full root build with it is **9670 jobs**, 0 warnings, 0 errors.

---

## 0.94 Status (2026-09-04, night) — §0.93(e) is **closed**: the obstruction ladder over a subgroup, and row 5 as one equation about one map

### (a) What landed

The "next brick" of §0.93(e) is done, and it turned out not to need a commuting square at all.  The
subgroup instance of the four-term sequence is obtained by *substitution*, and the only thing that
had to be supplied was the hypothesis of `TensorTorsionError.lean` for the substituted data:

```lean
hT' : ∀ q : ℕ, q.Prime → ∀ Q : Sylow q ↥H,
  IsTateClassTwo (Q : Subgroup ↥H) (resObj H A) (tateRes H A 2 α)
```

The difficulty is that `Q : Subgroup ↥H` is a group of *pairs* — an element of `H` together with a
proof — whereas everything the class formation supplies is indexed by `Subgroup G`.  The repository
had no transitivity-of-restriction lemma.  Three of `IsTateClassTwo`'s fields were dispatched as
follows.

* Field 3 (`dvd_of_zsmul_eq_zero`) needs **no transport at all**: `dvd_of_zsmul_tateRes_eq_zero`
  applied twice.  Order of a class is not a cohomological statement.
* Field 1 (`isZero_one`) is transported along the isomorphism
  `Q ≃* Q.map H.subtype` (`Subgroup.equivMapOfInjective`, gotcha 1294) by a new degree-one analogue
  of `tateTwoCongr`.
* Field 2 (`exists_zsmul`) is *not* transported; it is re-derived from field 3 by
  `isTateClassTwo_of_card_le`, given finiteness and the count in degree two, both transported by
  `tateTwoCongr`.

The transport datum is free: `resObj Q (resObj H A)` and `(Action.res _ e).obj (resObj (Q.map
H.subtype) A)` are **the same representation on the nose**, so the comparison morphism is
`hom := ModuleCat.ofHom LinearMap.id`, `comm := fun _ => rfl`, and bijectivity is
`Function.bijective_id` (gotcha 1295).

Four files:

* `TateCohomology/GroupCongr.lean` (edited) — `tateOneCongr`, the degree-one analogue of
  `tateTwoCongr`.
* `TateCohomology/RestrictTrans.lean` (new) — `subgroupTransEquiv`, `resTransHom`,
  `resTransTateOne`, `resTransTateTwo`, and the payoff `isTateClassTwo_resObj_of_card`.
* `TateCohomology/NakayamaSubgroupError.lean` (new) — `isTateClassTwo_sylow_resObj`, the two maps
  `resTateNakayamaPTorsionErrorLeft`/`Right`, and the exactness statements
  `range_resTateNakayamaPTorsionErrorLeft`, `ker_resTateNakayamaPTorsionErrorRight`,
  `exact_resTateNakayamaPTorsionErrorLeft`, `exact_resTateNakayamaPTorsionErrorRight`.  Note the
  middle map is `resTateNakayamaTwoMap` — the *global* comparison read on `H` — via
  `resTateNakayamaTwoMap_eq`, so the ladder really is the restriction of the global one.
* `Units/BaseTateSylow.lean` (new) — the number-field instance:
  `resBaseTateNakayamaPTorsionRight`, `ker_resBaseTateNakayamaPTorsionRight`, and the two forms of
  the criterion, `range_shaTorusPTorsionMap_of_sylow_sup` and
  `range_shaTorusPTorsionMap_of_sylow_map`.

Commit `2ea3c58`; full root build **9675 jobs**, 0 warnings, 0 errors, 0 `.lean` sorries.

### (b) Row 5, as one equation

Combining with §0.92's Sylow reduction, the entire remaining content of row 5 is now:

> For `P` a Sylow `p`-subgroup of `G = Gal(K/k)`, with
> `obs_P := resBaseTateNakayamaPTorsionRight k K W hW P n`
> the obstruction map `Ĥ^{n+2}(P, C_K ⊗ W) → Ĥ^{n+4}(P, C_K[p] ⊗ W)`, and
> `ι_* : Ĥ^{n+2}(P, I_K ⊗ W) → Ĥ^{n+2}(P, C_K ⊗ W)`,
>
> ```
> obs_P (range ι_*) = range obs_P.
> ```

That is `range_shaTorusPTorsionMap_of_sylow_map`.  Everything else — the class formation, the
fundamental class, the counts on every subgroup, the four-term sequence, the Sylow reduction, the
subgroup ladder — is a theorem.  This is a statement about a **single linear map over a `p`-group**,
placed over a field `k' = K^P` over which `K/k'` has `p`-power degree.

### (c) Why this is the right shape for Route 1

Over a `p`-group the local input simplifies twice over.

* `C_K[p] ≅ I_K[p] / μ_p(K)` and `I_K[p] = ∏_w μ_p(K_w)`, so
  `Ĥ^*(P, I_K[p] ⊗ W) ≅ ∏_{P\text{-orbits } o} Ĥ^*(P ∩ D_w, μ_p(K_w) ⊗ W)` by Shapiro
  (`Tate.tateOrbitsEquiv`, gotcha 1291, plus the `AdicSOrbitTate` layer).
* `range obs_P` is therefore a subgroup of a *product of local groups*, and the assertion
  `obs_P (range ι_*) = range obs_P` says the local components that actually occur already occur on
  ideles.  Since `ι_*` is itself the product map, the equation is a **sum-of-invariants** statement:
  the obstruction of a class of idele classes is a vector of local invariants summing to zero, and
  every such vector is attained.

So the target object of the next brick is the identification of `Ĥ^{n+4}(P, C_K[p] ⊗ W)` with (a
quotient of) `∏_o Ĥ^*(P ∩ D_w, μ_p(K_w) ⊗ W)`, together with the description of `obs_P ∘ ι_*` as
the product of the local obstructions.

### (d) Lean notes

* **1294.** `Subgroup.equivMapOfInjective (H : Subgroup G) (f : G →* N) (hf : Injective f) :
  H ≃* H.map f` is at `Mathlib/Algebra/Group/Subgroup/Map.lean:478`; `Subgroup.subtype_injective`
  exists (`Defs.lean:236`).
* **1295.** For `Q : Subgroup ↥H` and `S := Q.map H.subtype`, the comparison
  `(Action.res _ (e : ↥Q →* ↥S)).obj (resObj S A) ⟶ resObj Q (resObj H A)` is
  `hom := ModuleCat.ofHom LinearMap.id`, **`comm := fun _ => rfl`**.  The two representations agree
  on the nose.
* **1296.** `Units/IdeleClassTate.lean` declares `variable {k K : Type}` — **implicit**; its counting
  lemmas take only `(S : Subgroup Gal(K/k))`.  By contrast `zsmul_baseFundamentalClass_eq_zero_imp_dvd`
  (`Units/BaseTate.lean`) has `k K` explicit.
* **1297.** `resObj S (tensorObj A W)` and `tensorObj (resObj S A) (resObj S W)` are defeq, so
  `ker`/`range` statements mixing the two unify with no bridging.
* **1298.** `lake build InverseGalois.CFT.TateCohomology.NakayamaSubgroupError` = **8084 jobs**; full
  root build with all four files = **9675 jobs**.

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
| **Grunwald–Wang** | **ABSENT in Mathlib / EXISTS locally** | Zero hits upstream, nothing adjacent (no Ш, no local–global for cyclic extensions). `$L/CFT/GrunwaldWang.lean` proves the power-class form for a squarefree exponent — see §0.24. |
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

Adds Grunwald–Wang (**[XXL]**, needs CFT — but see §0.24: the power-class form for a squarefree
exponent is landed, so what is left of this item is the character form), Poitou–Tate duality
(**[XXL]**, needs profinite group
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

## 0.95 Status (2026-09-04, later) — Shapiro over a subgroup: the ideles' `p`-torsion decomposed over an arbitrary subgroup of the Galois group

### (a) The obstacle §0.94 left, and why base change was the wrong idea

§0.94 reduced row 5 to a single statement about a single map over a Sylow subgroup `P ≤ G`:

```
obs_P : Ĥ⁰(P, C_K ⊗ W)  →  Ĥ²(P, C_K[p] ⊗ W)      (i.e. `…_of_sylow_map … (-2)` after shifting)
range obs_P ∘ ι_*  =  range obs_P                  (the content of row 5)
```

and the plan for computing the target is Shapiro: `Ĥ*(G, I_K[p] ⊗ W) ≅ ∏_v Ĥ*(D_w, μ_p(K_w) ⊗ W)`,
the product over the places `v` of the *base* field.  A subgroup `P` does **not** fix the places of
the base field, so the naive reading fails.

The tempting fix — base change `k ⇝ K^P`, so that `P` becomes the full Galois group of `K/K^P` and
the existing whole-group statement applies verbatim — is a **trap**, and was rejected.  It forces
every object in sight (`W`, `α`, the class formation data, the fundamental class) to be re-derived
over the new base field, and the compatibility of `obs` with that base change is exactly as hard as
the thing being proved.  Route taken instead, per §0.93(d) ("Shapiro works for *any* subgroup"):
**restrict the family action, not the base field.**

### (b) Brick 1 — `Tate/FamilyResGroup.lean`

Every orbit-decomposition theorem in `Tate/Family*.lean` is stated for a bare
`{G X : Type} [Group G] [MulAction G X] [Finite G]` with a `FamilyAction M G`.  A subgroup `S ≤ G`
acts on the *same* family, with the *same* transports:

```lean
def FamilyAction.resGroup (F : FamilyAction M G) (S : Subgroup G) : FamilyAction M ↥S where
  map g x := F.map (g : G) x
  map_one x a := F.map_one x a
  map_mul g h x a := F.map_mul (g : G) (h : G) x a
```

There is nothing to prove: `Subgroup.instMulAction`'s `(g : ↥S) • x` is *definitionally*
`(g : G) • x` (`Submonoid.smul_def` is `rfl`), so all six compatibilities are `rfl`:

| statement | proof |
| --- | --- |
| `(F.resGroup S).familyAut = F.familyAut.comp S.subtype` | `rfl` |
| `(F.torsion m).resGroup S = (F.resGroup S).torsion m` | `rfl` |
| `orbitSectionsRep (F.resGroup S) = resObj S (orbitSectionsRep F)` | `rfl` |
| `torsionRep (F.resGroup S).familyAut m = resObj S (torsionRep F.familyAut m)` | `rfl` |
| `repOfAddAut (φ.comp f) = (Action.res _ f).obj (repOfAddAut φ)` | `rfl` |
| `torsionRep (φ.comp f) m = (Action.res _ f).obj (torsionRep φ m)` | `rfl` |

so `tateTensorTorsionResGroupEquiv` — the orbit decomposition over `S` — is literally
`tateTensorTorsionEquiv (F.resGroup S) (resObj S W) e x₀ hH hH' n`.

Two small pieces of glue had to be added alongside.

1. **`stabilizerSubgroupHom S x : ↥(stabilizer ↥S x) →* ↥(stabilizer G x)`** — `⟨(g : ↥S), g.2⟩`,
   all fields `rfl`.  This is needed because *no*
   `MulSemiringAction ↥(stabilizer ↥S v) (v.adicCompletion K)` instance exists in the repository,
   so the local factor over `S` cannot be phrased with `smulUnitsAut` directly; it is phrased as
   `(smulUnitsAut (G := D_v)).comp (stabilizerSubgroupHom S v)`.
2. **`resObj_pairRep S A B : resObj S (pairRep A B) = pairRep (resObj S A) (resObj S B)`.**  This
   is a genuine (if two-line) obstruction, not a `rfl`.  `resObj S (piRep A) = piRep (fun i => resObj
   S (A i))` **is** `rfl`, because the `.V` field of `(Action.res _ f).obj X` iota-reduces to `X.V`
   even with `i` free.  But `pairFamily A B = fun b => cond b A B`, and under the binder
   `cond b (resObj S A) (resObj S B)` is *stuck*.  Proof: `funext b; cases b <;> rfl`, then `rw`.

### (c) Brick 2 — `Units/IdeleTorsionSubgroup.lean`

The number-field instantiation.  The only mathematical content is the identification of the local
factor: for an orbit `ω` of `S` on the places of `K` and a chosen `v₀ ∈ ω`,

```lean
theorem stabAut_resGroup_adicUnits_eq :
    stabAut v₀ _ (orbitFamily ((adicRingFamily (k := k) (K := K)).unitsFamily.resGroup S) ω)
      = (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
          (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K)).comp
        (stabilizerSubgroupHom S (v₀ : HeightOneSpectrum (𝓞 K)))
```

— the transport by an element of `S` fixing `v₀` *is* the transport by that element of `G`.  Proof:
`stabAut_orbitFamily` (which applies verbatim to the restricted family, gotcha 1314) followed by
`transport_adicUnitsFamily`.  Mirror statement at the infinite places.

From that, `adicIdeleTorsionTensorTateResEquiv` / `infiniteIdeleTorsionTensorTateResEquiv` and then

```lean
def ideleTorsionTensorTateResEquiv (n : ℤ) :
    tateModule (resObj S (tensorObj (torsionRep (ideleAutHom k K) (p : ℤ)) W)) n ≃+
      (∀ ω : orbitRel.Quotient ↥S (InfinitePlace K),        tateModule … n) ×
      (∀ ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K)), tateModule … n)
```

**the complete cohomology of an arbitrary subgroup `S ≤ Gal(K/k)` with coefficients in `I_K[p] ⊗ W`,
as the product over the `S`-orbits of places of `K` of the complete cohomology of the stabiliser
there with coefficients in `μ_p(K_w) ⊗ (W|_S)`**, together with the vanishing corollary
`isZero_tateModule_tensor_ideleTorsionRes`.

The assembly is four isomorphisms glued: `ideleTorsionIso` (torsion of the restricted product is the
torsion of the full product), `fullIdeleTorsionIso` (the full product splits as a pair), the
`eqToIso` of `resObj_pairRep`, and `tateTensorPairEquiv`; then the two halves.

Costs: `lake build …Units.IdeleTorsionSubgroup` = **8227 jobs**; full root build = **9677 jobs**,
0 warnings, 0 errors.

### (d) Gotchas recorded

* **1308.** `TateCohomology/Pair.lean` declares `variable {k G : Type}` — universe-monomorphic.  A
  caller writing `universe u` + `{k G : Type u}` gets `pairRep … has type Rep.{0} … but is expected
  to have type Rep.{u} …`.  Use `{k G : Type}`.
* **1309.** `resObj` commutes with `piRep` definitionally but **not** with `pairRep` (see (b)2).
* **1310.** `tensorIsoLeft W (f : A ≅ B) : tensorObj A W ≅ tensorObj B W` — coefficient argument
  **first**, iso second.
* **1311.** There is no `resIso`; restrict an iso with `(Action.res _ S.subtype).mapIso f`.
* **1312.** Leaving `tateTensorPairEquiv _ _ …` with underscores over a restricted representation
  times out `isDefEq` at 200000 heartbeats.  Pass both representation arguments explicitly and set
  `synthInstance.maxHeartbeats 800000` / `maxHeartbeats 1000000`.
* **1314.** `stabAut_orbitFamily F x₀ hH' hH'' g a` applies verbatim with
  `F := (…).unitsFamily.resGroup S`; `transport_adicUnitsFamily` /
  `transport_infiniteUnitsFamily` then finish with all arguments `_`.
* **1316.** `Tate/FamilyConst.lean` (home of `smul_orbit_of_mem_stabilizer_val` and
  `mem_stabilizer_val_of_smul_orbit`) is **not** in the import closure of
  `Units/IdeleTorsionTensor.lean`; import it explicitly.

### (e) What the next brick is

The place-by-place description is now available over the Sylow subgroup, so the remaining chain for
row 5 is:

1. the short exact sequence `0 → μ_p(K) ⊗ W → I_K[p] ⊗ W → C_K[p] ⊗ W → 0` read over `S`.  This
   should be nearly free: `resSeq` preserves short exactness and `resSeq_cocycleSeq` &c. are all
   `rfl` (gotcha 1114).
2. the identification of `Ĥ^{n+4}(P, C_K[p] ⊗ W)` with a quotient of `∏_ω Ĥ^*(P ∩ D_w, μ_p(K_w) ⊗ W)`
   coming from 1, and the description of `obs_P ∘ ι_*` as the product of the local obstructions.
3. **the real content**: the sum-of-invariants / reciprocity input proving
   `obs_P(range ι_*) = range obs_P` at `n = -2`.

Step 3 is where the global input (reciprocity, the product formula for the `p`-th power Hilbert
symbol — row 6, already done) finally enters; steps 1 and 2 are bookkeeping of the kind just
completed.

## 0.96 Status (2026-09-04, later still) — Poitou–Tate, read as a duality: what row 5 actually needs, and the naturality brick that was missing

### (a) The question this section answers

The directive was "work on Poitou–Tate, make sure it *feeds* appropriately into rows 5/6".  Row 6
(the `p`-th power Hilbert symbol and its product formula) is done.  Row 5 is

```
Ш²(k, A)  ≅  Ш¹(k, A′)^∨                            (global duality, Poitou–Tate)
```

but §0.94 already reduced *the thing row 5 is used for* to the single equation

```
(*)     range (obs_P ∘ ι_*)  =  range obs_P ,       obs_P : Ĥ⁰(P, C_K ⊗ W) → Ĥ²(P, C_K[p] ⊗ W)
```

over a Sylow subgroup `P ≤ G = Gal(K/k)`.  So the question is not "how do I state the nine-term
sequence" but "which duality statement, at the *finite* level the repository works at, discharges
`(*)`".

### (b) Milne's route, and why the repository does not take it

Milne, *Arithmetic Duality Theorems* (local copy: `/home/alex_harmonic_fun/igp-logs/adt.txt`;
§I.1 at line 977, Thm I.1.8 at 1183, the `(G_S, C_S)` material at 2515–2552, Thm I.4.6 at 2635,
Thm I.4.10 at 2866) proves global duality for a **`P`-class formation** `(G_S, C_S)` by producing,
for every finitely generated `G_S`-module `M`, maps

```
α^r(G_S, M) : Ext^r_{G_S}(M, C_S)  →  H^{2-r}(G_S, M)^∨
```

and showing `α^r` is an isomorphism for `r ≥ 1` (Thm I.4.6), whence the nine-term sequence
(Thm I.4.10).  Formalizing that literally would require the `Ext^r_{G_S}(M, C_S)` machinery over a
**profinite** group, plus the `S`-idele class formation as an object in its own right.

The repository is built the other way round: everything lives at the *finite* level
`Ĥ^*(G, C_K ⊗ W)` with `G = Gal(K/k)` finite, and the profinite statements are assembled from
finite ones.  **At the finite level Milne's `α^r` factors as**

```
Ĥ^r(G, Hom(M, C_K))  --(Tate cup-product duality)-->  Ĥ^{-r-1}(G, M)^∨
Ĥ^r(G, Hom(M, C_K))  <--(Tate–Nakayama, cup with the fundamental class)--  Ĥ^{r-2}(G, M)
```

and **both halves are already in the repository**:

* Tate–Nakayama — `TateCohomology/Nakayama*.lean`, `Units/BaseTateSylow.lean` (conditional only on
  the `Tor₁` clause, which is discharged for the modules in play).
* Tate cup-product duality — `TateCohomology/Duality.lean` (degree `0` against degree `-1`),
  `DualityShift.lean` (the two degree-moving identifications), `DualityDivisible.lean` (the
  recursion over all of `ℤ`, with the criterion of Baer replacing the hypothesis on the
  representation), culminating in
  `tateDualEquivOfBaer : Ĥ^n(G, Hom(A, C)) ≃ₗ (Ĥ^{-n-1}(G, A) →ₗ C)` and its specialization
  `tateCharacterEquiv` at `C = ℝ/ℤ`.

**Decision (governing): stay with the `Ĥ^*(G, C_K ⊗ W)` formulation; do not build
`Ext^r_{G_S}(M, C_S)`.**  What was actually missing was neither half of the factorization — it was
that *the duality was not known to be compatible with a map of the representation*, which is
precisely what turns a statement about `range` into a statement about `ker`.

### (c) The dual reformulation of `(*)`

Over a field of coefficients (or any dualizing `C`), for a map `u : X → Y` of finite abelian groups,

```
range u = Y   ⟺   ker (u^∨ : Y^∨ → X^∨) = 0
range (v ∘ u) = range v   ⟺   ker (u^∨ ∘ (…)) ∩ … = …
```

and the useful form of `(*)` is: **a functional on `Ĥ²(P, C_K[p] ⊗ W)` that kills
`range (obs_P ∘ ι_*)` kills `range obs_P`.**  Under the duality this functional *is* a class of
`Ĥ^{-3}` of the dual representation, `obs_P^∨` *is* the map the duality attaches to `obs_P`, and
`ι_*^∨` *is* the map attached to `ι_*`.  Getting from "the functional attached to `obs_P`" to "the
map induced by the dual of `obs_P`" is exactly the naturality square

```
Ĥ^n(G, Hom(B, C)) --(Hom(φ,C))_*--> Ĥ^n(G, Hom(A, C))
      |  dual                              |  dual
      v                                    v
Ĥ^{-n-1}(G, B)^∨  --(- ∘ φ_*)-->     Ĥ^{-n-1}(G, A)^∨
```

which is what `DualityNatural.lean` now proves, for every `φ`, every `n` and every `C` satisfying
the criterion of Baer.

### (d) The blocker inside `DualityDivisible.lean`, and its removal

`tateDualEquivOfBaer` is defined by recursion on the degree.  Each step transports a duality
against `coshiftObj A` up one degree, or a duality against `shiftObj A` down one degree, and each
transport had to reconcile two spellings of a degree, e.g. `-(n+1)-1+1` versus `-n-1`.  Both steps
did that with

```lean
rwa [show (-(n+1)-1+1) = -n-1 from by ring] at h
```

producing an **opaque `Eq.mpr`** in the middle of the definition.  Naturality against such a term is
unprovable: the equation relates two expressions *both* containing `n`, so `subst` does not apply,
and `generalize` breaks the dependent motive.

Fix (commit below): add `subst`-defined degree-comparison helpers to `DualityDivisible.lean` and
re-define the two steps in term mode against them:

```lean
def tateCoshiftEquivCongr (A : Rep ℤ G) {d n : ℤ} (h : d + 1 = n) :
    ↥(tateModule A d) ≃ₗ[ℤ] ↥(tateModule (coshiftObj A) n) := by subst h; exact tateCoshiftEquiv A d

def tateShiftEquivCongr (A : Rep ℤ G) {d n : ℤ} (h : d + 1 = n) :
    ↥(tateModule (shiftObj A) d) ≃ₗ[ℤ] ↥(tateModule A n) := by subst h; exact tateShiftEquiv A d
```

plus `dualStepUp_apply` / `dualStepDown_apply`, both `rfl` (gotcha 1325).  With those in hand every
naturality step is `subst h; exact <the ShiftNatural lemma>`.

The refactor was **free**: nothing in the repository imports `DualityDivisible.lean` except
`InverseGalois/CFT.lean` (gotcha 1324), so `lake build …DualityDivisible` is 8063 jobs / 49 s.  Had
the helpers gone into `Shifting.lean` or `ShiftNatural.lean`, as first planned, most of the CFT tree
would have been invalidated.

### (e) `TateCohomology/DualityNatural.lean` — what landed

`coeffDualHom φ C : coeffDualObj B C ⟶ coeffDualObj A C` (a map of representations reverses the
direction on functionals), functorial (`coeffDualHom_id`, `coeffDualHom_comp`), and then the three
squares:

| square | statement | proof |
| --- | --- | --- |
| middle degrees | `tateDualZeroEquiv_naturality` | `H0mk_surjective` + `exists_Hm1mk`, then `rfl` |
| coshift/shift | `coeffDualShiftIso_naturality` | both routes are `∑ₓ ψ x (φ (f x))` |
| shift/coshift | `coeffDualCoshiftIso_naturality` | both routes are `∑ₓ ψ x (φ (z x))` |

The recursion is carried by a predicate rather than by mirroring the construction:

```lean
def IsTateDualNatural (C : Type) [AddCommGroup C] (n : ℤ)
    (e : ∀ A : Rep ℤ G, ↥(tateModule (coeffDualObj A C) n) ≃ₗ[ℤ]
      (↥(tateModule A (-n - 1)) →ₗ[ℤ] C)) : Prop :=
  ∀ {A B : Rep ℤ G} (φ : A ⟶ B) (x) (z),
    e A (tateMap (coeffDualHom φ C) n x) z = e B x (tateMap φ (-n - 1) z)
```

with `IsTateDualNatural.degCongr`, `.stepUp`, `.stepDown` matching the three constructors of the
recursion one for one — the point being that `tateDualEquivNat C hC m` *is literally* a term of type
`∀ A, …`, and `tateDualEquivNeg`'s inner argument *is literally*
`(fun A' => dualDegCongr C A' h (… A')) (shiftObj A)`, so the `Prop`-level recursion lines up with
the data-level one exactly.  Results:

```lean
theorem tateDualEquivOfBaer_naturality_apply (C) (hC : Module.Baer ℤ C) (n : ℤ) (φ : A ⟶ B) (x) (z) :
    tateDualEquivOfBaer C hC A n (tateMap (coeffDualHom φ C) n x) z
      = tateDualEquivOfBaer C hC B n x (tateMap φ (-n - 1) z)

theorem tateCharacterEquiv_naturality (n : ℤ) (φ : A ⟶ B) (x) (z) :
    tateCharacterEquiv A n (tateMap (coeffDualHom φ (AddCircle (1 : ℚ))) n x) z
      = tateCharacterEquiv B n x (tateMap φ (-n - 1) z)
```

Costs: `lake build …TateCohomology.DualityNatural` = **8066 jobs**, 13 s; full root build =
**9679 jobs**, 0 warnings, 0 errors.

### (f) Two negative findings worth not re-discovering

* **`tateDualEquiv` (in `DualityShift.lean`) is `.some`-defined** — it is extracted from
  `nonempty_tateDualEquiv` by choice, so *no* naturality statement about it is provable, and none
  should be attempted.  The canonical version is `tateDualEquivOfBaer` in `DualityDivisible.lean`;
  everything downstream must use that one.
* **Gotcha 1129, sharpened.** The biquadratic counterexample refutes an idelic fundamental class:
  `α` does not lift to `H²(G, I_K)` because `Ĥ²(G, I_K)` is a direct **sum** over the places, so a
  class with infinitely many nonzero local components has no preimage.  This is why the route to
  `(*)` goes through the *torsion* sequence `0 → μ_p(K) ⊗ W → I_K[p] ⊗ W → C_K[p] ⊗ W → 0` and not
  through `I_K` itself.

### (g) §0.95(e) step 1 is already landed

`Units/IdeleClassTorsionSubgroup.lean` (built earlier the same day) is exactly step 1 of the §0.95(e)
plan: `resSeq_tensorSeq_ideleClassTorsion_shortExact`,
`range_tateδ_tensor_ideleClassTorsionRes` (the image of the connecting map is the kernel of the map
to the ideles) and the two vanishing corollaries, the second with the hypothesis on the ideles
replaced by the vanishing of every local factor over the `S`-orbits.  So the remaining chain is
steps 2 and 3 only.

### (h) The error sequence, continued

The four-term error sequence recorded in §0.93 continues to the left as a long exact sequence:

```
… --Left(n)--> Ĥ^n(W) --…--> Ĥ^{n+2}(A[p] ⊗ W) --obs(n)--> Ĥ^{n+4}(A[p] ⊗ W) --Left(n+2)--> Ĥ^{n+2}(W) → …
```

so `range obs(n) = ker Left(n+2)` is available *if* exactness at `Ĥ^{n+4}(A[p] ⊗ W)` is proved — a
third exactness statement of the same shape as the two already there.  That is an optional brick: it
would let `(*)` be attacked as a statement about a kernel from the start, without invoking the
duality at all.  Recorded, not scheduled.

### (i) Gotchas recorded

* **1324.** Nothing imports `TateCohomology/DualityDivisible.lean` except `InverseGalois/CFT.lean`
  (import at `CFT.lean:662`, narrative at `CFT.lean:4295`).  Edits there cost 8063 jobs / 49 s.
* **1325.** `LinearEquiv.symm_symm … := rfl`; `LinearEquiv.arrowCongr e₁ e₂ f x = e₂ (f (e₁.symm x))`
  (`Mathlib/Algebra/Module/Equiv/Basic.lean:649`).  Hence `dualStepUp_apply` / `dualStepDown_apply`
  hold by `rfl`.
* **1326.** `tateMap_comp_apply` lives in `NakayamaNatural.lean:74`, **not** `Functorial.lean`.  To
  keep the duality tree independent of Nakayama, declare a `private` copy.
* **1327.** `Norm.lean:181` `exists_Hm1mk` is oriented `x = Hm1mk …`, so `obtain ⟨v, hv, rfl⟩`
  substitutes `x`.
* **1328.** `ShiftNatural.lean:54` uses `C` for a *representation*; a new file using `C` for
  coefficients must not collide.
* **1329.** `Duality.lean:279` `tateDualZeroEquiv A C h₁ h₂ = coeffDualEquiv A.ρ C h₁ h₂`.
* **1330.** `↥(coeffDualObj A C).V` is **not** reducibly a function type: `f v` on a term of that
  type fails with "Function expected".  Type the map as
  `coeffDualLinear : (↥B.V →ₗ[k] C) →ₗ[k] (↥A.V →ₗ[k] C)` and let `mkHom` do the defeq; state
  equivariance against `coeffDual B.ρ C g`, not against `(coeffDualObj B C).ρ g`.
* **1331.** For the same reason `(ψ : G → …)` fails on a variable of type
  `↥(coshiftObj X).V` — the coercion resolver does not unfold to find the `Subtype`.  Use `ψ.1`,
  whose elaboration *does* whnf the type.
* **1332.** `rw [indDualMap_apply, indDualMap_apply]` does **not** close the resulting sum equality;
  finish with `exact Finset.sum_congr rfl fun x _ => rfl` (the two summand families are defeq
  pointwise but live over different modules).
* **1333.** Dot notation fails on a `def … : Prop := ∀ …`: `h.degCongr` reports
  "The environment does not contain `Function.degCongr`" because the type is whnf'd to a `Pi`.
  Write `IsTateDualNatural.degCongr h he` in full.  Relatedly, a statement whose only occurrence of
  the section variable `G` is inside an implicit argument leaves `Finite ?m` stuck — pin it with
  `(G := G)`.

### (j) What the next brick is

Unchanged from §0.95(e): step 2 (identify `Ĥ^{n+4}(P, C_K[p] ⊗ W)` as a quotient of
`∏_ω Ĥ^*(P ∩ D_w, μ_p(K_w) ⊗ W)` and describe `obs_P ∘ ι_*` as the product of the local
obstructions) and step 3 (the reciprocity input).  What §0.96 adds is that step 3 may now be run in
its dual form: the naturality square lets a statement about `range obs_P` be converted into one
about the kernel of the dual map, where the sum-of-invariants relation is the natural input.

---

## 0.97 Status (2026-09-04, later still) — the obstruction sequence extends past the obstruction, so row 5 is now an image-equals-kernel statement inside one group

### (a) What landed

`InverseGalois/CFT/TateCohomology/TorsionErrorLong.lean` (new, ~155 lines) and an extension of
`InverseGalois/CFT/Units/BaseTateSylow.lean`.  Build green: the new module alone 8085 jobs,
`BaseTateSylow` 8396 jobs, full root build **9680 jobs**, `grep -c "warning:\|error:"` = 0, 0
sorries.

New declarations, in `InverseGalois.CFT.Tate`:

* `range_tateNakayamaNextMap A b M n :`
  `range (tateNakayamaNextMap A b M n) = ker (tateMap (cocycleTensorSeq (shiftObj A) b M).g (n+1))`
* `range_tateNakayamaTwoNextMap` — the same for the cocycle attached to a class in degree two.
* `range_tateNakayamaPTorsionErrorRight A α W hW hT n :`
  `range (tateNakayamaPTorsionErrorRight … n) = ker (tateNakayamaPTorsionErrorLeft … (n+1))`
* `exact_tateNakayamaPTorsionErrorRightLeft` — the same as `Function.Exact`.
* `range_resTateNakayamaPTorsionErrorRight`, `exact_resTateNakayamaPTorsionErrorRightLeft` — over a
  subgroup.

and in `InverseGalois.CFT`:

* `resBaseTateNakayamaPTorsionLeft k K W hW S n` — the map entering the comparison for the idele
  class group with the fundamental class, read on a subgroup `S`.
* `range_resBaseTateNakayamaPTorsionRight k K W hW S n :`
  `range (obs_S n) = ker (resBaseTateNakayamaPTorsionLeft k K W hW S (n+1))`
* `range_shaTorusPTorsionMap_of_sylow_ker` — the row-5 criterion with the right-hand side of `(*)`
  replaced by that kernel.

### (b) The mathematics

The four-term sequence of `TensorTorsionError.lean` is a window on the long exact sequence of
`cocycleTensorSeq (shiftObj A) (tateTwoCocycle A α) W`, which is
`0 → shiftObj A ⊗ W → cocycleTensorObj → W → 0`.  Writing `E(n)` for
`cocycleTensorObjPTorsionEquiv A α W hW hT n`, an isomorphism
`Ĥ^n(cocycleTensorObj) ≅ Ĥ^{n+3}(A[p] ⊗ W)`, the two error maps are literally

```
errorLeft  n = (tateMap g n)   ∘ E(n)⁻¹      : Ĥ^{n+3}(A[p]⊗W) → Ĥ^n(W)
errorRight n = E(n+1) ∘ (tateMap f (n+1)) ∘ (tateNakayamaIso)⁻¹
                                             : Ĥ^{n+2}(A⊗W) → Ĥ^{n+4}(A[p]⊗W)
```

so exactness of the long exact sequence at `Ĥ^{n+1}(cocycleTensorObj)` — i.e.
`range (tateMap f (n+1)) = ker (tateMap g (n+1))`, which is `tateExact_map_map` — transports along
`E(n+1)` to `range (errorRight n) = ker (errorLeft (n+1))`.  The whole thing is therefore one long
exact sequence

```
… --errorLeft n--> Ĥ^n(W) --TN--> Ĥ^{n+2}(A⊗W) --errorRight n--> Ĥ^{n+4}(A[p]⊗W)
   --errorLeft (n+1)--> Ĥ^{n+1}(W) --TN--> …
```

alternating between the coefficients, their tensor product with the representation, and the vectors
killed by the prime.

### (c) The new shape of row 5

§0.94(b) stated the remaining content of row 5 as, for `P` a Sylow `p`-subgroup of `Gal(K/k)`,

```
(*)   Submodule.map obs_P (range ι_*) = range obs_P
```

The right-hand side was, until now, opaque: `range obs_P` is the image of a map out of a group we
have no independent handle on.  §0.97 replaces it by an explicitly described subgroup of the target:

```
(*)   Submodule.map obs_P (range ι_*) = ker (Left_P (n+1))
```

with both sides living inside `Ĥ^{n+4}(P, C_K[p] ⊗ W)`, the group that §0.95 decomposes into local
pieces.  `Left_P (n+1) : Ĥ^{n+4}(P, C_K[p] ⊗ W) → Ĥ^{n+1}(P, W)` is `resBaseTateNakayamaPTorsionLeft`
— an explicit linear map, not a `range`.  This is the form in which the reciprocity input can be
fed: at `n = -2` the target `Ĥ^{-1}(P, W)` is the norm-kernel of `W`, and the sum-of-invariants
relation is exactly a statement that a product of local classes lands in it.

### (d) What did *not* change

The two remaining steps of §0.95(e) are untouched: step 2 (the local decomposition of
`Ĥ^{n+4}(P, C_K[p] ⊗ W)` and the componentwise description of `obs_P ∘ ι_*`) and step 3 (the
reciprocity input).  What §0.97 buys is that step 3's *target* is now a kernel of an explicit map
rather than an image of an inaccessible one, so step 2's local decomposition has something concrete
to be compared against.

### (e) Lean facts learned

* **1334.** `tateExact_map_map hX n : Function.Exact (tateMap X.f n) (tateMap X.g n)` lives at
  `TateCohomology/Graded.lean:131`, next to `tateExact_map_δ` (146) and `tateExact_δ_map` (162).
  `LinearMap.exact_iff` does **not** apply to it directly (the maps are `ModuleCat` homs, not
  `LinearMap`s); the repo idiom, at `TateNakayamaError.lean:94`, is
  `ext x; simp only [LinearMap.mem_range, LinearMap.mem_ker]; exact (tateExact_map_map … x).symm`.
* **1335.** For `E` a `LinearEquiv`, the shape `range (E ∘ₗ f) = ker (g ∘ₗ E.symm)` closes with
  `rw [LinearMap.range_comp, <range f = ker g>, LinearMap.ker_comp]` followed by
  `exact Submodule.map_equiv_eq_comap_symm _ _`.
* **1336.** `Units/BaseTateSylow.lean` is a leaf — only `InverseGalois/CFT.lean` imports it — so
  editing it costs 8396 jobs, and a new `TateCohomology/` module it depends on costs 8085.
* **1337.** Reflowing a paragraph in a module docstring can push the *next* line over 100
  characters; re-run the character-accurate length check after every rewrap, not once at the end.

### (f) What the next brick is

Unchanged in substance from §0.95(e)/§0.96(j), now with the sharper target of (c):

1. **Step 2.** Present `Ĥ^{n+4}(P, C_K[p] ⊗ W)` through the short exact sequence of
   `Units/IdeleClassTorsionSubgroup.lean` and the orbit product of
   `Units/IdeleTorsionSubgroup.lean`, and describe `obs_P ∘ ι_*` componentwise.
2. **Step 3.** The reciprocity input, now in the form `map obs_P (range ι_*) = ker (Left_P (n+1))`,
   optionally run in the dual form supplied by `DualityNatural.lean`.

---

## 0.98 Status (2026-09-04, later) — the first half of step 2 is **landed**, and two structural facts about the second half

### (a) What landed

`InverseGalois/CFT/Units/IdeleClassTorsionSubgroupLocal.lean` (full root build **9681 jobs**, 0
warnings, 0 errors).  It is the subgroup analogue of `Units/IdeleClassTorsionLocal.lean`, i.e. the
*target of the obstruction*, presented locally, over an arbitrary `S ≤ Gal(K|k)` — and therefore
over a Sylow `p`-subgroup `P`, which is the only case the criterion of `Units/BaseTateSylow.lean`
ever asks about.

```lean
theorem ker_tateδ_tensor_ideleClassTorsionRes (n : ℤ) :
    LinearMap.ker (tateδ (resSeq_tensorSeq_ideleClassTorsion_shortExact hp W S) n).hom
      = LinearMap.range (tateMap
        (resHom S (tensorHomLeft W (ideleToIdeleClassTorsion k K (p : ℤ)))) n).hom

abbrev localTorsionResFamily (n : ℤ) : Type :=      -- ∏ over S-orbits of places of K
  (∀ ω : orbitRel.Quotient ↥S (InfinitePlace K), …) × (∀ ω : orbitRel.Quotient ↥S (…), …)

theorem exists_localTorsionRes_tateMap_eq_of_isZero (n : ℤ)
    (h : Limits.IsZero (tateModule (resObj S (tensorObj (torsionRep globalUnitsAut (p:ℤ)) W)) (n+1)))
    (x : tateModule (resObj S (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W)) n) :
    ∃ y : localTorsionResFamily (p := p) W S w₀ v₀ n,
      tateMap (resHom S (tensorHomLeft W (ideleToIdeleClassTorsion k K (p : ℤ)))) n
        ((ideleTorsionTensorTateResEquiv S W e w₀ v₀ n).symm y) = x
```

and the bridge to the shape `BaseTateSylow.lean` states the obstruction in,

```lean
def ideleClassTorsionNsmulResEquiv (n : ℤ) :
    ↥(tateModule (tensorObj (nsmulTorsion (resObj S (ideleClassRep k K)) p) (resObj S W)) n)
      ≃ₗ[ℤ] ↥(tateModule (resObj S (tensorObj (torsionRep (ideleClassAutHom k K) (p:ℤ)) W)) n) :=
  tateTensorNsmulTorsionRepEquiv ((ideleClassAutHom k K).comp S.subtype) p (resObj S W) n
```

which is accepted **verbatim**: `resObj S (repOfAddAut φ)` and `repOfAddAut (φ.comp S.subtype)` are
definitionally equal, as are `resObj S (torsionRep φ m)` and `torsionRep (φ.comp S.subtype) m` and
(gotcha 1297) `resObj S (tensorObj A W)` and `tensorObj (resObj S A) (resObj S W)`.  So
`tateTensorNsmulTorsionRepEquiv` from `Units/NsmulTorsionRep.lean`, stated for a bare finite group,
already *is* the subgroup bridge; no new transport was needed.

So the **target** of `obs_P` is now a group presented entirely by local data.  What is still missing
from step 2 is the description of `obs_P ∘ ι_*` — and (b) says that description cannot take the
shape §0.93(d) assumed.

### (b) Negative result — `Ĥ^*(P, I_K ⊗ W)` has **no** local product (or sum) description

§0.88(d) and §0.93(d) both list "Shapiro for `I_K ⊗ M`" as a pending brick, on the analogy with
`Ĥ^*(G, I_K) = ⊕_v Ĥ^*(D_w, K_w^×)` and with the landed
`Ĥ^*(S, I_K[p] ⊗ W) ≅ ∏_ω Ĥ^*(S ∩ D_w, μ_p(K_w) ⊗ W)` of `Units/IdeleTorsionSubgroup.lean`.  **The
naive form is false.**

*Why the torsion case works.*  Two facts, both worth keeping:

* for any family `(M_w)`, the natural map `(∏_w M_w)/p → ∏_w (M_w/p)` is an isomorphism (surjective
  componentwise; injective because `(p x_w)_w = p·(x_w)_w`);
* for `W` a **finite-dimensional** `𝔽_p`-vector space, `− ⊗_{𝔽_p} W ≅ (−)^{dim W}` commutes with
  arbitrary products.

Together: `(∏_w M_w) ⊗_ℤ W ≅ ∏_w (M_w ⊗_ℤ W)` whenever `W` is killed by `p` and finite-dimensional.
This is exactly what makes `I_K[p] = ∏_w μ_p(K_w)` survive tensoring, and it is what
`ideleTorsionTensorTateResEquiv` rests on.

*Why the full-idele case fails.*  `I_K ⊗ W` is the restricted product `∏'_w (K_w^× ⊗ W)` with
respect to `O_w^× ⊗ W`, so `Ĥ^*(P, I_K ⊗ W) = colim_S Ĥ^*(P, I_{K,S} ⊗ W)` with

```
Ĥ^*(P, I_{K,S} ⊗ W)  =  ∏_{ω ⊆ S} Ĥ^*(P_w, K_w^× ⊗ W)  ×  ∏_{ω ⊄ S} Ĥ^*(P_w, O_w^× ⊗ W).
```

For `I_K` itself the second product vanishes for `S ⊇ Ram(K|k)`, because the local units of an
unramified extension are cohomologically trivial.  **After tensoring with `W` they do not.**  Take
`M` cohomologically trivial over a group `D`; from `0 → M[p] → M → pM → 0` and
`0 → pM → M → M/pM → 0` one gets `Ĥ^i(D, M/pM) ≅ Ĥ^{i+1}(D, pM) ≅ Ĥ^{i+2}(D, M[p])`.  With
`M = O_w^×`, `M[p] = μ_p(K_w)`, `W = 𝔽_p` trivial (so `M ⊗ W = M/pM`):

```
Ĥ^i(D_w, O_w^× ⊗ 𝔽_p)  ≅  Ĥ^{i+2}(D_w, μ_p(K_w)).
```

Concretely, over `k = ℚ(ζ_p)` with `K|k` cyclic of degree `p` and `w` an *unramified* place with
`D_w` of order `p`: `Ĥ^0(D_w, O_w^× ⊗ 𝔽_p) ≅ Ĥ^2(D_w, μ_p) ≅ Ĥ^0(D_w, μ_p) = μ_p/μ_p^p ≅ ℤ/p ≠ 0`.
By Chebotarev infinitely many places are of that kind, so the second product has infinitely many
nonzero factors for **every** finite `S`.

*What survives.*  The colimit is filtered, so `range ι_* = ⋃_S range (ι_{S,*})` inside the fixed
group `Ĥ^{n+2}(P, C_K ⊗ W)`: a class comes from the ideles iff it comes from the `S`-ideles for
**some** finite `S`.  That is the classical formulation (Tate's tori paper works with `I_{K,S}`
throughout, never with a product formula for `I_K ⊗ W`), and it is what step 2's second half has to
be built on.  The brick to schedule is therefore **`Ĥ^*(P, I_{K,S} ⊗ W)` for a finite `S`**, not a
product formula for `I_K ⊗ W`.

### (c) Negative result — lattice dévissage on `W` is circular; free `𝔽_p[P]`-dévissage shifts the degree but has no base case

Two dévissages suggest themselves for reducing the `p`-torsion criterion to the torsion-free one of
§0.88(b) (`range_baseShaTorusMap`).  Neither works, for opposite reasons.

**Lattice resolution.**  Take `0 → X_1 → X_0 → W → 0` with `X_i` `P`-lattices.  Tensoring with `C_K`
gives the four-term sequence `0 → Tor_1(C_K,W) → C_K⊗X_1 → C_K⊗X_0 → C_K⊗W → 0`, and
`Tor_1(C_K,W) = C_K[p] ⊗ W` — **the same obstruction group** the four-term error sequence of
`TensorTorsionError.lean` produces.  So the lattice case cannot be leveraged by presentation; the
Tor term reproduces the difficulty verbatim.

**Free `𝔽_p[P]`-resolution.**  Take `0 → W' → F → W → 0` with `F` free over `𝔽_p[P]`.  Because every
term is an `𝔽_p`-vector space, `X ⊗_ℤ − = (X/p) ⊗_{𝔽_p} −` on this sequence, which is exact for
**any** `X`; and `X ⊗_ℤ 𝔽_p[P]^d ≅ Ind_1^P((X/p)^d)` is induced, so `Ĥ^*(P, X ⊗ F) = 0`.  Hence the
connecting map is an isomorphism `Ĥ^m(P, X ⊗ W) ≅ Ĥ^{m+1}(P, X ⊗ W')`, **naturally in `X`** — so it
carries the whole diagram (`E`, `I`, `C`, `C[p]`) at once.  Cup product commutes with connecting
maps, so `TN` is carried too, and

> the row-5 criterion at `(W, m)` holds **iff** it holds at `(W', m+1)`.

Since `𝔽_p[P]` is self-injective (`P` a `p`-group, so `𝔽_p[P]` is a Frobenius algebra and free =
injective), `W` also *embeds* in a free module, so the shift runs downwards as well.  Consequently
**the criterion, quantified over all `W`, is independent of the degree**: it may be checked in
whichever degree is most convenient.  That is a real simplification of the target, but it is a
reduction with no base case — every degree remains equally open.

A tempting corollary is false and worth writing down: "if `W = N/pN` for a `P`-lattice `N` then
`TN_W` is an isomorphism" does **not** follow from `TN_N` being one, because the bottom row of the
would-be ladder is not exact: `C_K ⊗ N --p--> C_K ⊗ N` has kernel `(C_K ⊗ N)[p] ⊇ C_K[p] ⊗ N ≠ 0`.

### (d) Lean notes

* **1338.** `resObj S (repOfAddAut φ)` is **definitionally** `repOfAddAut (φ.comp S.subtype)`, and
  likewise `resObj S (torsionRep φ m) = torsionRep (φ.comp S.subtype) m`.  Combined with gotcha
  1297 this means every `Units/NsmulTorsionRep.lean` statement, though phrased for a bare finite
  group, applies to a subgroup of the Galois group with no transport at all — just instantiate
  `G := ↥S` and `φ := (…).comp S.subtype`.
* **1339.** A hypothesis such as `hp : p.Prime` that appears only in the *proof term* and not in the
  statement is **not** auto-included, even when the statement's other arguments were themselves
  formed with it in a previous declaration.  `exists_localTorsionRes_tateMap_eq_of_isZero` needed an
  explicit `include hp in`; `exists_localTorsionRes_tateMap_eq`, whose statement mentions
  `resSeq_tensorSeq_ideleClassTorsion_shortExact hp W S`, did not.
* **1340.** Composing a `tateMap` with an `AddEquiv` between two `∀ ω, tateModule …`-products via
  `AddEquiv.toIntLinearEquiv` invites the `ℤ`-smul instance diamond of gotcha 850 (the Pi type gets
  `Pi.module ℤ` from the `ModuleCat ℤ` factors, not `AddCommGroup.toIntModule`).  The repo idiom in
  `Units/IdeleClassTorsionLocal.lean` — state the result as `∃ y, f ((equiv).symm y) = x`, applying
  the equivalence to *elements* — sidesteps it entirely and is what this file uses.
* **1341.** `lake build InverseGalois.CFT.Units.IdeleClassTorsionSubgroupLocal` type-checks under
  `lake env lean` in ≈2 min; the full root build with it is **9681 jobs**.

### (e) What the next brick is

1. **Step 2, second half.**  `Ĥ^*(P, I_{K,S} ⊗ W)` for a finite `S` containing the ramified and
   archimedean places, as the product of the local factors at `S` and the unit factors outside it,
   and `range ι_*` as the union over `S` of the images.  (Replaces the impossible product formula
   for `I_K ⊗ W`; see (b).)
2. **Step 3.**  The reciprocity input, in the form `map obs_P (range ι_*) = ker (Left_P (n+1))`.
   The exact sequence it must consume — `0 → Br(K|k) → ⊕_w Br(K_w|k_v) --Σ inv--> ℚ/ℤ`, i.e. ABHN
   (`eq_one_of_mem_sha2`) plus reciprocity (`totalInvariant_eq_one_base`) — is already in the repo;
   what is missing is the machine that carries it from `K^×` coefficients to `K^× ⊗ W`
   coefficients, and that machine is Tate–Nakayama duality for the class formation.

---

## 0.99 Status (2026-09-04, latest) — the projection formula absorbs every local contribution, so only the *local cokernels* are left; plus the exact place Poitou–Tate enters Schmidt–Wingberg

### (a) What landed

Commit `f11f281` (previous session) added `TateCohomology/NakayamaNextNatural.lean` and
`Units/DecompositionNakayamaNext.lean` (the map *leaving* the comparison is natural in the
representation, and at a decomposition group its values on the classes from the completion are the
image of the purely local ones), plus two theorems in `Units/BaseTateSylow.lean`.  Full root build
**9683 jobs**, 0 warnings, 0 sorries.

This session added three theorems, no new modules:

* `Tate.tateCor_tateMap_tensorHomLeft_tateNakayamaTwoMap` and
  `Tate.map_tateCor_range_tateNakayamaTwoMap_le` in
  `TateCohomology/NakayamaSubgroup.lean` — **the projection formula for the comparison**: if
  `φ : A' ⟶ resObj H A` carries `β` to `tateRes H A 2 α`, then
  `cor_H ( (tensorHomLeft _ φ)_* ( TN_{A'} β x ) ) = TN_A α (cor_H x)`, hence
  `cor_H ( φ_* ( range TN_{A'} ) ) ≤ range TN_A`.
  Proof: `tateMap_tensorHomLeft_tateNakayamaTwoMap` turns the left side into
  `cor_H (resTateNakayamaTwoMap H A α M n x)`, and `tateCor_tateNakayamaTwoMap` finishes.
* `map_tateCor_range_tateNakayamaTwoMap_decompositionUnits_le` in
  `Units/DecompositionNakayama.lean` — the same, specialised to `H = D_w` and
  `φ = decompositionPlaceIdeleClass k w`, discharged by `tateMap_localizedFundamentalClass`.
* `range_shaTorusPTorsionMap_of_sylow_nakayama` in `Units/BaseTateSylow.lean` — the row-5 criterion
  in the canonical form of gotcha 1076, with **no obstruction in the statement at all**:
  ```
  range (resTateNakayamaTwoMap P (ideleClassRep k K) (baseFundamentalClass k K) W n)
    ⊔ range (tateMap (resHom P (tensorHomLeft W (ideleToIdeleClass k K))) (n+1+1)).hom = ⊤
  ```
  implies `range (shaTorusPTorsionMap k K W hW n) = ker (…globalUnitsToIdele…)`.  Discharged by
  `range_shaTorusPTorsionMap_of_sylow_sup` after `rw [ker_resBaseTateNakayamaPTorsionRight]`.

### (b) Where Poitou–Tate actually enters Schmidt–Wingberg

Read off `sw.txt` lines 1255–1345.  In the whole paper **Poitou–Tate is used exactly once**, inside
the Claim of step 2, and only as

>  `Ш²(k, E(n,τ)) ≅ Ш¹(k, E(n,τ)′)^∨`,  where `E′ = Hom(E, μ_p)`.

Everything downstream is elementary: `E′` is a *trivial* `G_K`-module, so the Hasse principle gives
`Ш¹(k,E′) ↪ H¹(K|k, E′)`; dualising that injection gives the surjection

>  `Ĥ^{-2}(G, E(n,τ)(-1)) ↠ Ш²(k, E(n,τ))`,

which is the map the Claim needs, and it is natural in `π : F(m) ↠ F(n)`.  Proposition 6 is then
applied with **`k = -2`** and `T = Hom(μ_p, ℤ/pℤ)` — a **one-dimensional** `T`, fixed in advance.
SW state explicitly (line ~340) that Prop 6 is used only for `k = 2` and `k = -2`.

### (c) Consequence: row 5 at `n = -2` repairs §0.87(a) without recreating its circularity

§0.87(a) refuted the §0.84(c) Hochschild–Serre route because its step 3 needed
`dim T₀ ≤ #G² · dim E(m,τ)` with `m = r·n`, and the binder order of
`exists_genericShrink_res_cohomology_eq_zero` made that circular: the module `T` whose cohomology
had to be killed grew with `m`.

The route of record does **not** have that defect.  Its inputs are:

1. §0.84(c) steps 1–2, both already proven: `Ш²(K,E) = 0` (`eq_one_of_mem_sha2`) and the degree-two
   Hochschild–Serre sequence (§0.85/§0.86), giving `Ш²(k,E) ⊆ inf H²(G,E)` modulo transgression;
2. **row 5 at `n = -2`**, i.e. `Ш¹(G, K^× ⊗ W) = image of Ĥ^{-2}(G,W)`, with `W = E(-1)` and the
   Kummer identification of §0.88(a);
3. Prop 6 at `k = -2` with `T = Hom(μ_p, 𝔽_p)` — **one-dimensional and fixed a priori**, so the
   §0.87(a) circularity cannot recur;
4. Prop 6 at `k = 2` with `T = 𝔽_p` trivial, to kill the residual inflated class.

The two shrinks compose: for a target `n` take `m₁ = m₀^{(2)}(n)` and then `m = m₀^{(-2)}(m₁)`; the
surjection `F(m) ↠ F(m₁)` kills the transgression and `F(m₁) ↠ F(n)` kills the inflated class.

### (d) The projection formula absorbs the local Tate–Nakayama contributions

With (a) in hand the shape of step 3 collapses.  Write `P` for a `p`-Sylow of `G`, `w` for a place,
`P_w = P ∩ D_w`.  The criterion is `range TN_P ⊔ range ι_* = ⊤` inside `Ĥ^{n+2}(P, C_K ⊗ W)`.
Decompose `range ι_*` over the places (§0.98(e) item 1).  At each place the *local* comparison
`TN_w` produces classes which, by
`map_tateCor_range_tateNakayamaTwoMap_decompositionUnits_le`, corestrict **into `range TN_P`**.
So the local Tate–Nakayama part of `range ι_*` contributes nothing new, and the whole content of
step 3 is that the **local cokernels** span:

>  `ker Left_P (n+1)  =  Σ_w cor_w ( ker Left_w (n+1) )`   inside `Ĥ^{n+4}(P, C_K[p] ⊗ W)`,

where `cor_w` is `Ĥ^{n+4}(P_w, μ_p(K_w) ⊗ W) → Ĥ^{n+4}(P, I_K[p] ⊗ W) → Ĥ^{n+4}(P, C_K[p] ⊗ W)`.

* The `⊇` inclusion needs exactly one compatibility, `Left_P ∘ cor_w = cor_{P_w}^P ∘ Left_w`, i.e.
  **naturality of `Left`** — see (e).  (Compare gotcha 1345: in the ambient equation the `⊆`
  direction is the automatic one; here, after the decomposition, the roles have swapped, because
  `⊇` is the statement that the local pieces *land* in the right place.)
* The `⊆` inclusion is the reciprocity content and has **no plan yet**.

### (e) Scope of the `Left`-naturality brick

`Left_A(n) = tateMap g_A n ∘ E_A(n)⁻¹` where `g_A = (cocycleTensorSeq (shiftObj A) (tateTwoCocycle A
α) W).g` and `E_A = cocycleTensorObjPTorsionEquiv`.  The relation `ψ ≫ g_B = g_A` is **free** from
`cocycleTensorSeqHom`'s `comm₂₃` (its `τ₃` is `𝟙 W`).  So `Left`-naturality is *exactly* naturality
of `E`, which decomposes into four pieces:

1. `tateMapIso (cocycleTensorIso …)` — formal;
2. `tensorPTorsionShiftFreeEquiv` (`TensorPTorsionShift.lean:536`) — **the substantial one**: built
   from the free presentation `kerSeq (freeHom E)` via `modNsmul`, `modCycleSeq`, `modTorSeq`,
   `modTorTorsionIso` and two `tateδ`s, so it needs functoriality of `freeObj`/`freeHom`/`kerObj`
   plus `tateδ`-naturality (`DeltaNatural.lean`);
3. `tateMapIso (tensorIsoLeft W (cocycleNsmulTorsionIso …).symm)` — formal;
4. `tensorShiftNsmulTorsionEquiv` — formal.

Estimate: 600+ lines over 2–3 modules.

### (f) Shortcuts ruled out this session

* **Dévissage of `W` to the trivial module `𝔽_p`.**  Legitimate (`𝔽_p[P]` is local for a `p`-group
  `P`, so every composition factor is trivial) but useless: `W = 𝔽_p` already contains the
  difficulty, since `Ш¹(P, K^×/p)` is a Selmer-type group.
* **Lattice resolution `0 → X_1 → X_0 → W → 0` with `X_0` free over `ℤ[P]`.**  Then
  `Ĥ^*(P, C_K ⊗ X_0) = 0`, so the induced inclusion `range TN_W ⊇ range v_* = 0` says nothing.
  Consistent with §0.98(c).  (The *other* dévissage, `0 → X --p--> X → W → 0` when `W` lifts to a
  lattice, replaces `W` by `μ_p(K) ⊗ W` in the connecting term — not obviously easier, and it needs
  `W` liftable.)
* **Milne, *Arithmetic Duality Theorems*.**  Grepped `adt.txt`: it has **no** finite-group-level
  Ш-duality theorem; all of its I.4 material is phrased over `G_S`.
* **`K^× ⊗ W` as a Cartier dual.**  `Hom(W^∨, K^×) = W ⊗ μ_p ≠ K^× ⊗ W`, so the finite-level
  Tate/Nakayama duality for tori does not extend to these coefficients.  Corroborates §0.88(c):
  the `p`-torsion case is genuinely Poitou–Tate.
* **`E(n,τ)` free over `𝔽_p[G]`.**  True for `τ = (1,1)` (`F/F^p[F,F] = 𝔽_p[G]^d`, and then
  `Ĥ^*(G, C_K ⊗ 𝔽_p[G]^d) = 0` and row 5 would be vacuous), but **false in general**: for `p` odd
  the degree-two graded piece is `Λ²(𝔽_p[G]^d)`, on which the stabiliser of a basis pair `{g,h}` is
  `⟨hg^{-1}⟩` when `hg^{-1}` is an involution.  So `E(n,τ)` is a sum of `Ind_H^G` of modules over
  subgroups `H` with nontrivial `H` in general, and no free lunch.  (Unverified against SW; recorded
  only to close off the "maybe the coefficients are always induced" hope.)
* **The unramified places impose no condition.**  For `x ∈ H²(G,E)` inflated to `H²(k,E)` and `v`
  unramified in `K`, the composite `H²(G,E) → H²(D_w,E) → H²(k_v,E)` factors through
  `H²(Ẑ, E) = 0` because `G_{k_v} ↠ Ẑ ↠ D_w`.  So `Ш²(k,E) ∩ inf H²(G,E)` is cut out by the
  **ramified and archimedean** places only.  A real simplification of the *statement*, but it does
  not by itself produce the surjection of (b).

### (g) Gotchas

1342. `rw [tateMap_comp_apply]` FAILS on a goal whose inner map is `(cocycleTensorSeq X b M).f` —
      use explicitly-typed `have h1/h2/h3 := tateMap_comp_apply _ _ _ _` and chain with
      `refine h1.trans ?_` / `rw [h2]` / `refine h3.trans ?_` / `exact congrArg …`; also write
      `tateMap φ n x` as a plain application, never `(tateMap φ n).hom x` in a `show`.
1343. Full root build with `NakayamaNextNatural.lean` + `DecompositionNakayamaNext.lean` + the
      extended `BaseTateSylow.lean` is **9683 jobs**; `lake build …NakayamaNextNatural` alone is
      8086 jobs (~10 s); `BaseTateSylow` + `DecompositionNakayamaNext` together is 8685 jobs
      (~2 min).
1344. `rw [tateMap_localizedFundamentalClass k w] at h` succeeds even when the rewritten term occurs
      in the *type of an existential binder*.
1345. (MATH) In `map obs_P (range ι_{P,*}) = range obs_P`, the `⊆` inclusion is **automatic**
      (`range obs_P = ker Left_P` and `Left_P ∘ obs_P = 0`); all content is in `⊇`.
1346. `Submodule.map f (Submodule.map g (LinearMap.range h))` membership unpacks with
      `rintro _ ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩`, and the witness proof must then be the **`.symm`** of
      the projection formula, since `LinearMap.range` membership is `∃ y, f y = x`.

### (h) Next

1. The `Left`-naturality brick of (e) — it makes the `⊇` half of (d) automatic.
2. Step 2's second half (§0.98(e) item 1): `Ĥ^*(P, I_{K,S} ⊗ W)` for finite `S`, and
   `range ι_* = ⋃_S range ι_{S,*}`.  `Units/SIdeleClass.lean` (`SIdele`, `sIdeleDiag`,
   `sIdeleClassSES`), `SIdeleHerbrand.lean`, `SIdeleNorm.lean`, `AdicSIdeles.lean` and
   `AdicOrbitTate.lean` are the base to build on.
3. Step 3's `⊆` half — still the wall.

---

## 1.00 Status (2026-09-04, latest) — row 5 is now a single named hypothesis, and the Tor route is refuted

### (a) What landed

Commits `0db1ee4` and `dce307e`; full root build **9684 jobs**, 0 warnings, 0 errors, 0 sorries,
axioms `[propext, Choice, Quot.sound]`.

* `Units/IdeleClassTorsionSubgroup.lean` (`0db1ee4`) — step 2 bookkeeping.
  `range_tateMap_tensor_ideleClassTorsionRes`: the classes of `Ĥ^n(S, C_K[p] ⊗ W)` coming from the
  ideles are exactly `ker δ`.  `exists_ideleTorsionLocal_of_tateδ_eq_zero` /
  `tateδ_tateMap_ideleTorsionLocal_eq_zero`: each such class is the class of a family of *purely
  local* classes, one per `S`-orbit of places, via `ideleTorsionTensorTateResEquiv`.  Both are
  stated in the gotcha-1340 shape `∃ y, f ((equiv).symm y) = x` to dodge the ℤ-smul diamond.
* **`Units/NakayamaSpan.lean`** (`dce307e`) — the wall, named.

```
def HasIdeleClassNakayamaSpan (k K : Type) … (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ W : Rep ℤ Gal(K/k), (∀ w : ↥W.V, p • w = 0) → ∀ (P : Sylow p Gal(K/k)) (n : ℤ),
    LinearMap.range (resTateNakayamaTwoMap ↑P (ideleClassRep k K) (baseFundamentalClass k K) W n)
      ⊔ LinearMap.range (tateMap (resHom ↑P
          (tensorHomLeft W (ideleToIdeleClass k K))) (n + 1 + 1)).hom = ⊤
```

  with `range_shaTorusPTorsionMap_of_span` deriving row 5 from it (`Sylow.nonempty` supplies the
  subgroup, so none appears in the conclusion), plus its surjectivity readings
  `exists_shaTorusPTorsionMap_of_span` and `exists_shaTorusPTorsionMap_one_of_span`.  The latter is
  literally the map §0.99(b) says Schmidt–Wingberg needs:

>  `Ĥ^{-2}(G, W)  ↠  Ш¹(G, K^× ⊗ W)`,  `W = E(-1)`.

  This is the repository's standard treatment of an out-of-reach step: a `Prop`-valued `def`, never
  an axiom and never a `sorry`.
  `hasIdeleClassNakayamaSpan_of_not_dvd` discharges it unconditionally when `p ∤ [K:k]`: the Sylow
  subgroup is then trivial and `card_nsmul_eq_zero_tateModule` makes every module in sight vanish.
  So the hypothesis is non-vacuous and correct in the degenerate case; only `p | [K:k]` is open.

### (b) The remaining chain to `FrattiniKernelEP`, in full

1. `Ш²(K, E) = 0` — **done** (`eq_one_of_mem_sha2`).
2. degree-two Hochschild–Serre, giving `Ш²(k,E) ⊆ inf H²(G,E)` modulo transgression — **done**
   (§0.85/§0.86).
3. `Ĥ^{-2}(G, E(-1)) ↠ Ш¹(G, K^× ⊗ E(-1))` — **done conditionally**
   (`exists_shaTorusPTorsionMap_one_of_span`).
4. Kummer, as `G`-modules: `K^× ⊗ E(-1) ≅ H¹(K, E)` when `μ_p ⊆ K` — **missing** (§0.90(c) item 2).
5. `Ш¹(G, H¹(K,E)) ↠ Ш²(k, E)`, the edge map of 2 restricted to the locally trivial classes —
   **missing**, but elementary given 1 and 2.
6. Prop 6 at `k = -2` with the one-dimensional `T = Hom(μ_p, 𝔽_p)`, and at `k = 2` with `T = 𝔽_p`
   — **done** (`Shafarevich/Shrink.lean`), composed as in §0.99(c).

So exactly two elementary bricks (4, 5) and one hypothesis (`HasIdeleClassNakayamaSpan`) stand
between the repository and all-solvable.

### (c) Why the span is hard — a refutation to not re-derive

The repository's Tate–Nakayama for a general coefficient module `W` is conditional on
`Tor₁^ℤ(C_K, W)` being cohomologically trivial.  For `W` killed by `p`,

>  `Tor₁^ℤ(C_K, W) ≅ C_K[p] ⊗_{𝔽_p} W`,

so it is tempting to hope `C_K[p]` is cohomologically trivial and thereby get the span for free.
**It is not.**  From `1 → K^× → I_K → C_K → 1`,

>  `1 → μ_p(K) → I_K[p] → C_K[p] → ker(K^×/K^{×p} → I_K/I_K^p) → 1`,

and `I_K[p] = ∏_v μ_p(K_v)` — a *full* product, since roots of unity are units everywhere — which
is `∏_{orbits} Ind_{D_w}^{G} μ_p(K_w)`.  Shapiro then gives `Ĥ^*(G, I_K[p]) = ⊕_v Ĥ^*(D_w, μ_p(K_w))`,
generally nonzero.  (The last term of the four is where Grunwald–Wang and the Wang counterexample
live.)  So no dévissage of the coefficients and no Tor computation removes the arithmetic input.

Together with §0.98(b) (no local product description of `Ĥ^*(P, I_K ⊗ W)`), §0.98(c) (lattice
dévissage is circular) and §0.99(f), the class-formation machinery is now exhausted: it computes
`coker TN = range obs = ker Left`, and nothing more.

### (d) Orientation of the two halves of §0.99(d), restated

For `ker Left_P (n+1) = Σ_w cor_w (ker Left_w (n+1))`:

* `⊇` (`ker Left_P ⊇ Σ_w cor_w(…)`) is the naturality of `Left` — it is a *prerequisite* for using
  the other half, since it is what lets a local class be recognised inside `Right_P(range ι_*)`,
  but on its own it proves nothing about the span.
* `⊆` is the reciprocity content, i.e. exactly the input Poitou–Tate supplies in the literature.

### (e) Lean notes

* An `Int`-numeral degree such as `(-2 : ℤ) + 1 + 1 + 1` **is** `rfl`-equal to `1`, but supplying an
  argument of the `1`-form to a lemma stated in the `+1+1+1`-form raises *Application type
  mismatch*: the elaborator checks argument types at a lower transparency.  Work around it with
  `refine lemma … ?_ ?_` — unification against the goal assigns the value argument, leaving only the
  side condition, which `exact` then closes at default transparency.  (gotcha 1347)
* `Sylow.nonempty` (`Mathlib/GroupTheory/Sylow.lean:177`) is an instance, so
  `obtain ⟨P⟩ : Nonempty (Sylow p Gal(K/k)) := inferInstance` is all that is needed to drop a Sylow
  subgroup out of a statement. (gotcha 1348)

### (f) Next, with the bricks already on the shelf

1. **Brick 4** — the Kummer identification as `G`-modules.  Its core is already present:
   `Profinite/KummerHom.lean` has `IsKummerData`, `IsKummerData.kummerEquiv`
   (`K^×/(K^×)^n ≅ SmoothH1 G_K μ_n`), `ker_kummerHom`, `kummerHom_surjective`, and
   `Profinite/KummerRes.lean` has the restriction behaviour (`resH1_kummerClass_eq_one_iff`,
   `map_localPowers` — the locally trivial classes are the units that are `n`-th powers in every
   completion).  What is missing is (i) equivariance of `kummerEquiv` for the *outer* group
   `Gal(K/k)`, and (ii) the twist `E ≅ μ_p ⊗ Hom(μ_p, E)` when `μ_p ⊆ K`, which turns
   `SmoothH1 G_K μ_p ⊗ Hom(μ_p,E)` into `SmoothH1 G_K E`.
2. **Brick 5** — the edge map on locally trivial classes.  `Profinite/Transgression.lean`
   (`exists_comapH2_eq_of_transgression`) is the degree-two inflation–restriction input and
   `Profinite/ShaComap.lean` the functoriality of `sha2`; `eq_one_of_mem_sha2` is input 1.
3. **A restructuring worth considering before either.**  Inputs 1 and 2 already give
   `Ш²(k,E) ⊆ inf H²(G,E)`, so the *target* of the surjection lives inside a finite-level group.
   Bricks 4 and 5 may therefore be replaceable by a purely finite-level construction of
   `Ш¹(G, K^× ⊗ W) → H²(G, E)`, avoiding the profinite/finite bridge altogether.
4. `Left`-naturality (§0.99(e)), then step 3's `⊆` — still the wall.

### (g) The twist can be made to disappear

`W = E(-1) = Hom(μ_p, E)` is a genuine twist only while `μ_p ⊄ k`.  As soon as `μ_p ⊆ k` the
Galois group `G = Gal(K/k)` acts trivially on `μ_p`, a choice of primitive `p`-th root of unity
gives a `G`-isomorphism `Hom(μ_p, E) ≅ E`, and brick 4 collapses to

>  `K^× ⊗ E ≅ H¹(K, E)`  —  `kummerEquiv` tensored with `E`, plus `G`-equivariance.

And `μ_p ⊆ k` may be *assumed*: `[k(μ_p) : k]` divides `p - 1`, hence is prime to `p`, while every
module in sight is killed by `p`.  So restriction to `k(μ_p)` is injective and corestriction is
surjective on all the groups involved — the same res–cor device the repository already uses to
reduce row 5 to a Sylow subgroup (`surjective_tateCor_sylow_of_prime`,
`range_shaTorusPTorsionMap_of_sylow`).  Doing this *first* is likely the cheapest path through
bricks 4 and 5: it removes the twist, makes `μ_p` a trivial module everywhere, and makes the
Kummer sequence over `K` a sequence of `G`-modules with no coefficient subtleties.  The abstract engine for
this is already present and general: `TateCohomology/SylowSurjective.lean` has
`surjective_tateCor_of_coprime` (corestriction from a subgroup of index prime to a multiple killing
the cohomology is onto) and `nsmul_eq_zero_tateModule_of_nsmul`, and
`TateCohomology/SylowInjective.lean` has `eq_zero_of_tateRes_eq_zero`.  Neither is phrased for a
Sylow subgroup, so both apply verbatim to `Gal(K/k(μ_p)) ≤ Gal(K/k)`; what is missing is only the
base-field plumbing (and the compatibility of `baseFundamentalClass` with the change of base, which
§0.92 flags as the one thing its `.choose` definition does not supply).

---

## 1.01 Status (2026-09-05) — sufficient conditions for the span, and the `Left`-naturality brick of §0.99(e) is **not** needed

### (a) What landed

Full root build **9685 jobs**, 0 warnings, 0 errors, 0 sorries.

1. **`Units/NakayamaSpan.lean`**, two new sufficient conditions for `HasIdeleClassNakayamaSpan`:

   * `hasIdeleClassNakayamaSpan_of_isZero` — if `Ĥ^{n+4}(P, C_K[p] ⊗ W)` vanishes for every Sylow
     `P`, every `W` killed by `p` and every `n`, the span holds.  Reason: that group is where the
     obstruction lands, so `obs_P = 0`, so `ker obs_P = ⊤`, and `ker obs_P = range TN_P`
     (`ker_resBaseTateNakayamaPTorsionRight`) already fills the whole group before the ideles
     contribute anything.  The proof is five lines: transport the vanishing across
     `isZero_tateModule_tensorObj_nsmulTorsion_repOfAddAut`, then `top_sup_eq`.
   * `hasIdeleClassNakayamaSpan_of_isZero_idele` — the same conclusion from vanishing of
     `Ĥ^{n+4}(P, I_K[p] ⊗ W)` **and** `Ĥ^{n+5}(P, μ_p(K) ⊗ W)`, via the squeeze
     `isZero_tateModule_tensor_ideleClassTorsionRes`.  The first of the two is a condition **place
     by place** (Shapiro: `Ĥ^*(P, I_K[p] ⊗ W) = ⊕_ω Ĥ^*(P_w, μ_p(K_w) ⊗ W)`), so this reduces the
     span to data read off the local extensions.

2. **`TateCohomology/NakayamaNextRestrict.lean`** (new module) — the map leaving the comparison of
   Tate and Nakayama against a subgroup:

   * `resNakayamaIso` — the two identifications of degree, read on a subgroup — together with
     `tateRes_tateNakayamaIso`, `tateCor_resNakayamaIso` and the two `symm` versions.
   * `resTateNakayamaNextMap`, `tateRes_tateNakayamaNextMap`, **`tateCor_tateNakayamaNextMap`**, and
     `map_range_resTateNakayamaNextMap`:

     >  `cor_H ( range obs_H )  =  range obs_G`   whenever `cor_H` is onto on `Ĥ^{n+2}(–, A ⊗ M)`.

   * `resTateNakayamaTwoNextMap` and the same three statements for the cocycle attached to a
     prescribed class in degree two.

### (b) Why (2) replaces the 600-line brick of §0.99(e)

§0.99(d) phrased row 5's remaining half as an identity between **kernels of `Left`**, and §0.99(e)
costed the `⊇` half as naturality of `Left` — a large ladder of squares.  That is avoidable.
`range_resBaseTateNakayamaPTorsionRight` (`Units/BaseTateSylow.lean:130`) says

>  `range obs_S (n)  =  ker Left_S (n+1)`

for **every** subgroup `S`, so every statement §0.99(d) makes about `ker Left` is literally a
statement about `range obs`, and the identity to prove becomes

>  `range obs_P  =  Σ_w cor_w ( range obs_{P_w} )`.

The `⊇` half of *that* is `tateCor_tateNakayamaTwoNextMap` — landed above, four lines — because
`map_resBaseTateNakayamaPTorsionRight_eq_range_iff` (`BaseTateSylow.lean:143`) strips the
`cocycleTensorObjPTorsionEquiv` off any spanning statement and leaves exactly
`tateNakayamaTwoNextMap`.  **`Left`-naturality is off the critical path.**  Item 4 of §1.00(f)
should be read as: *step 3's `⊆` only.*

### (c) The structure of `C_K[p]`, from Grunwald–Wang

`exists_pow_eq_of_forall_localPow_outside_of_prime` (`CFT/GrunwaldWang.lean:226`) needs only the
**finite** places and tolerates a finite exceptional set, and it carries no roots-of-unity
hypothesis.  Hence for *every* prime `p`

>  `ker( K^×/(K^×)^p → I_K/I_K^p ) = 1`,   so   `C_K[p] ≅ I_K[p] / μ_p(K)`

— the four-term sequence of §1.00(c) collapses to three terms.  This is the exact sequence the
repository already carries as `resSeq_tensorSeq_ideleClassTorsion_shortExact`
(`Units/IdeleClassTorsionSubgroup.lean:81`); the observation is that Grunwald–Wang is what makes it
short, and that it is short for *every* `p`, not only for `p` odd or `μ_p ⊆ K`.  It does **not**
make `C_K[p]` cohomologically trivial (§1.00(c) stands): the middle term `⊕_w Ĥ^*(P_w, μ_p(K_w))` is
generally nonzero, which is precisely why (a)(2) is a *sufficient* condition and not a proof.

### (d) What is left

* Step 3's `⊆` — `range obs_P ⊆ Σ_w cor_w(range obs_{P_w})`.  Still the reciprocity wall; this is
  where Poitou–Tate enters in the literature.  The best lead remains `C_K[p] ≅ I_K[p]/μ_p(K)` plus
  Shapiro: the obstruction is a map out of `Ĥ^{n+2}(P, C_K[p] ⊗ W)`, whose only non-local input is
  the `μ_p(K)` term, and the reciprocity law is exactly a statement about that term.
* Bricks 4 and 5 of §1.00(b), unchanged — and §1.00(g)'s reduction to `μ_p ⊆ k` first.

### (e) Lean notes

* `lake build InverseGalois.CFT.Units.NakayamaSpan` with the two new imports is **8410 jobs, ~93 s**;
  `…TateCohomology.NakayamaNextRestrict` is **8072 jobs, ~24 s**.  (gotcha 1349)
* `rw [tateCor_naturality]` / `rw [tateRes_naturality]` **fail** on a goal whose morphism is
  `(cocycleTensorSeq S b M).f` while the surrounding `tateCor`/`tateRes` names the object as
  `cocycleTensorObj S b M`: the two are defeq only by unfolding the non-reducible `cocycleTensorSeq`
  and taking a structure projection, which `rw`'s keyed matching will not do.  Instantiating the
  lemma's implicit objects explicitly — `tateRes_naturality (A := tensorObj (shiftObj A) M)
  (B := cocycleTensorObj (shiftObj A) b M) H …` — elaborates fine (argument types are checked at
  default transparency) and produces a hypothesis in the `cocycleTensorObj` form; `exact h` then
  closes the goal.  (gotcha 1352)

---

## 1.02 Status (2026-09-05, later) — the span is now a statement about a *family* of subgroups, read entirely on the map leaving the comparison

### (a) What landed

Commit `a2ebcf5`.  Full root build **9685 jobs**, 0 warnings, 0 errors, 0 sorries; axioms of every
new declaration are `[propext, Classical.choice, Quot.sound]`.

1. **`Units/NakayamaSpan.lean`** — `hasIdeleClassNakayamaSpan_of_next`.  The named hypothesis
   `HasIdeleClassNakayamaSpan k K p` is now implied by a statement in which the comparison of Tate
   and Nakayama does not appear at all, only the map *leaving* it:

   >  `map obs_P ( range ι_{P,*} )  =  range obs_P`   for every `p`-torsion `W`, every Sylow `P`,
   >  every degree.

   Proof: `ker_resBaseTateNakayamaPTorsionRight` rewrites `range TN_P` as `ker obs_P`, `sup_comm`,
   then `map_eq_range_iff_sup_ker_eq_top` (`Units/IdeleTorusShaSharp.lean:68`) converts the `⊔ = ⊤`
   into the image identity, and `map_resBaseTateNakayamaPTorsionRight_eq_range_iff` strips the
   `cocycleTensorObjPTorsionEquiv`.  This matters because `obs` is *natural in the coefficients* and
   the comparison is not, so only in this form can the places be brought to bear.

2. **`TateCohomology/NakayamaNextRestrict.lean`** — the family assembly,
   `map_range_eq_range_of_iSup_cor` and its degree-two specialisation
   `map_range_eq_range_of_iSup_cor_two`.  Given a family of subgroups `Hs : ι → Subgroup G` and, for
   each `i`, an explicit submodule `V i ⊆ Ĥ^{n+2}(Hs i, A ⊗ M)` with

   * `hV` — `cor_{Hs i} (V i) ≤ range ι_*`, and
   * `hglob` — `range obs_G ≤ ⨆_i cor_{Hs i} ( obs_{Hs i} (V i) )`,

   the conclusion is `map obs_G (range ι_*) = range obs_G`, exactly the hypothesis of (1).  The proof
   is four lines and consumes `tateCor_tateNakayamaNextMap`: a value produced on a subgroup out of a
   class whose corestriction `ι_*` already reaches is a value produced on the whole group out of a
   class `ι_*` reaches.

### (b) The shape of the family hypothesis, corrected

The previous session's draft of (2) took the hypothesis in the form *"on each subgroup, `obs`
attains on the local ideles every value it attains at all"*.  That is **not** what the decomposition
brick supplies and is in general false at a single place — a single decomposition group sees only
one local factor, and §0.99's projection formula gives the inclusion in the wrong direction
(gotcha 1277).  The usable form quantifies over an explicit family of submodules `V i` and asks only
that the *corestrictions* cover, which is what Shapiro produces.  Four wrapper lemmas built on the
old form (`sup_range_eq_top_iff_map_range`, `sup_range_eq_top_of_iSup_cor`, and their `_two`
versions) were deleted along with a private copy of the generic linear-algebra lemma the repository
already had.

### (c) What is left, unchanged in substance

* `hglob` at the family of decomposition subgroups of `P` — i.e. still
  `range obs_P ⊆ Σ_w cor_w(range obs_{P_w})`, the reciprocity wall of §1.01(d).  The assembly above
  is the consumer that has been waiting for it; nothing else is missing on that side.
* `hV` for the same family — the easy direction, Shapiro's decomposition of `range ι_*`; deliberately
  not yet wired up, because `hglob` has no proof and the machinery would be unconsumed.
* Bricks 4 and 5 of §1.00(b), and §1.00(g)'s reduction to `μ_p ⊆ k` first.

### (d) Lean notes

* `map_eq_range_iff_sup_ker_eq_top (f : M →ₗ[R] N) (S : Submodule R M) : Submodule.map f S =
  LinearMap.range f ↔ S ⊔ LinearMap.ker f = ⊤` already exists at
  `Units/IdeleTorusShaSharp.lean:68`, used at `BaseTateSylow.lean:189`.  Do not re-derive it in a
  `TateCohomology/` module — `IdeleTorusShaSharp` does not import `NakayamaNextRestrict`, so the two
  copies would not even clash at elaboration time.  (gotcha 1353)
* `Units/BaseTateSylow.lean:213` already carries `range_shaTorusPTorsionMap_of_sylow_next`, the
  "next map" form of the Sylow criterion.  (gotcha 1355)
* There is **no** `Gal(K/k)`-action on `SmoothH1 G_K M` anywhere under `CFT/Profinite/`; bricks 4/5
  would have to build it.  (gotcha 1356)
* No module under `CFT/` mentions `IsInverseGalois` except the four `Scholz/*` files: there is no
  general bridge from `SmoothH2` classes to embedding problems, and the only EP↔arithmetic bridge is
  `CFT/Kummer/CentralEmbeddingPlaces.lean`, whose `exists_surjective_hom_of_forall_place_lift`
  needs a **central** kernel.  (gotcha 1357)

---

## 1.03 Status (2026-09-05, later still) — **brick 5 is done at the profinite level**, and the local condition is the *localised* one

### (a) What landed

Commits `73f68ec`, `c7faa77`, `565db26`, `a1c110a`, `b9bd14d`, `d07b7fd`, `6ed5e84`, `782d566`.
Full root build **9691 jobs**, 0 warnings, 0 errors, 0 sorries.

The whole of brick 5 of §1.00(b), in the profinite language of `CFT/Profinite/`, is now a theorem.
The tower, bottom to top:

1. **`Profinite/Transgression.lean`** (`73f68ec`, strengthened in `d07b7fd`) — the raw descent.  A
   smooth two cocycle `a` whose restriction to `π.ker` is the coboundary of a smooth `b` is
   corrected by four successive twists into a cocycle inflated from the quotient, provided the
   transgression of the twisted cocycle is the coboundary of a smooth homomorphism.  Each correction
   is built by decomposing an element along its coset, so smoothness survives, but the order matters:
   the last two corrections need an open normal subgroup cut out by the trivialisation the first two
   produce.  `exists_comapH2_eq_of_locally_coboundary` packages this with the local input in the form
   `smoothH2Mk_mem_sha2` delivers, and `exists_comapH2_eq_of_mem_sha2` is then a one-liner.
2. **`Profinite/H1Conj.lean`** (`c7faa77`) — the conjugation action of the ambient group on
   `SmoothH1 ↥N M` for `N` normal, with the subgroup acting trivially, so it is an action of the
   quotient.  **This retires gotcha 1356**, which said no such action existed.
3. **`Profinite/TransgressionClass.lean`** (`b9bd14d`) — `IsTransgressionDatum`, the four conditions
   a transgression satisfies, and `transClass`, the class in `SmoothH1 G (SmoothH1 ↥N M)` they
   define.  `transClass_eq_one_iff` is the equivalence with trivialisation by a smooth homomorphism;
   the hard direction needs the trivialising homomorphism on the kernel to be extendable smoothly to
   the whole group, which is why `HasOpenNormalBasis` (true for compact groups) appears.
4. **`Profinite/TransgressionRestrict.lean`** (`6ed5e84`, `782d566`) — the local side.  A
   transgression restricted to a subgroup `D` in both variables is a transgression for
   `N.subgroupOf D`, hence has a class `localTransClass` of its own; the localisation homomorphism
   `resCoeffH1` restricts a class to `D` and its coefficients to `N ⊓ D` at the same time; and
   `resCoeffH1 (transClass h) = localTransClass h D` is `rfl`.  The everywhere locally trivial
   classes of that localised system are `sha1Loc`, and the capstone is

   >  `exists_comapH2_eq_of_sha1Loc_eq_bot` — a class of `H²(G,M)` which is locally trivial on a
   >  family `S` and dies on `π.ker` is inflated from the discrete quotient, as soon as
   >  `sha1Loc M π.ker S = ⊥`.

### (b) A correction to §1.00(b) item 5: which `Ш¹` it is

Item 5 was written as `Ш¹(G, H¹(K,E))` with the localisation `H¹(G_v, H¹(K,E))` — the *same*
coefficients restricted.  That is **not** what local triviality of the class supplies.  The
transgression is functorial in the whole extension: for `D ≤ G_k` with image `D̄` in `G`,

>  `H²(G_k,M)₁ --tg--> H¹(G, H¹(N,M))`
>  `      | res_D                | res_{D̄} then localise the coefficients`
>  `H²(D,M)₁  --tg--> H¹(D̄, H¹(D ⊓ N, M))`

so `res_D α = 0` only forces the image of `tg α` in `H¹(D̄, H¹(D ⊓ N, M))` to vanish — the
coefficients are localised along with the class.  This is strictly weaker than the naive reading, so
the theorem obtained is strictly stronger, and it is also the *correct* target: the arithmetic
`Ш¹(G, K^× ⊗ W)` of step 3 is defined as `ker( H¹(G, K^×⊗W) → H¹(G, I_K⊗W) )`, and Shapiro turns the
right-hand side into `⊕_v H¹(D_w, K_w^×⊗W)` — the coefficients localised.  The two match.

### (c) What is left for brick 5's arithmetic side

`sha1Loc M π.ker S` lives in `SmoothH1 G_k (SmoothH1 G_K M)` while the arithmetic `Ш¹` lives in
`H¹(Gal(K/k), –)`.  Two elementary steps bridge them, neither yet written:

1. **Inflation.** `G_K` acts trivially on `SmoothH1 G_K M` (`conjH1_eq_self_of_mem`), so the
   transgression cochain factors through `Gal(K/k)` and the class is inflated; inflation is
   injective in degree one (`Profinite/Quotient.lean`), so `sha1Loc = ⊥` follows from the
   finite-level statement plus compatibility of the localisations.
2. **Brick 4**, unchanged: `SmoothH1 G_K E ≅ K^× ⊗ W` as `Gal(K/k)`-modules, with
   `SmoothH1 G_{K_w} E ≅ K_w^× ⊗ W` compatibly.  `Profinite/KummerConj.lean` (`565db26`, `a1c110a`)
   already carries the equivariance half; the twist half collapses once §1.00(g)'s reduction to
   `μ_p ⊆ k` is done.

### (d) Lean notes

* `transClass_eq_one`'s smoothness hypothesis was weakened from `IsSmooth₁ φ` to
  `IsSmooth₁ (fun x : ↥N => φ ↑x)` — the proof only ever used the latter.  Callers supply
  `isSmooth₁_comp (continuous_subtype N) hφs`.  (gotcha 1418)
* `isSmooth₁_comp` (`Profinite/Res.lean`) needs an explicit `rw [map_mul f x n]`: `f (x*n) = f x * f n`
  is defeq only for a `MonoidHom.mk'` built with an `rfl` proof, not for a general `MonoidHom`.
  (gotcha 1419)
* `abel` treats `Additive.ofMul 1` as an atom, so the `Additive.ofMul.injective; simp only [...];
  abel` idiom must include `ofMul_one` whenever a literal `1` can appear (e.g. from `1 / a`).
  (gotcha 1413)
* `Subgroup.normal_subgroupOf` and `Subgroup.instMulDistribMulAction` are both instances, and the
  subgroup action is `SMul.comp` along the coercion, so `(σ : ↥D) • m` is *definitionally*
  `(↑σ : G) • m`.  That is why `resSubH1_smul` and `resCoeffH1_transClass` are both `rfl`.
  (gotcha 1421)
* `Profinite/Coeff.lean` is **not** reachable from `Profinite/TransgressionClass.lean`; a module
  wanting `coeffH1` must import it explicitly.  (gotcha 1422)

---

## 1.04 Status (2026-09-05, latest) — the transgression is always inflated, so its local conditions are a group of the *finite* quotient

### (a) What landed

Commit `3fc2890`, `InverseGalois/CFT/Profinite/TransgressionInflate.lean`.  Full root build **9692
jobs**, 0 warnings, 0 errors, 0 sorries.

This is item 1 of §1.03(c), the inflation half of brick 5's arithmetic side.

1. **The transgression is trivial on the kernel.**  `IsTransgressionDatum.apply_one` reads the
   cocycle condition at `σ = τ = 1` and `x ∈ N`: it says `t 1 x = t 1 x * t 1 x`, so `t 1 x = 1`.
   With the left-invariance condition `t (n σ) x = t σ x` for `n ∈ N` this gives
   `IsTransgressionDatum.apply_eq_one_of_mem`: `t n x = 1` for all `n, x ∈ N`.  Hence
   `transCochain_eq_one_of_mem` — the transgression cochain is identically `1` on `N`.
2. **So the transgression class is inflated.**  `N` acts trivially on `SmoothH1 ↥N M`
   (`conjH1_eq_self_of_mem`, made an instance `actsTrivially_smoothH1`), and a smooth cocycle that
   is trivial on an open normal subgroup on which the coefficients are fixed is inflated
   (`exists_inflH1_eq`, `Profinite/Quotient.lean`).  `exists_inflH1_transClass` therefore produces
   `x : SmoothH1 (G ⧸ N) (SmoothH1 ↥N M)` with `inflH1 x = transClass h`.
3. **Localising an inflated class is inflating its localisation.**  With
   `quotSubHom : ↥D ⧸ N.subgroupOf D →* G ⧸ N` and the coefficient map `resSubH1 N D`, the
   composite `resCoeffQuotH1 N D` is defined on the quotient groups alone, and

   >  `resCoeffH1 N D ∘ inflH1 N = inflH1 (N.subgroupOf D) ∘ resCoeffQuotH1 N D`

   is **`rfl`** once the class is written as `smoothH1Mk` of a cocycle.  Since inflation is
   injective in degree one, `resCoeffH1 N D (inflH1 x) = 1 ↔ resCoeffQuotH1 N D x = 1`.
4. **The hypothesis is now a group of the quotient.**  `sha1Level M N hop S` is the subgroup of
   `SmoothH1 (G ⧸ N) (SmoothH1 ↥N M)` cut out by the localisations, and `sha1Level_eq` presents it
   as `⨅ D ∈ S, (resCoeffQuotH1 N D hop).ker`.  For `G = G_k`, `N = G_K` this is literally
   `Ш¹(Gal(K/k), H¹(G_K, M))` with the coefficients localised at each `D`, exactly the group
   §1.03(b) identified.  The capstone `exists_comapH2_eq_of_sha1Level_eq_bot` is the descent
   theorem conditioned on it, and `transClass_eq_one_of_sha1Level` the step that consumes it.

### (b) What is left of brick 5's arithmetic side

Only brick 4, unchanged in substance: `SmoothH1 G_K E ≅ K^× ⊗ W` as `Gal(K/k)`-modules, with
`SmoothH1 G_{K_w} E ≅ K_w^× ⊗ W` compatibly with `resSubH1`.  Two sub-bridges:

1. **The language bridge.**  `sha1Level` lives in `SmoothH1` of the *discrete* group `G_k ⧸ G_K`,
   while `Ш¹(Gal(K/k), K^×⊗W)` lives in `tateModule … 1 = groupCohomology … 1`.  On a discrete group
   the smoothness condition is empty, so the two cohomologies agree; this is
   `Profinite/Discrete.lean`.
2. **The coefficient bridge**, which is brick 4 proper: Kummer plus the twist.  The equivariance
   half is `Profinite/KummerConj.lean`; the twist is
   `Hom_{cont}(G_K, μ_p) ⊗_{𝔽_p} W ≅ Hom_{cont}(G_K, μ_p ⊗ W)`, an isomorphism because `W` is a
   finite-dimensional `𝔽_p`-vector space, checked on a basis (the map itself is natural, so the
   basis does not survive into the statement).  Note that the twist does **not** need `μ_p ⊆ k`:
   the map `a ⊗ w ↦ (x ↦ w(x α / α))`, `α^p = a`, is `Gal(K/k)`-equivariant for the diagonal action
   on `K^× ⊗ Hom(μ_p, E)` as it stands.  §1.00(g)'s reduction remains available but is not a
   prerequisite.

### (c) Lean notes

* `IsTransgressionDatum` forces `t 1 x = 1` for `x ∈ N`: the cocycle condition at `σ = τ = 1` gives
  `a = a * a`, closed by `left_eq_mul.1`.  (gotcha 1429)
* `refine ⟨fun h => lemma _ _ _ ?_, …⟩` is illegal when the `?_` needs the lambda-bound `h` — the
  metavariable is created outside the lambda.  Symptom: two errors, *don't know how to synthesize
  placeholder* and *unsolved goals* listing a goal without `h`.  Use `constructor` and `intro h`
  bullets.  (gotcha 1430)
* `resCoeffH1 N D (inflH1 N A hop x) = inflH1 (N.subgroupOf D) A_D _ (resCoeffQuotH1 N D hop x)` is
  `rfl` after `obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x`: `comapH1` and `coeffH1` compose
  definitionally on `smoothH1Mk`.  (gotcha 1431)
* `waitbuild.sh` may not create its log file at all while waiting for memory; a missing log is not
  an error.  (gotcha 1433)

---

## 1.05 Status (2026-09-05, latest) — **brick 4's construction side is built**: the first cohomology of the subgroup fixing a field *is* the units tensor the homomorphisms of the roots of unity, equivariantly and compatibly with restriction

### (a) What landed

Seven modules under `InverseGalois/CFT/Profinite/`, none of them previously recorded here.  Commits
`f1d3382` (`TwistRes`, `KummerTower`) and the present one (`TwistTensor`, plus the tensor-level
additions to `KummerTwist`); the first four landed with the profinite Kummer group.  Full root build
**9700 jobs**, 0 warnings, 0 errors, 0 sorries.

This is brick 4 of §1.04(b), the coefficient bridge, on its construction side.  The target is

>  `SmoothH1 G_K E ≅ K^× ⊗_ℤ Hom(μ_p, E)` as `Gal(K/k)`-modules,
>  compatibly with restriction to a decomposition subgroup.

The route is not "compose four isomorphisms" (the abandoned plan of gotcha 1445) but **build the
map directly and characterise it**, which is why every statement below is an equation between two
maps rather than a diagram chase.

1. **`Pi.lean` — the algebra of coefficient maps.**  A homomorphism of the coefficients induces a
   map of first cohomologies by postcomposing a cocycle (`coeffH1`); when the coefficients are acted
   on trivially this is functorial in the coefficients, so `coeffH1End` makes the endomorphisms of
   the coefficient group act on the cohomology, and `smoothH1PiHom` compares the cohomology of a
   product of coefficient groups with the product of the cohomologies.
2. **`Twist.lean` — the twist itself.**  Given a class `κ a ∈ H¹(G, M)` provided by an element `a`
   of a base group and a homomorphism `w : M →* E` of the coefficients, `twistClass κ a w` is
   `coeffH1 w (κ a)`.  It is bimultiplicative, hence `twistMap` out of
   `Additive A ⊗[ℤ] Additive (M →* E)`; and when `M` is cyclic, `E` is killed by `p`, `κ` is
   surjective with kernel the `p`-th powers and `E ≅ ∏ M`, `twistEquiv` upgrades `twistMap` to an
   isomorphism.  The coordinates `twistCoord` are what invert it.
3. **`TwistConj.lean` — equivariance on a pure tensor.**  The first cohomology of a *normal*
   subgroup `N ◁ G` carries the conjugation action of `G`, and for `coeffH1` to commute with it the
   homomorphism of the coefficients must move too: `homSMul σ w = σ ∘ w ∘ σ⁻¹`.  This is an action
   (`homMulDistribMulAction`), `conjH1_coeffH1` is the commutation, and `conjH1_twistClass` is the
   equivariance of the twist on a pure tensor, conditional on the classes the base group provides
   being equivariant (`hκ : conjH1 σ (κ a) = κ (ρ σ a)`).
4. **`KummerTwist.lean` — the arithmetic instance.**  For `K` an intermediate field of a Galois
   `Ω/k`, `kummerSubHom` is surjective with the `p`-th powers as kernel, which is exactly the datum
   `twistEquiv` consumes, so

   >  `kummerTwistEquiv : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E) ≃+ Additive (SmoothH1 ↥K.fixingSubgroup E)`.

   `conjH1_kummerTwistClass` is its `Gal(Ω/k)`-equivariance on a pure tensor, obtained from
   `conjH1_kummerSubHom` with `ρ σ = AlgEquiv.restrictNormalHom ↥K σ • ·`.
5. **`TwistRes.lean` — naturality in the group.**  A homomorphism `π` of base groups induces
   `comapH1` by precomposing a cocycle, `coeffH1` by postcomposing; `comapH1_coeffH1` says **the two
   compositions are equal on the nose** (both are `smoothH1Mk` of the same cochain).  Hence
   `comapH1_twistMap`: once the classes the base group provides are carried along by some
   `ν : A →* A'`, the whole twisting map is carried to the twisting map of the image, tensored with
   the identity on `M →* E`.  Two instances are packaged: `resInclH1` along an inclusion of
   subgroups, and `resSubH1 N D` for the part of `N` lying inside `D` — read on `G_k` with
   `N = G_K` and `D` a decomposition subgroup, that is **localisation at a place**.
6. **`KummerTower.lean` — naturality along a tower of fields.**  For `K ≤ L` the Kummer *cochain*
   of a unit `a ∈ (↥K)ˣ`, restricted to `L.fixingSubgroup`, is the Kummer cochain of `j a` read
   upstairs (`kummerSubCochain_tower`), because the cochain is *characterised* — the chosen `p`-th
   roots of `a` upstairs and downstairs are two roots of the same element of `Ω`, so they have the
   same coboundary — and so the two cochains agree *before* any class is taken.  Feeding this into
   `comapH1_twistMap` gives `resInclH1_kummerTwistEquiv`: **through the identification, restricting
   a class is including the units.**
7. **`TwistTensor.lean` — equivariance of the whole map.**  `homSMulHom σ` packages `homSMul σ` as
   an endomorphism of `M →* E`, and

   >  `conjH1 σ ∘ twistMap κ = twistMap κ ∘ (ρ σ ⊗ homSMulHom σ)`

   is `conjH1_twistMap`, by `TensorProduct.induction_on` off `conjH1_twistClass`.  For the action to
   be an action of the *quotient*, `N` must move both factors trivially; on the second factor that
   is automatic (`homSMul_eq_self_of_mem`: a subgroup acting trivially on source and target acts
   trivially on the homomorphisms between them).  On the arithmetic side `KummerTwist.lean` now
   carries `conjH1_kummerTwistMap` / `conjH1_kummerTwistEquiv` together with the two triviality
   facts `smul_units_eq_self_of_mem_fixingSubgroup` (an automorphism fixing `K` pointwise restricts
   to `1`, by `IntermediateField.restrictNormalHom_ker`) and
   `homSMul_eq_self_of_mem_fixingSubgroup`.

### (b) What is left of brick 4

Two items, both packaging rather than mathematics:

1. **Descend the action.**  Everything above is stated for `Gal(Ω/k)` acting through
   `K.fixingSubgroup`-triviality.  `Profinite/Quotient.lean` already has the general machinery —
   `class ActsTrivially N M`, `quotientAut N M : G ⧸ N →* MulAut M`,
   `instance quotientMulDistribMulAction`, `quotientMk_smul … = rfl`, `isSmoothAction_of_actsTrivially`
   — and `TransgressionInflate.lean:92` instantiates it for `SmoothH1 ↥N M`.  What is missing is only
   the *arithmetic* instantiation: `homMulDistribMulAction` is a `def`, not an `instance`, and the
   transport along `Gal(Ω/k) ⧸ K.fixingSubgroup ≃* Gal(↥K/k)` (which is
   `QuotientGroup.quotientKerEquivOfSurjective` applied to `AlgEquiv.restrictNormalHom`, its kernel
   being `IntermediateField.restrictNormalHom_ker`) has not been written down.  (gotcha 1467)
2. **The local `hν`.**  `resSubH1_twistClass` / `resSubH1_twistMap` are in place abstractly; the
   arithmetic hypothesis they still want is the identification of `↥(N.subgroupOf D)` — for
   `N = K.fixingSubgroup` and `D` a decomposition subgroup — with `↥L.fixingSubgroup` for
   `L = K ⊔ fixedField D`.  That needs `D` closed and the infinite Galois correspondence, plus the
   henselization-versus-completion comparison `(K ⊔ F)^× / p ≅ K_w^× / p`.

Then the language bridge of §1.04(b) item 1 (`Profinite/Discrete.lean`) carries the result into
`tateModule … 1` and it can feed `sha1Level`.

### (c) Strategic reconnaissance: the reciprocity wall is where it looked

A pass over `Units/NakayamaSpan.lean`, `Units/BaseTate.lean`, `Units/BaseFundamental.lean`,
`Units/GlobalTate.lean` and `Units/IdeleTorusShaTorsion.lean` settled three things about row 5, all
negative, and one about the shape of the endgame.

* **The sufficient conditions in `NakayamaSpan.lean` are not a proof route.**  Both
  `hasIdeleClassNakayamaSpan_of_isZero` and `_of_isZero_idele` ask a Tate group of the ideles to
  vanish, and it does not.  Take `k = ℚ`, `K = ℚ(i)`, `p = 2`, `G = P = ℤ/2`.  Then
  `I_K[2] = ⊕_w μ_2(K_w) = ⊕_v Ind_{G_v}^G ℤ/2`, and `Ĥ⁰(G_v, ℤ/2)` is `0` for split `v`
  (`G_v = 1`) but `ℤ/2` for non-split `v`.  So `Ĥ⁰(G, I_K[2]) = ⊕_{v \text{ non-split}} ℤ/2 ≠ 0`.
  The conditions are genuinely only sufficient.  (gotcha 1468)
* **No reformulation of the span escapes reciprocity.**  `range ι_* = ker δ` for the connecting map
  `δ : Ĥ^{n+2}(P, C ⊗ W) → Ĥ^{n+3}(P, K^× ⊗ W)`, so
  `range TN_P ⊔ range ι_* = ⊤ ⟺ range (δ ∘ TN_P) = range δ ⟺ Ш^{n+3}(P, K^× ⊗ W) = range shaTorusPTorsionMap`,
  which is row 5 itself.  The span is a restatement, not a reduction.  (gotcha 1469)
* **The structural blocker is `.choose`.**  `baseFundamentalClass k K` is
  `(exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_base k K).choose`, and it is built from
  `globalFundamentalClass`, itself `.choose` (`_of_rat` restricts, `_of_top` inflates, `_base` takes
  the normal closure over ℚ).  The global-versus-local comparison square that row 5 needs cannot be
  written against an opaque class; it wants the invariant-theoretic construction out of
  `localInvariantHom` plus Hasse reciprocity, i.e. the `CFT/Brauer/` tower.  That is the largest
  single remaining item in the whole file.  (gotcha 1118)
* **There are two independent hypothesis routes to all-solvable.**  `Main.lean:71`
  `isSolvable_isInverseGalois_of_splitPrimePowerEP` needs `SplitPrimePowerEP` *alone*, and
  `Generic.lean:256` `splitPrimePowerEP_of_genericSplitEP` reduces that to `∀ ℓ, GenericSplitEP ℓ`.
  The `FrattiniKernelEP` route is the other.  Brick 4 is needed on both, which is why it is the
  right thing to be building while the reciprocity tower is unaffordable.  (gotcha 1470)
* Note also that the `Units/` side's "everywhere locally trivial" is
  `ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) n)` — through the *ideles*, i.e. with
  localised coefficients by Shapiro, which is exactly the correction §1.03(b) made on the profinite
  side.  The two sides are asking the same question.  (gotcha 1471)

### (d) Lean notes

* The general machinery for a quotient action on `SmoothH1` already exists in
  `Profinite/Quotient.lean`; gotcha 1356 ("no arithmetic `Gal(K/k)`-action on `SmoothH1 G_K M`")
  means only that the arithmetic instantiation is missing.  (gotcha 1467)
* `TensorProduct.induction_on` naturality proofs want `simp only [map_zero]` and
  `simp only [map_add, hz, hz']`, never `rw`; the `tmul` case is
  `rw [TensorProduct.map_tmul]; exact congrArg Additive.ofMul (…)`, and `Additive.ofMul a` is
  definitionally `a`, so `x.toMul` closes the coercion gap.  (gotchas 1461, 1454)
* `MonoidHom.mk' (homSMul σ) (homSMul_mul σ)` is the whole of `homSMulHom`: `mk'` wants only
  `MulOneClass` on the source and `Group` on the target, and `M →* E` is a `CommGroup`.
* A statement mentioning `AlgEquiv.restrictNormalHom (↥K) σ • a` for `a : (↥K)ˣ` times out
  instance search at the default budget; it needs
  `set_option synthInstance.maxHeartbeats 400000` and `set_option maxHeartbeats 1000000`.
  (gotcha 1381, now also for `smul_units_eq_self_of_mem_fixingSubgroup`)
* `restrictNormalHom_eq_one_of_mem_fixingSubgroup` already exists, in `Brauer/SmoothLevel.lean:87`.
  A duplicate in `Profinite/` is not caught by `lake build <Module>` — it surfaces only at the root
  build, as *environment already contains …* on the `import` line of `InverseGalois/CFT.lean`.
  Grep the whole of `InverseGalois/` for a new name, not just the subdirectory.  (gotcha 1472)

---

## 1.06 Status (2026-09-05, latest) — the twisted Kummer identification descends to `Gal(K/k)`

Commit `719ac8b`, full root build green: **9703 jobs, 0 warnings, 0 errors, 0 sorries.**

### (a) What landed

Three new modules and two one-word promotions finish the "as `Gal(K/k)`-modules" half of brick 4.

* `Profinite/QuotientAction.lean` — the additive form of `Profinite/Quotient.lean`.  A new class
  `AddActsTrivially N T` (each element of `N` fixes every point of the `AddCommGroup` `T`) and, from
  it, `instance quotientDistribMulAction : DistribMulAction (G ⧸ N) T` built by lifting
  `DistribMulAction.toAddAut G T` through `QuotientGroup.lift`; `quotientAddMk_smul` is `rfl`.  This
  is needed because a tensor product is an additive group and there is no writing it otherwise,
  while the coefficients and their cohomology stay multiplicative.
* `Profinite/TwistAction.lean` — `instance tensorDistribMulAction : DistribMulAction G (Additive A
  ⊗[ℤ] Additive B)`, the *diagonal* action, built from `tensorSMulMap` (a `TensorProduct.map` of the
  two `MulDistribMulAction.toMonoidHom`s) with `tensorSMulMap_one` / `tensorSMulMap_comp` proved by
  `TensorProduct.ext'`.  Then `tensorSMul_eq_self_of_forall`, the instance
  `actsTrivially_tensor : [ActsTrivially N A] → [ActsTrivially N B] → AddActsTrivially N (Additive A
  ⊗[ℤ] Additive B)`, and `conjH1_twistMap_smul`, which is `conjH1_twistMap` with the tensor map
  replaced by `σ • z`.
* `Profinite/KummerAction.lean` — the arithmetic instantiation.
  `noncomputable instance restrictUnitsMulDistribMulAction : MulDistribMulAction Gal(Ω/k) ((↥K)ˣ)`
  is `MulDistribMulAction.compHom ((↥K)ˣ) (AlgEquiv.restrictNormalHom (↥K))` (so `σ • a` is
  *definitionally* `restrictNormalHom (↥K) σ • a`, and every earlier statement lines up on the
  nose); `instance actsTrivially_units` and the theorem `actsTrivially_hom` say the subgroup fixing
  the field moves neither factor; `conjH1_kummerTwistEquiv_smul` is the equivariance in action form;
  and **`kummerTwistEquiv_smul` is the payoff** —
  for `g : Gal(Ω/k) ⧸ K.fixingSubgroup`,
  `kummerTwistEquiv … (g • z) = Additive.ofMul (g • (kummerTwistEquiv … z).toMul)`,
  proved by `QuotientGroup.mk_surjective` and one `exact`, everything else being `rfl`.
* `Profinite/TwistConj.lean`: `homMulDistribMulAction` promoted from `def` to `instance`.
* `Profinite/Krull.lean`: `normal_fixingSubgroup` promoted from `theorem` to `instance`, so
  `K.fixingSubgroup.Normal` is now found by instance search (this retires gotcha 1380).  `Normal` is
  a `Prop`-valued class, so no diamond can bite; the full build confirms no regression.

### (b) The trap that shaped the design  (gotcha 1478 — MATH/Lean)

The first draft also declared `instance additiveDistribMulAction : DistribMulAction G (Additive M)`
from `MulDistribMulAction G M`, so that the *target* `Additive (SmoothH1 ↥N E)` would carry the
quotient action too.  **That instance silently destroys `tensorDistribMulAction`.**  With a
`G`-action on `Additive A` in scope, Mathlib's own `TensorProduct` left action
(`DistribMulAction R' (M ⊗[R] N)` for `R'` acting on the left factor) becomes applicable to
`Additive A ⊗[ℤ] Additive B`, and it is found *first*: `σ • x ⊗ₜ y` then means
`(σ • x) ⊗ₜ y`, not the diagonal `(σ • x) ⊗ₜ (σ • y)`.  The symptom is a `show` tactic failing on
what looks like a defeq goal, plus a `whnf` timeout.  The two actions are genuinely different, so
this is not a diamond to be papered over with priorities: the fix is to *not* give `Additive M` a
global `G`-action, and to write the target side as `Additive.ofMul (g • _.toMul)` instead.

The consequence for packaging: when the identification is finally read as an isomorphism of
`Rep ℤ Gal(K/k)`, the source must be built with `Rep.ofDistribMulAction ℤ Q _` out of
`tensorDistribMulAction`, and the target with `Rep.ofMulDistribMulAction Q (SmoothH1 ↥N E)` (whose
carrier is already `Additive` of the cohomology).  No `Additive`-valued action instance is needed
anywhere.

### (c) What is left of brick 4

1. **The `Rep` packaging.**  Assemble `kummerTwistEquiv` + `kummerTwistEquiv_smul` into an
   isomorphism in `Rep ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)`, then transport along
   `Gal(Ω/k) ⧸ K.fixingSubgroup ≃* Gal(↥K/k)` (this is
   `QuotientGroup.quotientKerEquivOfSurjective` applied to `AlgEquiv.restrictNormalHom (↥K)`, whose
   kernel is `IntermediateField.restrictNormalHom_ker`), and finally through
   `Profinite/Discrete.lean` into `groupCohomology` / `tateModule`, so that
   `Ш¹(Gal(K/k), K^× ⊗ W)` can be spoken about at the finite level.
2. **The remaining local step** — supply `hν` for the `resSubH1 N D` case: identify
   `↥(N.subgroupOf D)` (for `N = K.fixingSubgroup`, `D` a decomposition subgroup) with
   `↥L.fixingSubgroup` for `L = K ⊔ fixedField D`.  Needs `D` closed / the infinite Galois
   correspondence, plus `(K ⊔ F)^× / p ≅ K_w^× / p`.

### (d) Lean notes

* An `instance` whose body mentions `AlgEquiv.restrictNormalHom` must be `noncomputable`.
* Section variables used only in the *proof term* of a `theorem` are not auto-included (gotcha
  1289); `include hfix in` is required, and it goes *after* the `set_option … in` lines and *before*
  the docstring.
* `rw`'s closing `rfl` is reducible-transparency only: after `rw [one_smul, one_smul]` a goal
  `Additive.ofMul (Additive.toMul x) ⊗ₜ y = x ⊗ₜ y` is still open — add an explicit `rfl`
  (gotcha 1473).
* `MulDistribMulAction.compHom` / `DistribMulAction.compHom` are `abbrev`s taking the acted-on type
  explicitly (gotcha 1476); `DistribMulAction.toAddAut G T` and `AddAut.applyDistribMulAction` are
  the additive counterparts of `MulDistribMulAction.toMulAut` used in `Profinite/Quotient.lean`.
* `Units/InfiniteTowerDescent.lean` takes ~1000 s in a full build — after
  `Units/CompositumFundamental.lean` it is the second most expensive module in the CFT tree.

---

## 1.07 Status (2026-09-05, latest) — the Kummer tower no longer needs the intermediate field to be finite over the base

Full root build green: **9703 jobs, 0 warnings, 0 errors, 0 sorries.**

### (a) Why this was blocking

The remaining local step of brick 4 (§1.06(c) item 2) localises a class at a place.  On the profinite
side a place is a *decomposition subgroup* `D ≤ Gal(Ω/k)`, and the field it corresponds to is
`F = fixedField D`.  The identification to be proved reads the part of `N = K.fixingSubgroup` lying
inside `D` as the subgroup fixing the compositum `L = K ⊔ F`.

The first attempt tried to run this over the base `k`.  It cannot be: `L` is normal over `F` (because
`K` is normal over `k`, so `K ⊔ F` is normal over `F`), but **not** over `k`, and the localised
coefficients carry an action of `↥D ⧸ (N ⊓ D) ≅ Gal(L/F)`.  So the whole Kummer/twist tower has to be
usable with `F` as the base field — and `F/k` is infinite, being the fixed field of a decomposition
subgroup.  Every module in that tower carried `[FiniteDimensional k ↥K]`.  (gotcha 1491)

### (b) The hypothesis was consumed in exactly two places

Both are in `Profinite/FixingSubgroup.lean`, the only place in the repo where the Krull topology of
`Gal(Ω/↥K)` is compared with the subspace topology on `K.fixingSubgroup ≤ Gal(Ω/k)`.  Both used
finiteness only to move a finite extension across the intermediate field, and both can instead use
that *a finite extension is generated by a finite set of elements, each integral over the base*:

* `continuous_galSubHom`.  Given `F/k` finite, take a finite generating set `t` with
  `adjoin k t = F`; then `E := adjoin ↥K t` is finite over `↥K` because each generator is integral
  over `k`, hence over `↥K` (`IsIntegral.tower_top`).  An automorphism fixing `E` fixes `F`, because
  `restrictScalars k E = K ⊔ adjoin k t ⊇ F`.
* `isSmoothHom_fixingSubgroupEquiv`.  Given `E/↥K` finite, take a finite generating set `t` with
  `adjoin ↥K t = E`; then `E₀ := adjoin k t` is finite over `k`, and the open subgroup
  `E'.fixingSubgroup ∩ K.fixingSubgroup` (for `E'` a finite *normal* extension inside
  `E₀.fixingSubgroup`) maps into `E.fixingSubgroup`.

The finite generating set comes from `IntermediateField.essFiniteType_iff.1 inferInstance : F.FG`
(gotcha 1486): `Algebra.EssFiniteType.of_finiteType` is an instance, so a finitely generated
intermediate field is available from `FiniteDimensional` with no work.

The removal then propagates with no further proof changes to `Profinite/KummerConj.lean`,
`Profinite/KummerTwist.lean`, `Profinite/KummerTower.lean` and `Profinite/KummerAction.lean` — the
Kummer statements never used finiteness, only the two topological facts above.

### (c) Lean notes

* `IntermediateField.restrictScalars_adjoin_eq_sup` needs the base named explicitly,
  `restrictScalars_adjoin_eq_sup (F := k) K S`; otherwise Lean infers `F := ↥K` and reports a type
  mismatch.  (gotcha 1487)
* For `IntermediateField`, `le_sup_right hx` fails to elaborate ("Function expected at
  `le_sup_right`").  Hoist the membership into a `have` and write
  `SetLike.le_def.mp le_sup_right hxt`.  (gotcha 1488)
* To show a subgroup lands inside `(adjoin F S).fixingSubgroup`, use the Galois connection rather
  than working element by element: `rw [← IntermediateField.le_iff_le, ← ht]` then
  `IntermediateField.adjoin_le_iff.2` and `IntermediateField.mem_fixedField_iff`.  (gotcha 1489)
* Mathlib v4.28 has **no** lemma comparing the Krull topology of `Gal(Ω/L)` with the subspace
  topology on `L.fixingSubgroup`; `Profinite/FixingSubgroup.lean` is the only source.  The Mathlib
  bricks that do exist and are used here are `IntermediateField.fixingSubgroup_sup`
  (`Galois/Basic.lean:261`), `le_iff_le` (:232), `mem_fixedField_iff` (:213), `fixingSubgroupEquiv`
  (:268), `InfiniteGalois.fixingSubgroup_fixedField` (`Galois/Infinite.lean:144`) and
  `finiteDimensional_adjoin` (`Adjoin/Basic.lean:569`).  (gotcha 1490)

---

## 1.08 Status (2026-09-05, latest) — **brick 4 is built on both sides**: the localisation of a Kummer class at a place, and the identification read in the category of representations

Commits `39ef23b` (`Profinite/KummerLocal.lean`) and the present one (`Profinite/KummerRep.lean`).

### (a) The local step (§1.06(c) item 2)

`Profinite/KummerLocal.lean`.  Localising a class of `N = K.fixingSubgroup` at a place `D` means
`resSubH1 N D`, whose target is the first cohomology of `↥(N.subgroupOf D)`.  The module identifies
that with the subgroup fixing the compositum, in three moves.

* `interEquiv N D hH : ↥(N.subgroupOf D) ≃* ↥H` for any `H` with `g ∈ H ↔ g ∈ N ∧ g ∈ D`.  Both
  sides are elements of the big group lying in both subgroups, and both carry the topology induced
  from it, so the identification and its inverse are continuous (`continuous_induced_rng` twice) and
  it is a smooth homomorphism.  `comapInterH1` is the map it induces in the first cohomology.
* `resSubH1_eq_comapInterH1 : resSubH1 N D z = comapInterH1 N D hH (resInclH1 hle z)`.  Both sides
  substitute the same element of the big group into the cocycle, so after
  `obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z` the goal is closed by a bare `rfl`.
* `mem_fixingSubgroup_sup_iff` (`fixingSubgroup_sup` + `Subgroup.mem_inf`) and
  `fixingSubgroup_fixedField_of_isClosed` (`InfiniteGalois.fixingSubgroup_fixedField ⟨D, hD⟩`)
  supply the hypothesis `hH` for `H = (K ⊔ fixedField D).fixingSubgroup`.

The two payoffs are `resSubH1_kummerSubHom_sup` and `resSubH1_kummerTwistEquiv_sup`: **localising a
Kummer class at a place is including the units of `K` into the units of `K ⊔ fixedField D`**, and
the same through the twisted identification.  Routing through `resInclH1` and reusing
`resInclH1_kummerSubHom` / `resInclH1_kummerTwistEquiv` from `KummerTower.lean` avoids all
`TensorProduct.map … LinearMap.id` bookkeeping.  Note the design choice: the Kummer data `hL` for
the compositum is a *hypothesis*, exactly as in `KummerTower.lean`; constructing it from `hK` would
need "the `p`-th roots of unity in `K ⊔ F` are those in `K`", which is a separate arithmetic fact
and not what this module is about.

Still open on the local side, and needed only where the profinite side meets the idelic one:
`(K ⊔ F)^× / p ≅ K_w^× / p`, the henselization-versus-completion comparison.

### (b) The `Rep` packaging (§1.06(c) item 1)

`Profinite/KummerRep.lean`.  Two generic bricks and their arithmetic instantiation.

* `repIsoOfAddEquiv Q S T e he : Rep.ofDistribMulAction ℤ Q T ≅ Rep.ofMulDistribMulAction Q S`, for
  `e : T ≃+ Additive S` with `e (g • t) = Additive.ofMul (g • (e t).toMul)`.  One line:
  `Action.mkIso e.toIntLinearEquiv.toModuleIso fun g => ModuleCat.hom_ext (LinearMap.ext …)`.  Both
  directions are `rfl` on elements (`repIsoOfAddEquiv_hom_apply`, `_inv_apply`).
* `smoothH1EquivOfAddEquiv : SmoothH1 Q S ≃* Multiplicative ↥(H1 (Rep.ofDistribMulAction ℤ Q T))`
  for discrete `Q`, being `discreteSmoothH1Equiv` followed by
  `(groupCohomology.functor ℤ Q 1).mapIso` of the above, read as an `AddEquiv` through
  `Iso.toLinearEquiv` and wrapped by `AddEquiv.toMultiplicative`.
* `kummerRepIso` and `kummerSmoothH1Equiv` instantiate them at `Q = Gal(Ω/k) ⧸ K.fixingSubgroup`,
  `S = SmoothH1 ↥K.fixingSubgroup E`, `T = Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)`, with `he` being
  exactly `kummerTwistEquiv_smul` from `KummerAction.lean` and the discreteness of `Q` coming from
  `QuotientGroup.discreteTopology hop`.
* `kummerSha1` is `sha1Level E K.fixingSubgroup hop S` carried across, and `sha1Level_eq_bot_iff`
  says **the two readings vanish together**.  That is the sentence the local-global input to
  `exists_comapH2_eq_of_sha1Level_eq_bot` has to be proved in: a statement about
  `H¹` of a *finite* group with coefficients in `K^× ⊗ Hom(μ_p, E)`.

What is deliberately *not* done: presenting the finite group as `K ≃ₐ[k] K` rather than as
`Gal(Ω/k) ⧸ K.fixingSubgroup`.  The two are isomorphic (`QuotientGroup.quotientKerEquivOfSurjective`
of `AlgEquiv.restrictNormalHom ↥K`), but transporting the *action* onto `(↥K)ˣ` along that iso would
put a second `Gal(↥K/k)`-action on the units beside the natural one, which is the diamond the
development already refused once.  The clean route is invariance of `groupCohomology` under a group
isomorphism, via `Action.res` — a separate, reusable brick, and Mathlib v4.28 has no such lemma
(`Functoriality.lean` has `congr` only for two *equal* homomorphisms).  It is wanted only when the
`Units/` side actually consumes the group, so it is deferred rather than guessed at.

### (c) Lean notes

* `smoothH1Mk_congr rfl _ _ _ _` frequently cannot synthesize its implicit cochain arguments when
  the two sides are only definitionally equal; a bare `rfl` does the job.  (gotcha 1492)
* `InfiniteGalois.fixingSubgroup_fixedField` takes a bundled `ClosedSubgroup`; `⟨D, hD⟩` with
  `hD : IsClosed (D : Set G)` is the anonymous constructor.  (gotcha 1494)
* `Rep.ofMulDistribMulAction (M G : Type)` and the repo's `discreteSmoothH1Equiv (G M : Type)` are
  both `Type 0`-only, so the whole packaging section is stated with `k Ω M E J : Type`.
* `Rep.ofDistribMulAction ℤ Q T` needs `SMulCommClass Q ℤ T`; it is found automatically from
  `DistribMulAction Q T` on an `AddCommGroup`.
* The doc heading convention in this file is `## 1.0N Status (…)` with no `§`.  (gotcha 1495)

---

## 1.09 Status (2026-09-05, latest) — brick 4 now speaks the language of `Units/`: the level group is `Gal(K/k)`, not a quotient

`Profinite/KummerFinite.lean`; full root build **9706 jobs**, 0 warnings, 0 errors, 0 sorries.

### (a) The deferred brick of §1.08(b) was already in the repository — correction

§1.08(b) says the invariance of `groupCohomology` under an isomorphism of groups is "a separate,
reusable brick, and Mathlib v4.28 has no such lemma".  The second half is true of *Mathlib*
(`Functoriality.lean`'s `congr` compares two **equal** homomorphisms) but false of the repository:
`TateCohomology/GroupCongr.lean`, namespace `InverseGalois.CFT.Tate`, has had the whole brick since
the Tate–Nakayama tower was built:

```
bijective_cochainsMap_f     isIso_cochainsMap_of_bijective
groupCohomologyCongr (e : G ≃* G') (φ : (Action.res _ ↑e).obj A ⟶ B) (hφ : Bijective ⇑φ.hom.hom) (n)
  : groupCohomology A n ≅ groupCohomology B n
groupCohomologyCongr_hom (= groupCohomology.map ↑e φ n, by rfl)
groupCohomologyResCongr    tateModuleCongrSucc    tateOneCongr    tateTwoCongr
```

universe-polymorphic in `{k G G' : Type u}`.  The mandatory grep-before-writing rule caught the
duplicate before it was written.  (gotcha 1499)

### (b) What the new module does

The level group is presented twice: `Gal(Ω/k) ⧸ K.fixingSubgroup`, which is what inflation of a
cochain produces, and `Gal(↥K/k)`, which is what `Units/` computes with (`globalUnitsRep k K`,
`tensorObj … W`, `HasIdeleClassNakayamaSpan`).  `Profinite/KummerFinite.lean` identifies them and
carries the twisted Kummer statement across.

* `repIsoOfEquivSmul e B φ hφ : (Action.res _ ↑e).obj B ≅ Rep.ofDistribMulAction ℤ G T`, for
  `e : G ≃* G'`, `B : Rep ℤ G'`, `φ : T ≃+ ↥B.V` and
  `hφ : ∀ g t, φ (g • t) = B.ρ (e g) (φ t)`.  Same one-liner as `repIsoOfAddEquiv`, with `φ.symm`
  in place of `φ` because the restricted representation is the *source*.
* `groupCohomologyEquivOfSmul` = `Tate.groupCohomologyCongr` of that, in every degree;
  `h1MulEquivOfSmul` is degree one wrapped in `Multiplicative` so that it composes with
  `smoothH1EquivOfAddEquiv`.
* `quotientFixingSubgroupEquiv K : Gal(Ω/k) ⧸ K.fixingSubgroup ≃* Gal(↥K/k)`, being
  `QuotientGroup.liftEquiv _ (restrictNormalHom_surjective_level K)
  (IntermediateField.restrictNormalHom_ker K).symm`; `quotientFixingSubgroupEquiv_mk` is `rfl`.
* `kummerFiniteH1Equiv` composes `kummerSmoothH1Equiv` with `h1MulEquivOfSmul`, giving
  **`SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E) ≃* Multiplicative ↥(H1 B)`**
  for *any* `B : Rep ℤ Gal(↥K/k)` together with an intertwiner
  `φ : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E) ≃+ ↥B.V`.  `kummerFiniteSha1` carries `sha1Level`
  along it and `sha1Level_eq_bot_iff_finite` says the two readings vanish together.

Taking `B` as a parameter rather than constructing it is what keeps §1.08(b)'s diamond away: no
second `Gal(↥K/k)`-action is ever put on `(↥K)ˣ`.  The consumer supplies
`B = tensorObj (globalUnitsRep k ↥K) W` with `W` the representation on `Additive (M →* E)`, and
proves `hφ` — which, by `restrictUnits_smul` (`rfl`) and `quotientFixingSubgroupEquiv_mk` (`rfl`),
is an equality of the two *definitionally identical* actions on the left tensor factor.

### (c) The chain as it now stands

>  `Ĥ^{-2}(G, W)  ↠  Ш¹_{idelic}(G, K^× ⊗ W)`  — brick 3, conditional on the span
>  `Ш¹(G, K^× ⊗ W) ≅ sha1Level`                — brick 4, **done** (§1.05–§1.08 + this module)
>  `sha1Level = ⊥  ⇒  Ш²(k,E) ⊆ inf`           — brick 5, **done** (§1.03–§1.04)
>  `Ĥ^{-2}(G, W) = 0` after shrinking `G`      — Prop 6, **done** (`Shafarevich/Shrink.lean`)

with `W = E(-1) = Hom(μ_p, E)`.  So the surjection chain closes as soon as the two Ш's are the
same group, i.e. as soon as **"trivial on every decomposition subgroup" and "trivial in the ideles"
agree**.  That is the one comparison §1.08(a) already flagged: `(K ⊔ F)^× / p ≅ K_w^× / p`,
henselization versus completion, together with Shapiro for `Ĥ^*(G, I_K ⊗ W)`.  It is now the *only*
thing between the profinite tower and the idelic one, and it is arithmetic rather than formal.

### (d) Lean notes

* `Rep.ofDistribMulAction ℤ G T` and `Tate.groupCohomologyCongr` compose without any universe
  gymnastics as long as everything is `Type` (i.e. `Type 0`), which the packaging already was.
* `Action.mkIso`'s `comm` obligation, applied to an element, reads `f (M.ρ g x) = N.ρ g (f x)`:
  source action first, then the map.  With `f = φ.symm` the proof is
  `rw [φ.apply_symm_apply] at hb; show …; rw [← hb, φ.symm_apply_apply]`.
* `Function.Bijective ⇑(iso).hom.hom.hom` — three `.hom`s for an `Iso` in `Rep` (Iso, `Action.Hom`,
  `ModuleCat.Hom`), where `groupCohomologyCongr`'s hypothesis takes two for a bare morphism.  It is
  closed by `φ.symm.bijective`.
* `QuotientGroup.liftEquiv (hφ : Surjective φ) (HN : N = φ.ker) : G ⧸ N ≃* H`, with `liftEquiv_coe`
  a `simp` lemma and `rfl`; Mathlib's `InfiniteGalois.normalAutEquivQuotient` is the same
  construction but phrased through `fixedField H`, so it is not directly usable here.

---

## 1.10 Status (2026-09-05, latest) — **gap (ii-b) is closed**: the twisted cohomology of the ideles in degree one injects into that of the full product of the local unit groups

New modules `Tate/FamilyTrunc.lean`, `Tate/LiftInvariants.lean`, `Tate/FamilyInvariant.lean`,
`Tate/FamilyTensorFinsupp.lean`, `Units/InvariantUniformizer.lean`,
`Units/IdeleValuationSplit.lean`, `Units/IdeleFullCompare.lean`; `Tate/FamilyConst.lean` rewritten
around the constant family (the old Shapiro-for-permutation-modules content of that file was dead
code and is gone; its two orbit/stabiliser helpers moved to `Tate/FamilyOrbits.lean`).

### (a) The statement

`Units/IdeleFullCompare.lean`:

```
injective_tateMap_one_tensor_ideleToFullIdele
  (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p)) :
  Function.Injective (Tate.tateMap (tensorHomLeft W (ideleToFullIdele k K)) 1)
```

`Ĥ¹(G, I_K ⊗ W) ↪ Ĥ¹(G, ∏_v K_v^× ⊗ W)`, for a finite Galois group and coefficients of finite rank
over `𝔽_p`.  Composed with the Shapiro decomposition of the *full* product
(`Units/IdeleTensorOrbit.lean`, `Tate/FamilyTensorFull.lean`) this says **`Ш_dec ⊆ Ш_idelic`**: a
class trivial on every decomposition subgroup is trivial in the whole product, hence already
trivial in the restricted product.  The reverse inclusion `Ш_idelic ⊆ Ш_dec` is gotcha 1514 and was
already available, so the two Ш's of §1.09(c) are the same group *modulo* the henselization-vs-
completion comparison, which is gap (ii-a) and is untouched.

### (b) Route A, as built

The obstruction was that `I_K ⊆ ∏_v K_v^×` is not a `G`-retract (gotcha 1589) and the quotient is
not cohomologically trivial (gotcha 1538), so nothing formal gives injectivity.  What does give it
is a *lifting of invariants* in degree zero:

>  `Ĥ⁰` is invariants-modulo-norms, so a map along which every invariant of the target lifts to an
>  invariant of the source is surjective there (`Tate.surjective_tateMap_zero_of_lift`); in a short
>  exact sequence a degree in which the quotient map is surjective is a degree out of which the
>  connecting map vanishes, so the inclusion of the sub is injective one degree up
>  (`Tate.injective_tateMap_succ_of_surjective`).  Combined:
>  `Tate.injective_tateMap_one_of_lift_invariants`.

The lifting is supplied by the vector of valuations.  Write `V := fullIdeleVal : ∏_v K_v^× → ∏_v ℤ`
(`Units/IdeleValuationSplit.lean`), a map of representations onto the *permutation* module
`placeIntRep k K = orbitSectionsRep (constFamily (HeightOneSpectrum (𝓞 K)) ℤ Gal(K/k))`, whose
kernel-up-to-finite-support is exactly `idele K`.  A right inverse `S := valSection s` needs a
`G`-invariant family `s` of local units which are uniformizers at all but finitely many places;
`Units/InvariantUniformizer.lean` builds it from `Tate/FamilyInvariant.lean` (choose a value at one
index of each orbit fixed by the stabiliser there, transport around the orbit) plus the fact that
the decomposition group *is* the stabiliser and that only the places dividing the different fail to
carry a uniformizer fixed by it.

Then, for `a₀ ∈ (∏_v K_v^× ) ⊗ W` with all `g·a₀ − a₀ ∈ I_K ⊗ W`:

1. `V(a₀) ∈ (∏_v ℤ) ⊗ W` is moved by `G` only in finitely many places
   (`mem_finsuppTensor_of_mem_range`, using that `V` carries `I_K` into the finitely-supported
   sections);
2. `Tate/FamilyTensorFinsupp.lean`'s `exists_rho_invariant_sub_finsuppTensor` replaces it by an
   invariant `n'` differing in finitely many places only — this is `Tate/FamilyTrunc.lean`'s
   truncation on the finite invariant saturation, transported across the bijection
   `bijective_sectionsTensorMap_of_equivPi` (which needs no hypothesis on the family, only
   `e : ↥W.V ≃+ (Fin d → ZMod p)`);
3. `S(n')` is invariant, and `S(n') − a₀ = −S(V(a₀) − n') − (a₀ − S(V(a₀)))` lies in `I_K ⊗ W`,
   the first term by `valSectionHom_mem_range_of_finsuppTensor` and the second by
   `sub_valSectionHom_mem_range`.

The short exact sequence `0 → I_K → ∏_v K_v^× → Q → 0` survives tensoring with `W` even though `W`
is not flat, by `Tate.tensorSeq_shortExact_of_injective_modNsmul` plus
`injective_modNsmulHom_ideleToFullIdele` (the integers have no torsion, so the inclusion stays
injective mod `p`).

### (c) Lean notes

* **gotcha 1622 (elaboration, important).**  The `binop%` elaborator behind `-`/`+` **ignores type
  ascriptions** when computing the max type of the operands: writing
  `familyAut g X - (sectionsTensorMap … : ∀ _ : HeightOneSpectrum (𝓞 K), ℤ ⊗[ℤ] ↥W.V)` still fails
  with `failed to synthesize HSub …`.  The fix is never to hand-write a mixed-type subtraction —
  restructure so that the subtraction appears only in a goal *generated* by instantiating a lemma
  (goals produced by unification never go through `binop%`).  That is why
  `exists_rho_invariant_sub_finsuppTensor` exists as an abstract lemma at all.
* **gotcha 1623.**  For `⟨a - b, proof⟩` where `a - b` trips `HSub`, write `⟨_, proof⟩` and let the
  placeholder be inferred from the proof's type.
* **gotcha 1624.**  Prefer `refine LinearMap.mem_range.2 ⟨witness, ?_⟩` over building a
  `have hstep : LHS = RHS`: the `refine` route inherits the goal's already-fixed instances, whereas
  the `have` re-elaborates from scratch and hits `binop%`.
* **gotcha 1631 (elaboration, important).**  `exact Tate.injective_tateMap_one_of_lift_invariants
  hXT hlift` against the goal `Function.Injective (tateMap (tensorHomLeft W (ideleToFullIdele k K))
  1)` **times out at `isDefEq`** (>1M heartbeats, ~120 s) even though
  `(Tate.tensorSeq W (ideleFullShortComplex k K)).f = tensorHomLeft W (ideleToFullIdele k K)` is
  `rfl` *instantly* on its own, and even though the same `exact` against the goal stated with
  `(Tate.tensorSeq W …).f` succeeds instantly.  The unifier gets lost inside `tateMap` before it
  ever compares the morphism arguments.  **Fix:** bind the `rfl` as a `have` and rewrite the goal
  first —
  ```lean
  have hfeq : (Tate.tensorSeq W (ideleFullShortComplex k K)).f
      = tensorHomLeft W (ideleToFullIdele k K) := rfl
  rw [← hfeq]
  exact Tate.injective_tateMap_one_of_lift_invariants hXT hlift
  ```
  which runs in 0.7 s.  This is the operational form of gotcha 1612 ("never `rw` across the
  `tensorSeq`-vs-`tensorObj` defeq boundary — convert with a typed `have`").
* **gotcha 1632.**  `attribute [local reducible] Tate.tensorSeq` is **rejected** ("failed to set
  `[local reducible]` … affects the term indexing datastructures used by `simp` and type class
  resolution"), so the reducibility route to the same fix is not available.
* **gotcha 1633 (diagnosis recipe).**  To localise a whnf/isDefEq timeout, copy the theorem into
  `.scratch/`, stub its prerequisites with `sorry`, and put `set_option profiler true in` on it;
  the per-tactic breakdown names the culprit (`tactic execution of … exact took 119s`).  A scratch
  probe importing `Mathlib` plus a couple of repo modules elaborates in ~60 s, about 2.5× cheaper
  than the real `lake build` of the module.
* `Tate/FamilyConst.lean`'s old `tateConstEquiv`/`tateConstOrbitEquiv`/
  `isZero_tateModule_constFamily` were referenced nowhere; but the file also carried
  `smul_orbit_of_mem_stabilizer_val` and `mem_stabilizer_val_of_smul_orbit`, which
  `Units/IdeleTorsionSubgroup.lean` *does* use.  A per-module `lake build` never sees this: only the
  root build does (gotcha 1472 again, in the deletion direction).

### (d) Where Shafarevich stands

Unchanged from §1.09 except that (ii-b) is now a theorem:

>  `Ĥ^{-2}(G, W)  ↠  Ш¹_{idelic}(G, K^× ⊗ W)`  — brick 3, conditional on `HasIdeleClassNakayamaSpan`
>  `Ш¹(G, K^× ⊗ W) ≅ sha1Level`                — brick 4, done
>  `sha1Level = ⊥  ⇒  Ш²(k,E) ⊆ inf`           — brick 5, done
>  `Ĥ^{-2}(G, W) = 0` after shrinking `G`      — Prop 6, done
>  `Ш_dec = Ш_idelic`                          — (ii-b) **done**, (ii-a) open

The two open items are therefore (i) `HasIdeleClassNakayamaSpan` — the reciprocity identity
`ker Left_P = Σ_w cor_w(ker Left_w)`, blocked on `baseFundamentalClass` being `.choose`-defined —
and (ii-a) the henselization-vs-completion comparison `(K ⊔ F)^×/p ≅ K_w^×/p`.

---

## 1.11 Status (2026-09-06, latest)

### (a) Two modules landed

* **`Profinite/KummerLocalQuot.lean`** (commit `4655267`, full root build **9733 jobs**, clean).
  The local comparison of `KummerLocalCompare.lean`, restated on the *finite quotient*
  `↥D ⧸ K.fixingSubgroup.subgroupOf D` of a decomposition subgroup rather than on `↥D` itself.
  Three theorems, all delegating to `KummerLocalCompare`:
  `coeffH1_eq_one_of_coeffQuotH1_eq_one`,
  `coeffH1_resQuotH1_eq_one_of_resCoeffQuotH1_eq_one`,
  `coeffH1_resQuotH1_eq_one_of_mem_sha1Level`.
  This is the level the transgression's obstruction actually reads (finding 1787): the coefficients
  `SmoothH1 ↥K.fixingSubgroup E` are acted on through the quotient, so "locally trivial" is already
  a statement about the finite quotient, and rewriting the comparison there costs nothing —
  surjectivity of localisation and the description of its kernel are statements about the
  coefficients alone, with no reference to the acting group.
* **`Profinite/KummerTransport.lean`** (new).  The twisted Kummer identification
  `kummerFiniteH1Equiv`, **computed on cocycles**, plus the naturality square that gap (ii-a)
  needs.  See (b) and (c).

### (b) The Kummer identification is computable on cocycles

`kummerFiniteH1Equiv = (kummerSmoothH1Equiv …).trans (h1MulEquivOfSmul (quotientFixingSubgroupEquiv
K) B φ hφ)` and `kummerSmoothH1Equiv` is `smoothH1EquivOfAddEquiv` after a `discreteSmoothH1Equiv`.
Each of those two transports is built out of a `.symm` of a `Tate.groupCohomologyCongr`, so the
naive reading is that the composite is an *inverse* map and therefore useless on explicit cocycles.
That reading is wrong.

* **1806 (Mathlib naming).**  `MulEquiv.apply_eq_iff_eq_symm_apply` does **not** exist.  The two
  real lemmas are `MulEquiv.symm_apply_eq (e) : e.symm x = y ↔ x = e y`
  (`Algebra/Group/Equiv/Defs.lean:344`) and `MulEquiv.eq_symm_apply (e) : y = e.symm x ↔ e y = x`
  (:348).  `rw [← MulEquiv.eq_symm_apply]` turns `e a = b` into `a = e.symm b`.
* **1807 (decisive).**  Applying `MulEquiv.eq_symm_apply` twice flips the goal so that only the
  *forward* `groupCohomology.map` appears, and both resulting unfolding lemmas are literally
  `rfl`:
  ```lean
  theorem h1MulEquivOfSmul_symm_ofAdd (z : ↥(groupCohomology B 1)) :
      (h1MulEquivOfSmul e B φ hφ).symm (Multiplicative.ofAdd z)
        = Multiplicative.ofAdd (groupCohomology.map (e : Q →* G)
            (repIsoOfEquivSmul e B φ hφ).hom 1 z) := rfl

  theorem smoothH1EquivOfAddEquiv_symm_ofAdd
      (z : ↥(groupCohomology (Rep.ofDistribMulAction ℤ Q T) 1)) :
      (smoothH1EquivOfAddEquiv Q S T κ hκ).symm (Multiplicative.ofAdd z)
        = (discreteSmoothH1Equiv Q S).symm (Multiplicative.ofAdd
            (groupCohomology.map (MonoidHom.id Q) (repIsoOfAddEquiv Q S T κ hκ).hom 1 z)) := rfl
  ```
  Both are in `KummerTransport.lean`.
* **1808 (Mathlib map).**  `groupCohomology.functor k G n` has `map φ := map (MonoidHom.id _) φ n`
  (`Functoriality.lean:483`); `H1` is `abbrev H1 := groupCohomology A 1` (`LowDegree.lean:927`);
  `cochainsMap₁ f φ x = fun g => φ.hom.hom (x (f g))` (`Functoriality.lean:165`);
  `coe_mapCocycles₁ : ⇑(mapCocycles₁ f φ x) = cochainsMap₁ f φ x` is `rfl` (:297);
  `H1π_comp_map` (:317) is `@[reassoc (attr := simp), elementwise (attr := simp)]`, giving
  `H1π_comp_map_apply : map f φ 1 (H1π A x) = H1π B (mapCocycles₁ f φ x)`.
* **1809 (repo map, the Tate maps on cocycles in degree one).**
  `Tate.tateRes_one_H1π (H) : tateRes H A 1 (H1π A b) = H1π (resObj H A) (resCocycles₁ H A b)`
  (`TateCohomology/RestrictOne.lean:130`), with `resCocycles₁ H A b = ⟨fun h => b (h : G), _⟩`
  (`TateTheorem.lean:92`);
  `Tate.tateMap_one_H1π (φ) : tateMap φ 1 (H1π A b) = H1π B (homCocycles₁ φ b)`
  (`NakayamaNatural.lean:114`), with `homCocycles₁_apply : homCocycles₁ φ b τ = φ.hom.hom (b τ)`
  (:100, `rfl`).
* **1812 (repo map, reuse).**  `GroupCohomology/H2Transport.lean:68` already has exactly the
  morphism of representations needed —
  `transportRepHom (e : G ≃* G') (φ : A ≃ₗ[k] B) (hφ) : (Action.res _ (e.symm : G' →* G)).obj A ⟶ B`
  — so `KummerTransport.lean` does **not** define its own (and must not: the name is taken, gotcha
  1472).  Its universe constraint is `{k : Type u} {G G' : Type u}`, which for `k = ℤ` forces the
  acting groups into `Type`; every group in this part of the tower already is.

The payoff is `KummerTransport.lean`'s

```lean
noncomputable def transportCocycles₁ {u : Q → S} (hu : IsMulCocycle₁ u) :
    groupCohomology.cocycles₁ B :=
  mapCocycles₁ (e.symm : G →* Q)
    (transportRepHom e (transportUnitsEquiv κ B φ) (transportUnitsEquiv_intertwine κ hκ e B φ hφ))
    (cocyclesOfIsMulCocycle₁ hu)

theorem transportCocycles₁_apply (hu) (g : G) :
    transportCocycles₁ κ hκ e B φ hφ hu g = φ (κ.symm (Additive.ofMul (u (e.symm g)))) := rfl

theorem h1MulEquivOfSmul_smoothH1Mk (hu) (hs) :
    h1MulEquivOfSmul e B φ hφ (smoothH1EquivOfAddEquiv Q S T κ hκ (smoothH1Mk u hu hs))
      = Multiplicative.ofAdd (groupCohomology.H1π B (transportCocycles₁ κ hκ e B φ hφ hu))
```

i.e. **the class of a smooth one cocycle is the class of an explicitly given one cocycle**, and no
cocycle condition has to be proved by hand (`mapCocycles₁` supplies it).

### (c) The naturality square for gap (ii-a), step 2

`KummerTransport.lean`'s main theorem is the generic square.  Global data
`(Q, S, T, κ, hκ, e : Q ≃* G, B, φ, hφ)` with `G` finite; local data
`(Q', S', T', κ', hκ', e' : Q' ≃* ↥H, B', φ', hφ')` for a subgroup `H ≤ G`; a smooth `π : Q' →* Q`
with `hπ : ∀ g s, g • s = π g • s`; a `ψ : S →* S'` with `hψ : ∀ g s, ψ (g • s) = g • ψ s`; a
`Φ : resObj H B ⟶ B'`; and the two compatibilities

```lean
(hcomm : ∀ g : Q', ((e' g : ↥H) : G) = e (π g))
(hcoef : ∀ t : T,
  Φ.hom.hom (φ t) = φ' (κ'.symm (Additive.ofMul (ψ (Additive.toMul (κ t))))))
```

give

```lean
theorem tateMap_tateRes_eq_zero_of_coeffH1_comapH1_eq_one (hu) (hs)
    (hx : coeffH1 ψ hψ (comapH1 π hπ hsm (smoothH1Mk u hu hs)) = 1) :
    tateMap Φ 1 (tateRes H B 1 (Multiplicative.toAdd
      (h1MulEquivOfSmul e B φ hφ
        (smoothH1EquivOfAddEquiv Q S T κ hκ (smoothH1Mk u hu hs))))) = 0
```

The proof is a pointwise comparison of two cocycles on `↥H`: on the Tate side
`h ↦ Φ.hom.hom (φ (κ.symm (ofMul (u (e.symm ↑h)))))`, on the smooth side
`h ↦ φ' (κ'.symm (ofMul (ψ (u (π (e'.symm h))))))`; `hcomm` identifies the arguments and `hcoef`
the coefficients.

* **1813 (Lean).**  `↥((Action.res _ f).obj (Rep.ofMulDistribMulAction Q S)).V` does not reduce to
  `Additive S` during *elaboration* of a `show`, so `Additive.toMul s` there fails with
  `failed to synthesize HSMul Q ↑(…).V ?m`.  Pin it: write `@Additive.toMul S (@id (Additive S) s)`
  (and `@id (Additive S) s` wherever the bare `s` occurs), which forces the defeq check at default
  transparency and succeeds.  Use the *same* spelling on both sides of the `show` or the closing
  `rfl` will be left over.
* **1814 (Lean).**  Section *data* variables used only inside a tactic proof are not
  auto-included either, exactly like hypotheses (gotcha 747): `include κ' hκ' e' φ' hφ' hcomm hcoef
  in` is needed even though `κ'`, `e'`, `φ'` are `(…)`-explicit data.  Order (gotcha 18):
  `omit … in` first, then `include … in`, then the docstring.

### (d) Where Shafarevich stands

Unchanged from §1.10(d):

>  `Ĥ^{-2}(G, W)  ↠  Ш¹_{idelic}(G, K^× ⊗ W)`  — brick 3, conditional on `HasIdeleClassNakayamaSpan`
>  `Ш¹(G, K^× ⊗ W) ≅ sha1Level`                — brick 4, done
>  `sha1Level = ⊥  ⇒  Ш²(k,E) ⊆ inf`           — brick 5, done
>  `Ĥ^{-2}(G, W) = 0` after shrinking `G`      — Prop 6, done
>  `Ш_dec = Ш_idelic`                          — (ii-b) done, (ii-a) open

with (ii-a) now decomposed into four steps, of which **step 2 is done**:

1. **1b** — the group isomorphism `↥(stabilizer Gal(Ω/k) P) ⧸ L.fixingSubgroup.subgroupOf
   (stabilizer Gal(Ω/k) P) ≃* ↥(stabilizer Gal(↥L/k) v)`, from
   `QuotientGroup.liftEquiv _ (stabilizerRestrictPrime_surjective L hv) (Subgroup.ext …)`
   (`Units/HasseTwoDecomposition.lean`), and its archimedean twin.  Finding **1810**:
   `[IsGalois k ↥L]` already supplies `L.fixingSubgroup.Normal`
   (`Mathlib/FieldTheory/Galois/Basic.lean:452` and `Profinite/Krull.lean:56`), so no extra
   instance argument is needed.
2. **2** — the transport and the square: **done**, `Profinite/KummerTransport.lean`.
3. **1c** — the coefficient map `ψ_v` and its equivariance, with kernel condition supplied by
   `tensor_adicUnitHom_eq_zero_of_tensor_sup_eq_zero` /
   `tensor_infiniteUnitHom_eq_zero_of_tensor_sup_eq_zero`
   (`Kummer/DecompositionLocalPower.lean:200/216`) and surjectivity by
   `surjective_tensor_sup_of_stabilizer_ideal` / `_infinitePlace`
   (`Kummer/SupPowSurjective.lean:432/445`).
4. **3** — the commuting square of representations
   `resHom _ (tensorHomLeft W (globalUnitsToIdele k K)) ≫ ideleAdicLocalHom k K W v
   = tensorHomLeft (resObj _ W) (localUnitsHom v)` (an `ext` on pure tensors), then
   `tateRes_naturality` + `tateMap_comp_apply` feed both hypotheses of
   `eq_zero_of_forall_local_idele` (`Units/IdeleLocalVanish.lean:155`), giving
   `kummerFiniteSha1 ≤ ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) 1)`.

---

## 1.12 Status (2026-09-06, later) — **gap (ii-a) is closed**: an everywhere locally trivial Kummer class dies in the ideles

### (a) Two modules landed (commit `b350215`, full root build **9738 jobs**, clean)

* **`Kummer/SupKummerData.lean`** — Kummer data ascend.  `isKummerData_of_le (hK : IsKummerData ↥K
  Ω M ιK p) (hKL : K ≤ L) (hroot : ∀ x : Ωˣ, ∃ y : Ωˣ, y ^ p = x) : IsKummerData ↥L Ω M
  ((unitsInclusion hKL).comp ιK) p`, with the action of `Gal(Ω/↥L)` on `M` taken to be the trivial
  one (`trivialMulDistribMulAction`).  Only one clause has content: a primitive `p`-th root of
  unity of `K` stays primitive in `L`, so every `p`-th root of unity of `L` is one of its powers and
  therefore already in the image of `ιK`.  Also `unitsInclusion`, `injective_unitsInclusion`,
  `algebraMap_unitsInclusion`.
* **`Units/KummerIdele.lean`** — the assembly.  Three theorems:
  `tateMap_tateRes_kummerFiniteH1Equiv_adic_eq_zero`,
  `tateMap_tateRes_kummerFiniteH1Equiv_infinite_eq_zero`, and the capstone
  `tateMap_globalUnitsToIdele_kummerFiniteH1Equiv_eq_zero`:

  ```lean
  theorem tateMap_globalUnitsToIdele_kummerFiniteH1Equiv_eq_zero
      (eW : ↥W.V ≃+ (Fin dW → ZMod p))
      {z : SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E)}
      (hz : z ∈ sha1Level E K.fixingSubgroup hop (decompositionSubgroups k Ω)) :
      tateMap (tensorHomLeft W (globalUnitsToIdele k ↥K)) 1
        (Multiplicative.toAdd (kummerFiniteH1Equiv hK htriv htrivEK α hEp hfix
          (tensorObj (globalUnitsRep k ↥K) W) φ hφ hop z)) = 0
  ```

That is exactly `Ш_dec ⊆ Ш_idelic` read through brick 4's identification, so **gap (ii-a) is
closed** and steps 1b, 1c and 3 of §1.11(d) are all done.

### (b) How the place argument runs

For a finite place `v` of `K`: `Ideal.exists_ideal_over_prime_of_isIntegral` produces a prime `P`
of `𝓞 Ω` above `v` (gotcha 1848); `fixingSubgroup_fixedField_of_mem_decompositionSubgroups`
(`Units/DecompositionClosed.lean`) writes `stabilizer Gal(Ω/k) P` as `F.fixingSubgroup` for an
intermediate field `F`; the local argument then lives on the compositum `K ⊔ F`, where
`isKummerData_of_le` supplies the Kummer data, `surjective_tensor_sup_of_stabilizer_ideal`
(`Kummer/SupPowSurjective.lean`) the surjectivity and
`tensor_adicUnitHom_eq_zero_of_tensor_sup_eq_zero` (`Kummer/DecompositionLocalPower.lean`) the
kernel condition, and `globalUnitsAdicLocalHom_apply` (`Units/GlobalUnitsLocal.lean`) identifies the
evaluation at `v` with `adicUnitHom v ⊗ id`.  All of it is handed to
`tateMap_tateRes_kummerFiniteH1Equiv_eq_zero_of_tensor_eq_zero`
(`Profinite/KummerLocalTate.lean:246-351`).  The archimedean twin is structurally identical, with
`NumberField.InfinitePlace.comap_surjective` in place of the prime-above idiom.

The two local vanishings feed `tateMap_globalUnitsToIdele_eq_zero`
(`Units/GlobalUnitsLocal.lean:135`).

### (c) Gotchas

* **1849 (decisive).**  Writing `stabilizerQuotientEquivPrime ↥K hPunder` (the *coerced* type)
  where the lemma wants the `IntermediateField k Ω` itself does **not** give a type error: Lean
  grinds through unification and reports `(deterministic) timeout at whnf` **at the `theorem`
  line**, even at `maxHeartbeats 1000000`.  Gotcha 29 again — a whnf timeout on a declaration that
  mentions an `IntermediateField`-valued lemma is very likely a `↥E`-vs-`E` slip.
* **1850 (recipe).**  To localise a whnf timeout in a long tactic proof: copy the file into
  `.scratch/`, truncate the proof with `sorry`, and typecheck with
  `time env -u LD_LIBRARY_PATH lake env lean -Dlinter.style.multiGoal=true .scratch/<f>.lean`.
  Re-adding the `have`s one at a time isolates the offender in a handful of ~50 s iterations.
* **1851 (Mathlib).**  `IsPrimitiveRoot.isUnit` takes `p ≠ 0`, not `0 < p`.
* **1852 (instance).**  The `MulAction Gal(Ω/k) (Ideal (𝓞 Ω))` behind `stabilizer Gal(Ω/k) P` is the
  *pointwise* action, so a file writing that needs `open scoped Pointwise`.
* **1853 (Mathlib).**  `NumberField.InfinitePlace.comap_surjective (k := ↥L) (K := Ω)` needs
  `[Algebra.IsAlgebraic ↥L Ω]`, from `Algebra.IsAlgebraic.tower_top (K := k) (L := ↥L) (A := Ω)`.
* **1854 (Mathlib).**  `H1 A` is an abbrev for `groupCohomology A 1` (`LowDegree.lean:927`), so
  `kummerFiniteH1Equiv`'s codomain `Multiplicative ↥(H1 B)` feeds `tateRes`/`tateMap` directly.
* **1855 (build cost).**  `lake build InverseGalois.CFT.Units.KummerIdele` = 8391 jobs;
  `…Kummer.SupKummerData` = 8037 jobs.

### (d) Where Shafarevich stands

> ` Ĥ^{-2}(G, W)  ↠  Ш¹_idelic(G, K^× ⊗ W)`  — brick 3, conditional on `HasIdeleClassNakayamaSpan`
> ` Ш¹(G, K^× ⊗ W) ≅ sha1Level`              — brick 4, done
> ` sha1Level = ⊥  ⇒  Ш²(k,E) ⊆ inf`         — brick 5, done
> ` Ĥ^{-2}(G, W) = 0` after shrinking `G`    — Prop 6, done
> ` Ш_dec = Ш_idelic`                        — **(ii-a) and (ii-b) both done**

so **`HasIdeleClassNakayamaSpan` (§1.00, gap (i)) is the only mathematical content still missing**
from row 5.  The reciprocity identity it names is
`ker Left_P = Σ_w cor_w (ker Left_w)`, and the obstacle recorded at §0.90/§1.00 is that
`baseFundamentalClass` (`Units/BaseTate.lean:60`) is `.choose`-defined, so it must first be rebuilt
invariant-theoretically out of `localInvariantHom` plus reciprocity
(`Brauer/TotalInvariant.lean`, `Brauer/BaseReciprocity.lean`).

---

## 1.13 **REFUTATION** (2026-09-06) — `HasIdeleClassNakayamaSpan` as stated is FALSE

**Do not attempt to prove `HasIdeleClassNakayamaSpan k K p` in its current, `∀ W`-quantified
form.**  It is false: there is a number field `k`, a finite Galois extension `K/k` and a prime `p`
for which the span fails at `W = 𝔽_p` (trivial action) and `n = -2`.  What follows is the
computation, the counterexample, and what has to replace the hypothesis.

Throughout: `G = Gal(K/k)`, `I = I_K` the ideles, `C = C_K` the idele classes, `p` an odd prime,
`μ_p ⊆ k` (so `μ_p` is the trivial `G`-module `𝔽_p`).  `Ĥ` is Tate cohomology of the finite group
`G`; `D_v ≤ G` are the decomposition subgroups; `Ш^i(G,A) = ker(Ĥ^i(G,A) → ∏_v Ĥ^i(D_v,A))`.
Take `P = G` (i.e. `G` a `p`-group), so the Sylow subgroup in the statement of the span is all of
`G` and drops out.

### (a) At `n = -2` and `W` trivial, the Tate–Nakayama term contributes **nothing**

The span at `(W, n)` reads `range TN_W(n) ⊔ range ι_*(n+2) = ⊤` inside `Ĥ^{n+2}(G, C ⊗ W)`, where
`ι_* : Ĥ^{n+2}(G, I ⊗ W) → Ĥ^{n+2}(G, C ⊗ W)`.  Put `n = -2`, `W = 𝔽_p`.

* `TN` is natural in the coefficient module.  Along the reduction `ℤ ↠ 𝔽_p` the square

  ```
  Ĥ^{-2}(G, ℤ)  --TN-->  Ĥ⁰(G, C)
       |                    |
       v                    v
  Ĥ^{-2}(G, 𝔽_p) --TN-->  Ĥ⁰(G, C/p)
  ```

  commutes, and the **left vertical is surjective**: the Bockstein gives
  `Ĥ^{-2}(G,ℤ) → Ĥ^{-2}(G,𝔽_p) → Ĥ^{-1}(G,ℤ)` and `Ĥ^{-1}(G,ℤ) = 0`.  Hence
  `range TN_{𝔽_p}(-2) = image(Ĥ⁰(G,C) → Ĥ⁰(G,C/p))` (the top `TN` is Tate's isomorphism
  `Ĥ^{-2}(G,ℤ) ≅ Ĥ⁰(G,C)`, so the top row is onto `Ĥ⁰(G,C)`).
* `Ĥ⁰(G, I) → Ĥ⁰(G, C)` is **surjective**, because the next term is `Ĥ¹(G, K^×) = 0`
  (Hilbert 90).  Combined with naturality of `I → C` in the reduction square,

  > `range TN_{𝔽_p}(-2) ⊆ range ι_*(0)`.

**So at `W` trivial and `n = -2` the span is *equivalent* to `range ι_* = ⊤`, i.e. to
`Ш¹(G, K^× ⊗ W) = 0` — which is precisely the conclusion it is used to derive.**  The whole
Tate–Nakayama tower is doing no work in that instance.  (This is special to trivial `W`: the same
argument works for any `W` that is a quotient of a lattice `Y` with `Ĥ^{n-1}(G,Y) → Ĥ^{n-1}(G,W)`
zero, e.g. any trivial `W = 𝔽_p^d`; for a genuinely non-trivial `W` the `TN` term is strictly
bigger than the idelic one, because `Ĥ²(G,I) → Ĥ²(G,C)` need **not** be surjective —
its image is `(1/lcm_v |D_v|)ℤ/ℤ` inside `Ĥ²(G,C) ≅ (1/|G|)ℤ/ℤ`, which is the content of
gotcha 1129, "there is no idelic fundamental class".)

### (b) The cokernel of `ι_*` at `n = -2` is `Ш²(G, μ_p)`

Bockstein for a `G`-module `M`, `i = 0`:
`0 → Ĥ⁰(G,M)/p → Ĥ⁰(G,M/p) → Ĥ¹(G,M[p]) → 0` (the right-hand map is onto because `p` kills
`Ĥ¹(G,M[p])`), naturally in `M`.  Apply it to `M = I` over `M = C`:

```
0 → Ĥ⁰(G,I)/p → Ĥ⁰(G,I/p) → Ĥ¹(G,I[p]) → 0
       | (a)         | (b)        | (c)
0 → Ĥ⁰(G,C)/p → Ĥ⁰(G,C/p) → Ĥ¹(G,C[p]) → 0
```

`(a)` is onto by Hilbert 90 as above, so the snake lemma gives `coker(b) ≅ coker(c)`.  Now
Grunwald–Wang at prime exponent — **already in the repo**, `exists_pow_eq_of_forall_localPow_
outside_of_prime` (`CFT/GrunwaldWang.lean:226`) — makes `0 → μ_p → I[p] → C[p] → 0` exact
(§1.01(c), `resSeq_tensorSeq_ideleClassTorsion_shortExact`).  Since `I[p] = ∏_w μ_p =
∏_v Ind_{D_v}^G μ_p`, Shapiro plus "Tate cohomology of a finite group commutes with products"
gives `Ĥ^i(G, I[p]) = ∏_v Ĥ^i(D_v, μ_p)` with the map from `Ĥ^i(G, μ_p)` being the product of the
restrictions.  Hence

> **`coker(ι_* : Ĥ⁰(G, I/p) → Ĥ⁰(G, C/p)) ≅ Ш²(G, μ_p)`,**

and by (a), **the span at `(W = 𝔽_p, n = -2)` holds if and only if `Ш²(G, μ_p) = 0`.**

### (c) A `(k, K, p)` with `Ш²(G, μ_p) ≠ 0`

*Group theory.*  For `G = (ℤ/p)²`, `p` odd, the exponent-`p` Heisenberg extension
`1 → ℤ/p → H → (ℤ/p)² → 1` (with `H = ⟨a,b : a^p = b^p = [a,b]^p = 1, [a,b]` central`⟩`) is
non-split, so its class `0 ≠ x₁x₂ ∈ H²(G, 𝔽_p)`; but over any cyclic `C = ⟨(s,t)⟩ ≤ G` the
preimage is `⟨a^s b^t, z⟩ ≅ (ℤ/p)²` (exponent `p`!), so `res_C(x₁x₂) = 0`.  Equivalently, in
`H^*(G,𝔽_p) = Λ(x₁,x₂) ⊗ 𝔽_p[y₁,y₂]`, `res_C(a·x₁x₂ + b·y₁ + c·y₂) = (bs+ct)·y`, which vanishes for
every `(s,t) ≠ 0` iff `b = c = 0`.  So `Ш²_ω((ℤ/p)², 𝔽_p) = ⟨x₁x₂⟩ ≅ 𝔽_p ≠ 0` for odd `p`
(and `= 0` for `p = 2`).

*Arithmetic realisation.*  `p = 3`, `k = ℚ(μ_3) = ℚ(√-3)`, `K = k(α^{1/3}, β^{1/3})` with `α, β`
independent modulo cubes chosen so that

* `α = π₁` a prime element, `β = π₂ ·` (a cube) with `π₂` a prime element;
* `β ∈ (k_v^×)³` for every `v ∣ 3` and for `v = v₁` (the place of `π₁`);
* `α ∈ (k_{v₂}^×)³`, arranged by picking `𝔭₂` split in `k(α^{1/3})` (Chebotarev).

Then: `v₁` ramifies only in `k(α^{1/3})`, so `D_{v₁}` is cyclic of order 3; symmetrically for `v₂`;
every `v ∣ 3` splits in `k(β^{1/3})` so `D_v ≤ Gal(k(α^{1/3})/k)` is cyclic; the unique archimedean
place is complex, `D_∞ = 1`; every other place is unramified, so `D_v = ⟨Frob_v⟩` is cyclic.  **All
decomposition subgroups are cyclic**, hence `Ш²(G, μ_3) ⊇ Ш²_ω((ℤ/3)², 𝔽_3) ≠ 0`.

Therefore `HasIdeleClassNakayamaSpan ℚ(μ_3) K 3` is **false**, and
`kummerFiniteH1Equiv_eq_one_of_span` / `sha1Level_eq_bot_of_span`
(`Units/KummerShaBot.lean`) are **vacuous** for such a `K`.  Both remain true theorems; they just
cannot be discharged by proving their hypothesis in general.

Note the structural reason: by Chebotarev **every cyclic subgroup of `G` is a decomposition
subgroup**, so `Ш^i(G,A) ⊆ Ш^i_ω(G,A)` always, and the span can only ever hold when the
Tate–Šafarevič group of the *finite* group `G` over its decomposition subgroups vanishes.  That is
a condition on `K`, not a theorem about `K`.

### (d) A positive by-product: `Ш²(k, μ_p) = 0` with **no** Poitou–Tate

At the level of the full absolute Galois group the answer is the opposite.  Kummer
`0 → μ_p → 𝔾_m → 𝔾_m → 0` plus Hilbert 90 gives, globally and at every place,
`0 → k^×/(k^×)^p → H²(k, μ_p) → Br(k)[p] → 0`.  A locally trivial class maps to a locally trivial
Brauer class, which vanishes by Albert–Brauer–Hasse–Noether — **already in the repo**,
`eq_one_of_mem_sha2`; so it comes from an `α ∈ k^×/(k^×)^p` that is a local `p`-th power
everywhere, hence a global `p`-th power by Grunwald–Wang at prime exponent — **also already in the
repo**.  So

> **`Ш²(k, μ_p) = 0` for every number field `k` and every prime `p`, from two theorems the repo
> already has.**

Consequently every class of `Ш²(G, μ_p)` dies under inflation to `G_k`, hence dies at some finite
level: for every `K` there is `K' ⊇ K` with `inf(Ш²(Gal(K/k), μ_p)) = 0` in `H²(Gal(K'/k), μ_p)`.
This does **not** give `Ш²(Gal(K'/k), μ_p) = 0` (new classes appear at level `K'`), so it does not
repair the span; but it does say the correct shape of the hypothesis is an **`∃ K`** statement, and
it is the germ of the replacement.

### (e) What has to change

1. **Refactor the hypothesis to be per-coefficient and per-degree.**  `HasIdeleClassNakayamaSpan`
   quantifies over *all* `W` and *all* `n`, and is used at exactly one pair: `W = E(-1)` and
   `n = -2`.  A predicate `HasIdeleClassNakayamaSpanAt k K p W n` is not refuted by (c) — the
   counterexample only kills the instance `W = 𝔽_p`.  (When `μ_p ⊆ k` and the kernel `E` of the
   embedding problem is the *trivial* module `𝔽_p`, though — the central `ℤ/p` case, which is a
   genuine case of `FrattiniKernelEP` — `W = E(-1)` **is** trivial, and by (a)+(b) the span is
   then literally equivalent to `Ш²(G, μ_p) = 0`.  So the refactor makes the statement honest, not
   provable.)
2. **The chooser of `K` must be the consumer.**  Row 5's real statement is
   `∃ K ⊇ k(μ_p, E)` — compatible with whatever the Šafarevič induction needs — such that the span
   holds at `W = E(-1)`, `n = -2`.  Sufficient conditions worth having in Lean, in increasing
   order of usefulness:
   * *some* place `v` has `D_v ⊇` a Sylow `p`-subgroup of `G` ⟹ `Ш^i(G, A) = 0` for every `p`-torsion
     `A` and every `i` (restriction to a Sylow subgroup is injective on `p`-primary parts) ⟹ the
     span for every `W` and every `n`.  Cheap to state, but only satisfiable when the Sylow
     subgroup is a *local* Galois group — restrictive.
   * `Ш²_ω(G, μ_p ⊗ W) = 0`, which subsumes the above and is the sharp form of (b).
3. **Or abandon the Tate–Nakayama route at `n = -2` altogether** and take Schmidt–Wingberg's own
   road: Poitou–Tate `Ш²(k,E) ≅ Ш¹(k,E′)^∨` with `E′ = Hom(E, μ_p)`, then
   `Ш¹(k,E′) ↪ H¹(G,E′)` and finite-group Tate duality `Ĥ^i(G,M)^∨ ≅ Ĥ^{-i-1}(G, M^D)` to get
   `Ĥ^{-2}(G, E(-1)) ↠ Ш²(k, E)`.  The repo has neither the Poitou–Tate pairing nor finite-group
   Tate duality yet.  By §0.99(b) this is the *only* place Schmidt–Wingberg use Poitou–Tate.

### (f) A caution about "reduce to `Ш²(k,E) ⊆ inf H²(G,E)`"

That containment is, on its own, **vacuous**: continuous cochain cohomology of a profinite group
with discrete coefficients is the filtered colimit of the finite-level cohomologies, so *every*
class of `H²(k,E)` is inflated from some finite `K'`.  The content of row 5 is therefore not the
containment but its **uniformity**: `K` (and hence `G`) must be fixed *before* the finitely many
classes that Schmidt–Wingberg's Proposition 6 is allowed to kill are chosen, because Prop 6's
threshold `m₀` depends on the number `t` of classes.  Any restructuring of rows 5/6 has to keep
that quantifier order — see §0.87(a), where losing it is exactly the recorded circularity.

### (g) Reading of SW Proposition 6 (`sw.txt:258–345`), for the record

Prop 6 does **not** make `Ĥ^k(G, E(m,τ) ⊗ T)` vanish.  It says: given `n, t, k, T, τ`, there is
`m₀ ≥ n` such that for all `m ≥ m₀` and *any prescribed* `x₁, …, x_t ∈ Ĥ^k(G, E(m,τ) ⊗ T)` there
is a surjective pro-`p`-`G`-operator homomorphism `ψ : F(m) ↠ F(n)` whose induced map kills
`x₁, …, x_t`.  The proof dimension-shifts to `k = -1` via `A_k = I_G^{-(k+1)}`, uses Lemma 5's
`G`-equivariant surjection `κ(d) : (F(d)/F(d)_2)^{⊗j} ↠ F(d)^{(τ)}/F(d)^{(τ+1)}`, takes `m = rn`
with `r` large and applies Proposition 2.  This is why row 5 is *not* subsumed by Prop 6: to feed
Prop 6 one needs a **fixed, `m`-independent** number of generating classes, and the only source of
such a bound in SW is the duality `Ĥ^{-2}(G, E(m,τ)(-1)) ↠ Ш²(k, E(m,τ))` with the
one-dimensional `T = Hom(μ_p, 𝔽_p)`.

---

## 1.14 Status (2026-09-06, later) — the brick-3/4/5 route is **doubly** broken; the Poitou–Tate chain, costed brick by brick; one brick landed

### (a) The second, independent reason the current route cannot finish

§1.13 refuted the *hypothesis* `HasIdeleClassNakayamaSpan`.  Even granting it, the route dies a
second time, and the second death is not repairable by weakening the span.

Look at what `KummerShaBot.lean` actually needs.  Both
`kummerFiniteH1Equiv_eq_one_of_span` and `sha1Level_eq_bot_of_span` take

```
(hzero : ∀ y : ↥(tateModule W (-2)), y = 0)
```

— the **total vanishing** of `Ĥ^{-2}(G, W)`.  That is what makes the argument work: the class dies
in the ideles, Tate–Nakayama produces it from `Ĥ^{-2}(G,W)`, and there is nothing there for it to
be produced from.

Schmidt–Wingberg's Proposition 6 cannot supply that.  Prop 6 (see §1.13(g)) makes a **prescribed
finite list** `x₁, …, x_t` of classes die, at the cost of raising `m`; it never makes the whole
group `Ĥ^{-2}(G, E(m,τ) ⊗ T)` vanish, and it cannot, because `F(m)` grows with `m` and so does its
cohomology.  So `hzero` is not a hypothesis SW's construction is able to discharge, and no
adjustment of the *span* hypothesis changes that: the two hypotheses sit in different arguments.

Why SW's own route does not have this problem: it never asks for total vanishing.  Poitou–Tate
gives a **surjection**

```
Ĥ^{-2}(G, E(-1))  ↠  Ш²(k, E)
```

so the single obstruction class `ε ∈ Ш²(k,E)` of the embedding problem has a **single** preimage
`x ∈ Ĥ^{-2}(G, E(-1))`, and Prop 6 is invoked with **`t = 1`**.  One prescribed class, killed by
one enlargement of `m`.  That is the whole reason the duality is in SW's proof at all.

**Conclusion.**  Bricks 3/4/5 (`Ĥ^{-2}(G,W) ↠ Ш¹(G, K^× ⊗ W)` → `sha1Level = ⊥` →
`Ш²(k,E) ⊆ inf`) are abandoned *as a route to* `FrattiniKernelEP`.  The Lean statements stay —
they are true theorems under their hypotheses, and brick 5 in particular is reused below — but the
plan of discharging their hypotheses is dropped.  Poitou–Tate is unavoidable.

### (b) The Poitou–Tate chain, brick by brick

Write `G = Gal(K/k)`, `E` a finite elementary abelian `p`-group with a `G_k`-action factoring
through `G`, and `E′ = Hom(E, μ_p)` its Cartier dual.  The target is the surjection above.  It
decomposes into four independent steps:

1. **Global duality** `Ш²(k, E) ≅ Ш¹(k, E′)^∨`.  *Missing — the monster.*  This is Poitou–Tate
   proper.  The repository already has the pairing that must induce it: `CFT/PoitouTate/CupDual.lean`
   builds `cupDual : H¹(G_k, E) → H¹(G_k, E′) → H²(G_k, μ_p)`, proves it preserves local
   triviality on both sides, and proves the product formula
   `∏_v inv_v ⟨·,·⟩_v = 1` for the unit symbols.  What is missing is exactness/perfectness, which
   is where Tate's local duality and a compactness argument enter.
2. **`Ш¹(k, E′) ↪ H¹(G, E′)`.**  Cheap.  `Ш¹(K, E′) = 0` for `E′` a finite module with trivial
   `G_K`-action, by Chebotarev (a class of `Hom(G_K, E′)` vanishing on every decomposition group
   vanishes on every Frobenius, hence on a dense set).  Then inflation–restriction.
3. **`H¹(G, E′) ≅ Ĥ^{-2}(G, E(-1))^∨`.**  **Already a theorem.**  `Tate.tateDualEquiv`
   (`CFT/TateCohomology/DualityShift.lean:373`) gives, for any finite `G` and any `p`-torsion
   `A`, `Ĥⁿ(G, Hom(A, C)) ≅ Ĥ^{-n-1}(G, A)^∨`.  Take `C = 𝔽_p`, `A = E(-1)`, `n = 1`.
4. **Dualise back.**  Finite `𝔽_p`-vector spaces, formal.

The degree-2 analogue of step 2 — `Ш²(k,E) ⊆ ker(res : H²(k,E) → H²(K,E))` — is *also* needed,
both to make `Ш²(k,E)` a finite-group-cohomology object and because it is precisely the hypothesis
`hb` of brick 5 (`exists_comapH2_eq_of_sha1Level_eq_bot`, `Profinite/TransgressionInflate.lean:277`,
which asks the cocycle to be a coboundary on `π.ker`).  That is what landed today.

### (c) Landed: an everywhere locally trivial class with split finite coefficients dies over the splitting field

Two files.

`InverseGalois/CFT/Profinite/PiTwo.lean` (new) is the degree-two half of `Profinite/Pi.lean`:
`IsSmooth₂.apply`, `isSmooth₂_pi_iff`, `isMulCocycle₂_pi_iff`, `smoothH2PiHom`,
`smoothH2PiHom_injective` / `_surjective`, `smoothH2PiEquiv`, `coeffH2Equiv`, `coeffH2_id`,
`coeffH2_comp`, and the two that make the whole thing usable against `sha2`:

```lean
theorem resH2_coeffH2 (H : Subgroup G) (x : SmoothH2 G M) :
    resH2 H (coeffH2 φ hφ x) = coeffH2 φ _ (resH2 H x)

theorem coeffH2_mem_sha2 {S : Set (Subgroup G)} {x : SmoothH2 G M} (hx : x ∈ sha2 M S) :
    coeffH2 φ hφ x ∈ sha2 N S
```

Both are `rfl` after destructuring the class into a cocycle: restriction and a coefficient map are
composition of the cocycle with something, on the source and on the target respectively.  Note that
injectivity of `smoothH2PiHom` needs `Fintype ι`, unlike degree one — in degree one the primitive
of a coboundary is an *element* of the coefficients, in degree two it is a *cochain*, and a family
of smooth cochains is smooth only for a finite family.

`InverseGalois/CFT/Units/DecompositionRestrict.lean` gains

```lean
theorem eq_one_of_mem_sha2_of_mulEquivPi_intermediate
    (hπ : ∀ (g : Gal(Ω/K)) (e : E), g • e = galRestrictScalarsHom k K Ω g • e)
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (htrivE : ∀ (g : Gal(Ω/K)) (e : E), g • e = e)
    (htrivM : ∀ (g : Gal(Ω/K)) (m : M), g • m = m)
    {J : Type*} [Fintype J] (α : E ≃* (J → M))
    {ι : M →* Kˣ} (hιinj : Function.Injective ι) (hιpow : ∀ m : M, ι m ^ n = 1)
    (hιsurj : ∀ y : Kˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (z : SmoothH2 Gal(Ω/k) E) (hz : z ∈ sha2 E (decompositionSubgroups k Ω)) :
    comapH2 (galRestrictScalarsHom k K Ω) hπ (isSmoothHom_galRestrictScalarsHom k K Ω) z = 1
```

which is exactly `Ш²(k, E) ⊆ ker(res_{G_K})` for a finite `E` of exponent `n` split by `K ∋ μ_n`.
The proof is four lines of content: restrict the class to `G_K` (it stays everywhere locally
trivial, `comapH2_mem_sha2_decompositionSubgroups`), transport along `α` (which is `G_K`-equivariant
because *both* actions are trivial), project to a factor, and apply `eq_one_of_mem_sha2` — whose
first consumer this is.  `smoothH2PiHom_injective` puts the factors back together.

This is the first arithmetic input to the Poitou–Tate chain that the repository can prove outright,
and it is reusable: it is simultaneously step 2′ of §1.14(b) and hypothesis `hb` of brick 5.

### (d) Where Shafarevich stands

Unchanged from §1.12(d) except: rows 5 and 8 are now understood to be *the same missing thing*
(global duality), row 5's Tate–Nakayama formulation is dead (§1.13, §1.14(a)), and the chain in
§1.14(b) is the replacement, with steps 3 and 4 already done and step 2′ done today.  Step 1 —
Poitou–Tate proper — is the sole remaining mathematical wall between the repository and
unconditional Shafarevich for solvable groups.  Everything nilpotent is complete and unconditional.

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
