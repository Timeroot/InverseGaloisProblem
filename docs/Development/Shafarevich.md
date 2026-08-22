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
anisotropic over `ℚ₂` by the same modulo-eight congruence, so `u(ℚ₂) = 4` exactly.

One remark of §0.1 is now obsolete. It said that the local invariant maps "cannot even be stated
until `ℚ_[p]` is made an instance of the local-field class"; `CFT/Local/PadicLocalField.lean`
supplies that instance — the first anywhere, Mathlib's `IsNonarchimedeanLocalField` having had
none — so the statements of local class field theory are now expressible over `ℚ_[p]`. Being able
to state them is not being able to prove them: ABHN itself is untouched.

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
