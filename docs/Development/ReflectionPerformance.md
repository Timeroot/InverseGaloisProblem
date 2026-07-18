> **UPDATE (superseded).** The conclusion below — that these proofs are "essentially at the
> practical floor for a `ring`/`linear_combination` certificate" — has since been overturned.
> The heavy identities are now proved by a *direct normal-form computation* using the
> `PolyReflect` engine + `native_decide`, with the dense Gröbner cofactors kept as opaque
> `RE.eval` data (so no degree-16/20 polynomial is ever `ring`-normalised or materialised as
> a surface literal).  This dropped E5 from ~an hour to ~2 min and E4 from ~800 s to ~50 s,
> and the whole resolvent chain (`Groups/D5.lean`) now compiles end-to-end.  See the
> "Performance of the resolvent identities" section of `README.md` and `PentagonalSumCertificates.lean`.
> The analysis below is retained only as a record of the earlier `ring`-based investigation.

# Historical performance analysis of the degree-16 / degree-20 certificates

This note records a detailed investigation into the compile time of the two heavy
pentagonal-sum identities and why a faster proof is hard to obtain with the current
tooling. The working proofs were left **unchanged** (they compile and are sorry‑free);
this document explains what was measured and tried.

## Starting point / clarification

* These two files do **not** use `native_decide`. They were already converted to
  `linear_combination` Gröbner‑cofactor certificates by earlier work. (`native_decide`
  does appear elsewhere — `PentagonalSum.lean`, `Groups/D5Polynomial.lean` — but only for small,
  fast finite‑group cardinality checks over `Equiv.Perm (Fin 5)`, not for these
  polynomial identities.)
* `psSq_esymm4` is a degree‑16 identity, `psSq_esymm5` a degree‑20 identity, each a
  statement of ideal membership modulo `(e₁,e₂,e₃)` over a general `CommRing`.

## Measured costs (Lean 4.x + Mathlib, this machine)

| item | time |
|------|------|
| `import Mathlib` + statement elaboration only | ~18 s |
| E4 full proof (`psSq_esymm4`) | **~811 s** |
| E5 full proof (`psSq_esymm5`) | **> 1320 s** |
| E4 product‑form LHS expansion alone (`ring`, 4 vars after `subst`) | ~124 s |
| `Σ Pⱼ⁸` (power‑sum, degree 16) expansion alone | ~30 s |

So for E4 the **cofactor handling adds ~690 s** on top of the ~124 s LHS expansion.

## Where the time goes

The dominant cost is `ring`/`ring1` (invoked by `linear_combination`) normalising the
degree‑16/20 identity, specifically the **Gröbner cofactor**:

* The cofactor `c₂` for `e₂` is a near‑dense degree‑14 polynomial in 4 variables
  (~664 terms; the dense bound is `C(17,3)=680`). For E5 the cofactors are ~1000–1200
  terms (degree ~18).
* Verifying `LHS − RHS = c₂·e₂ + c₃·e₃` forces `ring` to expand `c₂·e₂`
  (≈ 664·10 ≈ 8300 monomial products) and kernel‑check the resulting large reflective
  proof term. At ~0.08 s per product step this is ~690 s — inherent to `ring` at this
  size, not an elaboration artifact.

## Approaches tried (none gave a meaningful speedup)

1. **Chunking the cofactor** into many small `have`s and recombining: the final `ring1`
   still does the full degree‑16 normalisation (~800 s). No gain.
2. **Type‑annotated cofactor chunks** (to cut `binop%`/typeclass elaboration): ran
   ~710 s+. This *confirms* the wall is `ring1`, not literal elaboration.
3. **Elementary‑symmetric (e‑basis) compact cofactor**: invalid. The 6‑representative
   LHS is **not** a symmetric polynomial (it is symmetric only modulo the ideal), so it
   has no compact representation in `ℤ[e₁,…,e₅]`. Verified numerically.
4. **Newton's identities / power sums** (the natural "more mathematical" route):
   power‑sum LHSs (`Σ Pⱼ^{2k}`) expand ~4× cheaper than the product forms, **but** their
   Gröbner cofactors are equally dense (`Σ Pⱼ⁸` needs ~675 cofactor terms vs E4's 664),
   so each `ring1` costs about the same; and the route needs several power‑sum identities
   plus a `1/k` factor (so it would also require `CharZero`/`k` invertible). Net: not
   faster.
5. **E5 as a single `linear_combination`** (instead of the existing chunked form):
   ran > 1500 s — worse, because the degree‑20 cofactors are larger.
6. **`grobner` tactic**: > 280 s and did not finish (degree‑16 Buchberger in‑tactic).
7. **Structured Gröbner certificate**: `(e₂,e₃)` is already a Gröbner basis under
   grevlex (a regular sequence), so there is no sparser multiplier representation
   (certificate "product count" ≈ 8300 either way).
8. **Sparser certificate via the `(e₃,−e₂)` syzygy**: the cofactor is already near‑dense
   at the minimal possible degree, so it cannot be shrunk appreciably.

## Conclusion

The two proofs are essentially at the practical floor for a `ring`/`linear_combination`
certificate of these degree‑16/20 ideal‑membership identities. The cost is dominated by
`ring`'s kernel‑checked normalisation of a dense ~700‑term (E4) / ~1000‑term (E5)
cofactor, which is intrinsic to the certificate approach and not removable by
reformulating the cofactor.

A genuinely faster proof would have to avoid the in‑`ring` polynomial normalisation
altogether — i.e. obtain the sextic‑resolvent coefficient identities **structurally**
(Stauduhar's method / the symmetric‑function theory of the resolvent), so that each
coefficient is read off abstractly rather than proved by expanding a degree‑16/20
polynomial. That is a substantial new formalisation; it was not attempted here because
an incomplete attempt would replace the currently working, sorry‑free proofs with
`sorry`s (a regression).
