# Status of `IsInverseGalois.perm_fin`

The headline theorem is `IsInverseGalois.perm_fin (n : ℕ)` in
`InverseGalois/Hilbert/SymmetricViaHIT.lean`.

## Current route

The theorem is proved directly by the uniform Hilbert-irreducibility construction:

```
perm_fin n
    n = 0: the trivial group
      n > 0:
        → exists_full_resolvent
            → exists_resolvent_family
                → ResolventFamily.exists_resolvent_family_core
                → hilbert_irreducibility_theorem
        → sn_realizable_of_root
            → card_gal_eq_factorial_of_root
            → galActionHom_bijective_of_card_eq_factorial_sep
            → of_galActionHom_bijective_sep
```

Previously, `perm_fin` separately dispatched the cases `0, …, 5` and used a second
wrapper theorem only from degree six onward. That duplicated the case distinction already
implicit in the general construction. The single remaining `perm_fin` theorem handles degree zero directly and uses the resolvent construction
for every positive degree.

## Degree management

The pure Galois-theory lemmas now state their conclusions at the intrinsic degree
`f.natDegree`:

* `card_gal_eq_factorial_of_root` concludes
  `Nat.card f.Gal = f.natDegree.factorial`;
* `of_galActionHom_bijective_sep` realizes
  `Equiv.Perm (Fin f.natDegree)`;
* `sn_realizable_of_root` has the same intrinsic-degree conclusion.

Consequently these lemmas no longer carry a separate natural number `n` and a redundant
hypothesis `f.natDegree = n`. The equality is needed only once, at the boundary where the
specialized polynomial is connected back to the requested degree.

## Verification

The complete `InverseGalois` target builds successfully. A kernel-axiom check for `IsInverseGalois.perm_fin` reports only:

* `propext`,
* `Classical.choice`, and
* `Quot.sound`.

In particular, neither theorem depends on `sorryAx`.
