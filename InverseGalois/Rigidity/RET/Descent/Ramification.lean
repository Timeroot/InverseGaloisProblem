/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Descent.TameRamification
import InverseGalois.Rigidity.RET.Descent.GeomAKLB
import InverseGalois.Rigidity.RET.Descent.ArithAKLB
import InverseGalois.Rigidity.RET.Descent.TameCharacter
import InverseGalois.Rigidity.RET.Descent.WildInertia

/-!
# Ramification theory for the geometric branch-cycle datum

This module collects the ramification-theoretic content used to describe the tame inertia at the
branch points of a geometric Galois cover.

* `TameRamification` — the order of an inertia element of a Galois action on a Dedekind extension
  divides the ramification index, and inertia transports along the action on primes.
* `GeomAKLB` — the integral model `k[X] ⊆ B = integralClosure (k[X]) Ω` for a finite Galois
  extension `Ω/k(T)` over an algebraically closed constant field `k`, with its full instance stack,
  geometric places `(X - t)`, char-zero residue separability, and the ramification lemmas applied.
* `ArithAKLB` — the same model over the rational base, `ℚ[X] ⊆ B = integralClosure (ℚ[X]) Ω` for a
  finite Galois extension `Ω/ℚ(T)`, carrying the arithmetic Galois action; inertia there is cyclic
  and satisfies Fried's branch-cycle formula with the cyclotomic exponent.
* `TameCharacter` — the tame character `θ : inertiaSubgroup → (ResidueField A)ˣ` of a discrete
  valuation subring, well-defined, uniformizer-independent, and a group homomorphism.
-/
