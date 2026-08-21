import InverseGalois.Solvable.ChiefSeries
import InverseGalois.Solvable.Nilpotent
import InverseGalois.Solvable.Wreath
import InverseGalois.Solvable.WreathFunctor
import InverseGalois.Solvable.Semiabelian

/-!
# Solvable groups as Galois groups

Shafarevich's theorem states that every finite solvable group is a Galois group over `ℚ`.  Its
proof is arithmetic — it runs through embedding problems, class field theory and the
Grunwald–Wang theorem — and the *regular* analogue over `ℚ(T)` is not known even for `p`-groups.
This directory collects the group-theoretic reductions that organize the approach, each of them
free of arithmetic input and applicable to both realization predicates of the development.

* `InverseGalois.Solvable.ChiefSeries` peels a finite solvable group apart along elementary
  abelian normal subgroups, reducing the problem to embedding problems with elementary abelian
  kernel.
* `InverseGalois.Solvable.Nilpotent` assembles a finite nilpotent group from its Sylow subgroups,
  reducing the nilpotent case to `p`-groups.
* `InverseGalois.Solvable.Wreath` presents every semidirect product `A ⋊[φ] H` with `A` abelian as
  a quotient of the single regular wreath product `A ≀ᵣ H`, so that a realization of the wreath
  product realizes every split extension of `H` by `A` at once.
* `InverseGalois.Solvable.WreathFunctor` makes `A ≀ᵣ H` functorial in both arguments and exhibits
  `(A₁ × A₂) ≀ᵣ H` as a quotient of the iterated wreath product `A₁ ≀ᵣ (A₂ ≀ᵣ H)`, which lets a
  realization of wreath products propagate along quotients of either factor.
* `InverseGalois.Solvable.Semiabelian` defines Dentzer's class of semiabelian groups — the class
  the wreath-product approach reaches — and derives a realization of every one of its members from
  a realization of the wreath products alone.
-/
