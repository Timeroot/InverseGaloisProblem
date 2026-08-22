import InverseGalois.Solvable.ChiefSeries
import InverseGalois.Solvable.Nilpotent
import InverseGalois.Solvable.Wreath
import InverseGalois.Solvable.WreathFunctor
import InverseGalois.Solvable.WreathRecognition
import InverseGalois.Solvable.Semiabelian
import InverseGalois.Solvable.SemiabelianProduct
import InverseGalois.Solvable.Metacyclic
import InverseGalois.Solvable.SemiabelianCriterion
import InverseGalois.Solvable.SemiabelianHall
import InverseGalois.Solvable.SemiabelianSmall
import InverseGalois.Solvable.SemiabelianZGroup
import InverseGalois.Solvable.WreathCyclic
import InverseGalois.Solvable.Shafarevich

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
* `InverseGalois.Solvable.WreathRecognition` recognizes a group as a regular wreath product from a
  cocycle of coordinates together with a count, which is how a Galois group acting on conjugate
  layers of a field extension is identified.
* `InverseGalois.Solvable.Semiabelian` defines Dentzer's class of semiabelian groups — the class
  the wreath-product approach reaches — and derives a realization of every one of its members from
  a realization of the wreath products alone.
* `InverseGalois.Solvable.SemiabelianProduct` shows that the semiabelian class is closed under
  finite direct products, and deduces that a finite nilpotent group is semiabelian as soon as each
  of its Sylow subgroups is.
* `InverseGalois.Solvable.Metacyclic` shows that a finite group with a cyclic normal subgroup of
  cyclic quotient is semiabelian, and applies it to the generalized quaternion groups.
* `InverseGalois.Solvable.SemiabelianCriterion` shows that a group covered by a semidirect
  product of an abelian group by a semiabelian one is semiabelian, and deduces that a finite group
  with a normal abelian subgroup of cyclic quotient is semiabelian.
* `InverseGalois.Solvable.SemiabelianHall` supplements a normal abelian subgroup by a complement
  instead of by a cyclic group: a group with a normal abelian subgroup of coprime index, or with a
  normal abelian Sylow subgroup, is semiabelian as soon as the quotient is.
* `InverseGalois.Solvable.SemiabelianSmall` applies the criterion to the small orders: a group with
  an abelian subgroup whose index is the smallest prime factor of the order is semiabelian, and so
  is every group of order `p`, `p ^ 2`, `p ^ 3` or `p * q`.
* `InverseGalois.Solvable.SemiabelianZGroup` shows that a finite group all of whose Sylow subgroups
  are cyclic is metacyclic, hence semiabelian; in particular every group of squarefree order is.
* `InverseGalois.Solvable.WreathCyclic` splits the bottom group of a wreath product into cyclic
  factors, so that the realization of wreath products only has to be established when the bottom
  group is finite cyclic.
* `InverseGalois.Solvable.Shafarevich` carries out Ore's reduction of the whole theorem to split
  embedding problems with kernel of prime power order, which is where the arithmetic input is
  concentrated.
-/
