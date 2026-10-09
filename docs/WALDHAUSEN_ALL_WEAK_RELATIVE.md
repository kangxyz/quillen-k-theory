# All-weak structure and the actual identity-relative total

## Contract

The three new modules under `Quillen/Waldhausen/Fibration/AllWeak` prove a
scoped prerequisite for the remaining double-S/fibration assembly.

- `Basic.waldhausenStructure W` retains the original category, cofibrations,
  chosen zero and all actual pushout data, and sets the weak class to all
  morphisms. Its gluing, saturation and extension axioms are proved.
- `zeroToIdentity W` has precisely the original unique zero-to-object maps.
  `zeroToIdentityHomotopy W` is their actual S-realization homotopy from the
  original chosen zero to the identity. Its zero track is literally constant.
  `contraction W` is its reverse, and gives contractibility of this all-weak
  S-realization. These results retain independent object and hom universes.
- `CoproductCylinder.coproductJointData W` uses the original coproduct
  `source(f) ⨿ target(f)`, identity joint arrow and projection `[f,id]`.
  Its genuine Reedy exactness follows from the already proved exact sum
  functor and exact identity-arrow embedding. It preserves the original
  fine weak maps. Both endpoint identities are proved on the original
  maps; only the projection's weakness uses the new all-weak class.
  `jointData W` obtains the needed coproducts from the Waldhausen axioms.
- In the explicit common-universe case, `relativeEvaluationHomotopyEquiv W`
  applies the proved original relative-to-coarse evaluation to these actual
  structural inputs. Its forward map is literally that original evaluation,
  and preserves the actual relative zero. Consequently
  `relativeTotal_contractible W` proves contractibility of the actual
  relative total for `AllWeak.nested W`.

No cylinder, saturation or extension hypothesis on the original fine
structure W is required. In particular this applies to the actual inherited
fine structure on the acyclic category and to actual inner quotient-row
categories. This does not declare the original fine realization contractible.

## Role and remaining obligations

Every object is acyclic for the all-weak coarse structure, so this is the
identity-relative case of the existing actual relative model. The total is
contracted via the genuine relative-to-coarse equivalence and the original
all-weak zero transformation, rather than by asserting an extra degeneracy.

The relationship between identity-relative contractibility and double-S
loops is described in [Weibel, V.1.7.1](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.V.pdf).
Here the contractibility prerequisite is proved independently of a fibration
theorem. The following remain separate actual proof obligations:

1. The global relative-realization fiber theorem for the original tail map.
2. The original all-acyclic full-category/double-S base identifications.
3. The loop or fiber-exchange comparison, with the original canonical
   reversed zero-to-acyclic-inclusion path, rather than merely an abstract
   equivalence of spaces.

The based assertion here concerns the actual all-weak contraction and the
forward relative evaluation. No based inverse of the relative evaluation,
relative-total based contraction, double-S delooping equivalence, or
homotopy-fiber equivalence is supplied as a hypothesis or claimed as a
consequence of contractibility alone.

## Verification

Focused source checks and a single-pass recursive source-origin audit are
recorded in `logs/all-weak-*-check.log` and `logs/all-weak-relative-audit.log`.
The consumer file is `audits/AllWeakRelativeAudit.lean`; it checks independent
universes, original coproduct endpoint/projection maps, genuine Reedy
exactness, original zero tracks, exact relative forward map and basepoint,
actual acyclic and quotient-row categories, and bounded termwise complexes.
The terminal fixed44 audit (26 Basic +14 CoproductCylinder +4
RelativeContractible origins) and all23 consumers pass warning-free in
`logs/all-weak-relative-audit-final.log`. All recursively used axioms are
`propext`, `Classical.choice`, and `Quot.sound` only. Frozen production hashes
are in `logs/all-weak-relative-sources.sha256`. Independent review passed: fresh three-source rebuild, fixed44 recursive
origin audit and31 strengthened original-map consumers, with all hashes
unchanged. The independent review evidence is maintained separately.
