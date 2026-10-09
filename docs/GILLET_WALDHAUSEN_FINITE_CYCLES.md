# Genuine finite acyclic-cycle K-decomposition

## Contract and indices

The six new modules `FiniteCycleBounds`, `FiniteCycleFiltration`,
`FiniteCycleEvaluation`, `FiniteCycleKFormula`, `FiniteCycleKEquivalence`,
and `FiniteCycleIncidence` retain actual complexes and original maps.

Let A be abelian. Let P contain zero, be replete, extension-closed, and
closed under kernels of ambient admissible epimorphisms between P-objects.
The endpoint is `finiteCycleKEquiv P a m k`. Its source is the original
isomorphism-weak Waldhausen K-group of the inherited exact category of
bounded acyclic termwise-P complexes with actual term bounds `[a,a+m]`.
Its target is `Fin m` copies of the original inherited exact-category
K-group of P. The forward coordinate at i is definitionally the original
public normalized `KMap` of cycle evaluation in degree `a+i+1`. The inverse
is literally the finite product of the original public disk-insertion
`KMap`s, with the identity disk occupying degrees `a+i,a+i+1`.

Thus the free cycles are the interior degrees `a+1,...,a+m`. For a term
interval `[a,a+r-1]` there are `r-1` free coordinates when `r>0`. The proved
formula includes m=0: a genuinely acyclic single-term stratum has trivial
K-groups. The finite-layer theorem also covers empty intervals. Neither
acyclicity nor the isomorphism-weak acyclic category is assumed to have
trivial K-theory in general.

## Actual proof inputs

- Exactness and the actual epimorphism from the preceding zero term prove
  that cycles at and below the lower term bound vanish. Above the upper
  bound, the actual cycle inclusion into a zero term proves vanishing.
- Original smart truncation preserves every specified actual term bound.
  Its lower endpoint is already zero at a, and its upper endpoint is
  naturally identity at or beyond the upper term bound. The identity
  isomorphism retains the original truncation inclusion as its forward map.
- The original adjacent maps are a genuine structural cofibration sequence
  inside the same actual stratum. The quotient is the original identity
  disk on the next cycles. Its bounds follow from the actual quotient epi.
- The original disk's upper-cycle inclusion identifies its unique free
  cycle naturally with the inserted object. All other cycles are zero.
- Genuine canonical literal K-map additivity yields the finite layer
  formula. These identities and the actual disk-cycle evaluation natural
  isomorphisms prove both inverse identities of the group equivalence.

No equivalence, formal additive identity, projectivity, global uniform
bound, or geometric resolution hypothesis is an input. The cycles and
terms are evaluated in the isomorphism weak models. Such evaluations are
not asserted to preserve quasi-isomorphisms.

## The original inclusion matrix

`finiteAcyclicTermsInclusion` retains the actual complex and chain map.
Its exactness itself needs no kernel closure. On its original K-map,
`finiteCycle_KMap_incidence` proves

`term_j(inclusion(x)) = cycle_j(x) * cycle_(j+1)(x)`.

This is the existing K-group multiplication and original public `KMap`.
The original cycle inclusion and differential-to-cycles maps are the
arrows of the proved structural cofibration sequence used to derive it.
The lower factor at a and upper factor at b+1 vanish by the actual bound
lemmas. `finiteCycle_KMap_incidence_lower` and `_upper` retain these original
maps; `finiteCycleKEquiv_incidence` expresses interior terms in the proved
finite-cycle coordinates. In particular, a disk coordinate contributes
identically to its two adjacent term coordinates. The inclusion is not
claimed to be zero.

## Universes and schemes

Raw algebra, filtration, and finite endofunctor formulas allow independent
object and morphism universes. Mixed evaluation/insertion K-map results
explicitly use `A : Type (max u v)` and `Category.{v} A`, matching the
accepted finite-term interface. No universe-change equivalence is assumed.
For arbitrary `X : Scheme.{u}`, the direct application is
`finiteCycleKEquiv.{u,u+1} (SchemeSheaf.finiteLocallyFree X) a m k`, using
the independently proved arbitrary-scheme ambient kernel closure. No
noetherian, regularity, resolution-property, or global-projectivity
hypothesis is added.

## Boundary

This is a finite-stratum isomorphism-model theorem. The global finite-support
graded decomposition, filtered based K-group bridge, topological fibration,
and Gillet–Waldhausen comparison remain separate proof obligations.
All previously frozen thirty-four Gillet–Waldhausen sources are unchanged.

## Verification

All six focused source builds passed without warnings or errors. The
aggregate audit and literal original-map, inverse-product, empty-stratum,
K₀, and arbitrary-scheme consumers are in
`audits/GilletWaldhausenFiniteCycleKAudit.lean` with log
`logs/gillet-waldhausen-finite-cycle-k-axioms.log`.
The terminal fixed941 all-forty-source recursive audit passed with all
consumers, no warnings, errors, or `sorryAx`, and only the three standard
logical axioms. The six new origins number 169 (24+37+37+8+33+30).
The frozen manifest is
`logs/gillet-waldhausen-finite-cycle-k-checked-sources.sha256`; all six and
all prior thirty-four source hashes match. Independent six-source review
also passed a fresh isolated rebuild, fixed169 new-origin recursive audit,
and the actual-map consumers, including strengthened lower/upper/interior
inclusion coordinates.
