# Nested weak classes on the same actual quotient-row category

## Endpoint

`Fibration.Rows.NestedWeakEquivalences` packages the coarse pointwise weak
class directly on the existing `QuotientRows.Obj V n` object type.
`RowWeakEquivalences.nested N n` is a genuine
`NestedWeakEquivalences (QuotientRows.waldhausenStructure V n)`.
The cofibration and chosen-zero fields are literally unchanged.

All morphisms are the original natural transformations. Coarse weakness is
exactly `∀ p, N.coarse.weq (f.hom.app p)`. No different coarse-row object
category or hidden categorical model identification is introduced.

## Structural proof

Zero, Reedy cofibrations, their pushouts and cobase-change closure use the
accepted original fine row structure. The new weak class is multiplicative
and contains actual component isomorphisms. Its gluing axiom evaluates the
original displayed row pushouts at each original interval, transfers each
component cofibration along the given equality of base cofibration classes,
and applies the genuine original coarse gluing axiom.

Evaluation and every original ordinal reindexing are proved genuinely exact
for the coarse structures. Their underlying object and map formulas are the
unchanged original functors. Coarse two-out-of-three is inherited pointwise
when it holds in the original coarse structure; no fine saturation is used.

## Scope

Object and hom universes are independent. This is a structural input for
mixed-chain replacement at inner row levels. A genuine row-level cylinder
factorization, its middle-functor exactness and Reedy cofibration preservation
are distinct obligations. There is no realization or fiber conclusion.

## Verification

The focused source check passed warning-free. The initial and final fixed-count
recursive audits passed all 20 declaration origins, permitting only `propext`,
`Classical.choice`, and `Quot.sound`. All 15 consumers passed, including
independent object/hom universes, literal fine/coarse cofibration and zero
identity, original component maps, actual displayed evaluation/reindexing
pushouts, and degree zero. Source hashes were checked before and after the
terminal audit.

- Source manifest: `logs/nested-quotient-rows-sources.sha256`
- Audit: `audits/NestedQuotientRowsAudit.lean`
- Source log: `logs/nested-quotient-rows-check.log` (empty)
- Terminal audit: `logs/nested-quotient-rows-audit-final.log`
- Evidence manifest: `logs/nested-quotient-rows-artifacts.sha256`

Independent review is separate and pending.
