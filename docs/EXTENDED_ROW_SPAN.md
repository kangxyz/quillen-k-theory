# The actual terminal span of an extended exact row

Implementation: `Quillen/Waldhausen/QuillenComparison/ExtendedSpan.lean`.
Source manifest: `logs/extended-span-sources.sha256`.

## Checked interface

For an admissible finite flag A, an actual deflation p from P to its final
term and an actual inflation r from P to Z:

- `extendedMiddleInterval` selects the entire old ordinal inside its two-endpoint
  extension.
- `extendedRowInitialIso` identifies the extended flag with the initial flag of
  its cokernel-completed row, by the actual quotient projections.
- `extendedRowApexIso` identifies the terminal middle initial quotient with P.
- `extendedRowTopIso` identifies the new whole quotient with Z.
- `extendedRepresentative` has precisely apex P, left leg p followed by the old
  whole-interval quotient projection, and right leg r. Both admissibility proofs
  are supplied from the exact structure.
- `extendedRow_wholeSpan` identifies the actual whole-span Q-arrow with that
  representative under the displayed middle-source and terminal-target isomorphisms.
- `extendedRepresentative_initialFlag` specializes to the initial flag of an
  existing exact row. The canonical completed-initial-row isomorphism removes
  the old whole-interval quotient, leaving exactly the prescribed span (p,r).

The final endpoint theorems quantify over arbitrary object and hom universes
and require no caller-supplied pullback instances or reconstruction hypothesis.

## Proof

The initial quotient projections are isomorphisms because the extended flag
starts at a genuine zero. Canceling those projections reduces the left-leg
identity to `flagQuotient_extendedRowMiddleIso` and the terminal pullback
condition. The right-leg identity reduces to naturality of initial completion
and `extendedPullbackFlag_middle_to_last`. The actual Q-arrow identity then
follows from `qSpan_iso_naturality` with these explicit apex and endpoint
isomorphisms. The specialization uses the cokernel-comparison formula and the
identity initial quotient of the whole row.

## Verification and boundary

The implementation compiles warning-free with its matching olean.
`audits/ExtendedSpanAudit.lean` recursively audits every declaration origin and
checks the exact leg formulas and both endpoint identities in arbitrary
universes. All 24 declarations passed, with only `propext`, `Classical.choice`
and `Quot.sound`; the audit is count-frozen at 24. Logs are
`logs/extended-span.log` and `logs/extended-span-audit.log`.

This module supplies the terminal-span step of the finite-chain reconstruction.
The full essential-surjectivity and Q/S equivalence assembly belongs to separate
modules. No earlier frozen implementation source was edited.
