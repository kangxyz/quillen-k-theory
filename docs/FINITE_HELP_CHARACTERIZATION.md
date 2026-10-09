# Exact finite HELP characterization

Independently accepted 2026-10-09 14:24:57 UTC.

Fresh source checking, all four original declarations and thirteen strengthened
consumers passed. See [the independent review](REVIEW_20261009_FINITE_HELP_CHARACTERIZATION.md).

`Topology/HELP/FiniteCharacterization` characterizes the complete original
weak-equivalence property by literal finite boundary lifting of the actual
mapping-path endpoint, and by full prescribed-boundary HELP on every actual
finite cube. Dimension zero is included. No arbitrary compact-pair extension,
CW hypothesis or ordinary homotopy inverse is asserted.

The reverse direction applies the already accepted finite boundary-lifting
weakness theorem to the original endpoint and composes with the genuine
original mapping-path inclusion homotopy equivalence. The composite equals
the original map definitionally. The forward direction uses the independently
accepted full finite HELP theorem. PairLifting converts exact finite HELP to
the original strict endpoint lifting while retaining every stored path.

The source check is warning-free. All four original declarations and eight
consumers passed the recursive axiom audit with only standard logical
foundations. Consumers include the original arbitrary boundary homotopy,
identity maps, the empty-source/nonempty-target obstruction, actual endpoint
lifts and actual endpoint point-surjectivity. An initial review-counter type
inference error was repaired by explicitly annotating Nat; no source proof
changed. The audit now fixes the observed origin count at four.

Source manifest: `logs/finite-help-characterization-sources.sha256`.
Audit: `audits/FiniteCharacterizationAudit.lean`.
Source and audit logs: `logs/finite-help-characterization-check.log` and
`logs/finite-help-characterization-audit.log`.
This source is now integrated publicly and remains outside delivered version 8.
