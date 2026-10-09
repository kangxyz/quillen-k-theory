# Compact HELP over a displayed contracted base

`HomotopyFiber.ContractibleBase` and `ContractibleBaseHELP` retain the
original fiber projections and strict-fiber inclusions. A displayed homotopy
from the base identity to its constant map supplies a genuine point-inclusion
homotopy equivalence. The actual parameter equivalence for homotopy pullbacks
then makes the original homotopy-fiber projection a homotopy equivalence,
without assuming a fibration. Genuine Hurewicz lifting supplies the strict
fiber version. The contraction need not fix the chosen point during time.

Proved compact HELP composition and cancellation transport HELP on the
original fiber map to the original total map over that contracted base.
This does not assert gluing over an arbitrary base or construct a continuous
family of inverses from compact lifts.

Both sources compile warning-free. `audits/ContractibleBaseHELPAudit.lean`
checks all12 defining origins recursively against the standard three axioms
and eight consumers retaining original maps and source coordinates.
The source manifest is `logs/contractible-base-help-sources.sha256`.
Independent review is complete: see
[the independent review](REVIEW_20261009_CONTRACTIBLE_BASE_HELP.md).
Both files are integrated into the public umbrella.
