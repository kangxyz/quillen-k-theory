# Reconstructed exact rows and their initial Q-chains, 2026-10-09

## Checked result

`Quillen/Waldhausen/QuillenComparison/ReconstructedRows.lean` is checked
and frozen for the Q/S induction. It assembles the actual flag-extension
construction, rather than assuming a row realization of a chain.

For `F : Row E (ε[n])`, a deflation from `P` onto its initial flag's top,
and an inflation `P ⟶ Z`, the module constructs:

1. `reconstructedRow`: an actual exact row indexed by `ε[n+1]`, obtained
   by restricting `extendedRow` along the displayed ordinal equality cast.
2. `reconstructedMiddleIso`: an actual natural isomorphism from the
   middle restriction to `F`. It composes the exact ordinal reindexing,
   the author's actual quotient comparison `extendedRowMiddleIso`, and
   the uniqueness-of-cokernels map `completedInitialIso`.
3. `reconstructedInitialChainIso`: a natural isomorphism from the initial
   restriction of the reconstructed Q-chain to the original compared chain.

There are no caller-supplied pullback-existence, quotient-comparison,
fullness, or essential-surjectivity hypotheses. The only geometric/algebraic
inputs beyond the exact category and original exact row are the displayed
actual deflation and inflation.

## Canonical component control

`reconstructedInitialChainIso_hom_app` identifies the forward component as
the explicit central-index equality map followed by `qIsoOfIso` of the
actual middle-row component. `reconstructedCentralIsoAt` packages those
original-category maps. `reconstructedInitialChainIso_app` proves that the
entire component is exactly `E.qIsoOfIso (reconstructedCentralIsoAt … i)`;
`reconstructedInitialChainIso_app_last` specializes this to the terminal
object of the old subchain. No unspecified isomorphism is substituted.

`reconstructionMiddle_comp_cast` proves the equality of the actual ordinal
maps with the literal middle embedding used by `extendedPullbackFlag`.

This module does not establish terminal-span compatibility, the induction,
or full Q/S equivalence. Those are separately owned assembly steps.

## Verification and fingerprints

Direct `lean -j1` under `/tmp/quillen-lean-slot-1.lock` succeeded and produced
the normal importable olean. `audits/ReconstructedRowsAudit.lean` checks an
arbitrary-object/hom-universe consumer and recursively collects axioms for
every declaration originating in this source, including private/generated
constants. All **24 declarations passed**, depending only on `propext`,
`Classical.choice`, and `Quot.sound`. The source was rehashed after the audit.

Logs:

* `logs/q-s-reconstructed-rows.log`
* `logs/q-s-reconstructed-rows-axioms.log`
* `logs/q-s-reconstructed-rows-hashcheck.log`

SHA256:

```
44ef842161048bd94af62191dfc911cf43cd5cb0e97bee909cb1c7a7decf9844  Quillen/Waldhausen/QuillenComparison/ReconstructedRows.lean
bf490e0496c9086fa275ef213006febe303372bc3798e0e830857ce99b2faabc  logs/q-s-reconstructed-rows-sources.sha256
f91b53d131bbf49fdbb3eb9b93eef7e6c97406381cf76477a5abe597235901a6  audits/ReconstructedRowsAudit.lean
```

The source-origin audit recursively checks dependency axioms, but is not a
separate semantic acceptance report for the author's upstream quotient-row
modules. The final Q/S reviewer owns that wider acceptance.
