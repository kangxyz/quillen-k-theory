# Recursive reconstruction indices, 2026-10-09

`Quillen/Waldhausen/QuillenComparison/ReconstructionIndices.lean` is checked
and frozen. It supplies only the indexing and generic chain-isomorphism
prerequisites of the pending Q/S essential-surjectivity proof.

* `reconstructionMiddleOrdinal n` is an actual increasing ordinal map
  `ε[n] → ε[n+1]`, with value exactly `k + 1`.
* `reconstructionMiddle_size` and
  `reconstructionMiddleOrdinal_eq_castSucc_succ` identify it with the
  literal middle indices of the actual two-endpoint flag extension.
* `reconstructionMiddleOrdinal_lower`, `_upper`, and `_central` prove the
  recursive central-interval formulas.
* `reconstructionMiddle_centralFunctor` proves the equality of complete
  initial central chains, including maps.
* For every category `D : Type u` with `Category.{v} D`, `chainIsoMkLast`
  extends a natural isomorphism on the initial subchain and a terminal
  object isomorphism. Its only compatibility hypothesis is the actual last
  adjacent naturality square. The component and restriction lemmas recover
  precisely the supplied data. No fullness or essential-surjectivity
  conclusion is included in its inputs.

Verification used direct `lean -j1` under `/tmp/quillen-lean-slot-1.lock`,
producing the normal olean. `audits/ReconstructionIndicesAudit.lean` tested
an arbitrary-universe generic category consumer and recursively audited
all declarations originating in this module, including generated/private
constants. All **29 declarations passed**, with only `propext`,
`Classical.choice`, and `Quot.sound` as recursive axioms.

Evidence:

* `logs/q-s-reconstruction-indices.log`
* `logs/q-s-reconstruction-indices-axioms.log`
* `logs/q-s-reconstruction-indices-hashcheck.log` (unchanged source)

Frozen SHA256:

```
1845567a2df4189eaa08488cc9b361812d0d7de59f53a877f0c887d463efc139  Quillen/Waldhausen/QuillenComparison/ReconstructionIndices.lean
707d5f69a86f83f57292225f32769712c3358006588307bd08fd3d8f700829ad  logs/q-s-reconstruction-indices-sources.sha256
6475e2e61be40057f281f212c70b752de1a3b882f9442937f9b0cc647c4adcb5  audits/ReconstructionIndicesAudit.lean
```
