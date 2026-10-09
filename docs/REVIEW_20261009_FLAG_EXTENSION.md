# Admissible flag pullback and extension support, 2026-10-09

## Result and scope

The new support modules `Quillen/Waldhausen/QuillenComparison/FlagPullback.lean`
and `FlagExtension.lean` are checked and frozen for the Q/S reconstruction
worker. These are helper theorems, not a claim that the remaining essential
surjectivity or complete Q/S comparison has been proved.

For an arbitrary exact category `C : Type u` with `Category.{v} C`, an
admissible flag `A : Fin (n + 1) ⥤ C`, a deflation
`p : P ⟶ A.obj (Fin.last n)`, and an inflation `r : P ⟶ Z`,
`extendedPullbackFlag E A p hp r` is an actual functor with object sequence

```
0, P ×_(top A) A₀, …, P ×_(top A) Aₙ, Z.
```

`extendedPullbackFlag_inflation` proves admissibility of every arrow. The
constructor and this theorem have no extra pullback-existence hypothesis:
the exact-category deflation axiom supplies all required instances inside
the construction. In particular, no essential-surjectivity, resolution,
projectivity, balancedness, or quotient-comparison conclusion is assumed.

## Actual maps and universal properties

* `pullbackFlag` uses the chosen categorical pullbacks and their universal
  lifts. `pullbackFlag_map_isPullback` establishes each comparison square.
* `pullbackFlagToOriginal_deflation` and `pullbackFlag_inflation` prove the
  required exactness properties from those squares.
* `pullbackFlagTopIso` identifies the last pullback with `P`; its forward
  map is exactly the first projection. If `A.obj 0` is zero,
  `pullbackFlagInitialKernel` supplies the actual kernel universal property
  of the first pullback projection against `p`.
* `zeroPrefixFlag` is ordinary precomposition by `0 ⟶ A.obj 0`.
  `appendFlag` is the standard finite-arrow constructor on the old adjacent
  maps followed by the supplied final arrow. All intermediate transports
  are explicit equality isomorphisms.
* `appendFlagRestrictionIso` identifies the old subflag, and
  `appendFlag_to_last` proves the actual map to the new target is the old
  top map followed by the prescribed final arrow.
* The middle indices of the full extension are `i.castSucc.succ`.
  `extendedPullbackFlagMiddleIso` identifies that entire subflag with the
  original pullback flag. `extendedPullbackFlag_middle_to_last` proves that
  its actual maps to `Z`, after the canonical object identifications, are
  exactly `pullback.fst p (flagTopMap A i) ≫ r`.

The generic pullback constructions and comparison APIs take the usual
`HasPullback` instances to expose their actual objects. These instances are
proved by `flagPullback_exists E A p hp`; they are not a missing existence
obligation in the main extension endpoint.

The Q/S worker separately owns `PullbackQuotients.lean`, including the
canonical interval-quotient comparison. That module is not part of this
helper's kernel audit or frozen source manifest.

## Verification

Both actual sources were elaborated with Lean 4.34.0, `-j1`, under
`flock /tmp/quillen-lean-slot-1.lock`, producing normal importable oleans.
The only reported messages are non-fatal style/linter warnings.

* `logs/q-s-flag-pullback.log`: successful actual-source check.
* `logs/q-s-flag-extension.log`: successful actual-source check.
* `audits/FlagExtensionIndependentAudit.lean`: recursive axiom collection
  for **every declaration whose origin is either module**, including
  generated and private declarations; also checks an arbitrary-universe
  consumer producing the entire admissible flag without `HasPullback`
  assumptions.
* `logs/q-s-flag-extension-axioms.log`: **83 declarations passed**,
  35 from `FlagPullback` and 48 from `FlagExtension`. Every recursive axiom
  dependency belongs to `{propext, Classical.choice, Quot.sound}`.
* `logs/q-s-flag-extension-hashcheck.log`: both frozen sources match after
  the audit.

## Frozen fingerprints

```
f92f2392e55e72681e75af1ed74fdd832394e52537033c08d7d7b63dc58d0afc  Quillen/Waldhausen/QuillenComparison/FlagPullback.lean
58ae40f7d62783e3546ba5bb6097c4a76a9321529ac37d4c3b71d59788593dd9  Quillen/Waldhausen/QuillenComparison/FlagExtension.lean
09f1a296428292a8a3a92a56c1af8d2a02fb4da4035495c0851f9dfd4a11b541  logs/q-s-flag-extension-sources.sha256
5f78e34c2eae4af867665e8d83c605bed8b6268a21ae48e3725b21eb8384711c  audits/FlagExtensionIndependentAudit.lean
54b744ec2eee6bc73a5abd7f1d7dce0d3fedae8ad46dae37589e54280c0d3215  logs/q-s-flag-extension-axioms.log
```

This branch has not modified the previously accepted regular-scheme,
Q-core, or classification-diagonal source files.
