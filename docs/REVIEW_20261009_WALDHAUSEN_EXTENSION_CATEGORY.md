# Independent review: genuine Waldhausen extension category

Date: 2026-10-09. Result: **accepted for the six-source structural endpoint**.
No production source was modified.

## Accepted mathematical and Lean contract

For an arbitrary `W : Waldhausen.Structure C`, with `C : Type u` and
`Category.{v} C`, `ExtensionCategory.Obj W` is the actual full subcategory of
`Arrow C` on arrows belonging to `W.cof`. It has objects in `Type (max u v)`
and morphisms in `Type v`. There is no additive, abelian, smallness, or global
cocompleteness hypothesis.

The proved `waldhausenStructure W` has exactly componentwise weak equivalences.
Its cofibrations require a cofibration on sources and a cofibration on the
actual relative target comparison from the chosen pushout. The two relative
comparison lemmas prove equivalence with the same test using **any** displayed
relative pushout and its compatible comparison map. Thus the condition is not
an unexplained restriction to a selected witness.

All structure fields are derived from `W`:

- Composition uses the genuine source-change pushout of relative comparisons.
- The displayed pushout-cube theorem proves the new relative comparison is an
  actual cobase change of the old one, using pushout pasting and cancellation.
- The componentwise pushout arrow is proved to be a cofibration before it is
  admitted as an object. Its new leg is then proved Reedy-cofibrant. No closure
  conclusion is assumed while constructing this object.
- The arrow-category pushout universal property is constructed explicitly and
  reflected through the fully faithful full-subcategory inclusion.
- Comparing an arbitrary extension-category pushout to the constructed one
  establishes that both projections preserve all pushouts along these
  cofibrations. Cofibration stability and the two component gluing axioms then
  follow from the actual component squares.
- The chosen zero is the literal identity arrow of `W.zero`; the zero-object
  property and cofibrancy of every object are proved.

The exact functors `source W` and `middle W` are the actual source and target
projections. `cofiber W` is the actual categorical pushout of the original
cofibration along the canonical map to `W.zero`, via the existing genuine
pushout functor. Its object/map formulas, quotient projection, and cofiber
square are retained. Exactness follows from actual pushout interchange,
cofibration preservation, and gluing, applied to the proved structural
inclusion transformation.

The final theorem `isCofibrationSequence W` proves the complete existing
`Additivity.IsCofibrationSequence` predicate for
`source W → middle W → cofiber W`: three exactness statements, the pointwise
and relative cofibration condition, and the actual cofiber square. The desired
sequence is a theorem; it is not passed as an input.

I read all six sources and the relevant definitions/proofs in
`Waldhausen.Basic`, `Additivity.CofibrationSequence`,
`Additivity.PushoutCofibrations`, and `Additivity.PushoutPreservation`.
No circular structural hypothesis or hidden realization/K-theory assertion was
found. In particular, the structural pushout-functor dependencies are ordinary
categorical results and do not assume additivity.

## Independent checking

The selected six oleans were rebuilt from the frozen source files into
`logs/extension-category-independent-20261009/olean`, in dependency order.
Unchanged dependency artifacts were linked into that isolated namespace;
the six reviewed artifacts themselves were fresh regular files. No live Lake
build or replacement of the author's production oleans was used. Compilation
used Lean 4.34.0, `-j1`, and the shared slot1 lock, with acquisition time logged.

The fresh-source log and the independent audit contain no warnings or errors.
`lean --deps` records that the final module selects the isolated `Structure`
artifact. The audit imports the fresh final module through the same overlay.

`audits/ExtensionCategoryIndependentAudit.lean` independently runs a fixed
**64-origin** scan, including every private/generated declaration defined by
the six modules. Recursive `collectAxioms` permits only `propext`,
`Classical.choice`, and `Quot.sound`. All 64 pass. No `sorry` or new axiom is
present in the reviewed sources.

Arbitrary independent object/hom-universe consumers verify the category sizes,
exact cofibration/weak classes, arbitrary pushout preservation, all three
exact functors, the original arrow and quotient formula, and the actual
structural sequence. Additional independent consumers check:

- the chosen zero is literally the identity arrow;
- source and middle maps are literally the original square components;
- the Reedy condition is equivalent to the test using any displayed relative
  pushout;
- the actual pointwise pushout existence theorem, including the new Reedy leg;
- the actual cofiber object and morphism formulas through the terminal-arrow
  and relative-pushout functors.

All six source hashes matched both before and after the independent run.

## Exact limits

This accepts a genuine extension-category Waldhausen structure and its
structural source/middle/cofiber sequence. It does not assert an extension
category K-equivalence, a product decomposition of K-groups, a fibration or
Gillet–Waldhausen theorem. The later `Embeddings` and `InternalSequence` sources
are not part of this six-file review. The object-universe increase to `max u v`
is explicit; this review makes no raw cross-universe K-map identification.

## Frozen sources

Manifest: `logs/extension-category-independent-20261009/sources.sha256`

Manifest SHA-256:
`bcafa36fc1e888a9e320c6060903181b8855b16d06e866b2a38f209e2fb067f9`

- `Basic.lean`: `5d05256bd908092fede19617574b46c4daf62f08960ee9b7a7d525a941386f21`
- `PushoutCube.lean`: `60f3ab205ac9ae9ba03e383c899c8ccb110d27e21d5ce01167cad4d9a4f33a8a`
- `RelativeCofibrations.lean`: `2fd0dced73f579e1dc33e4c94db9660f7452bbbb223279723be0f0e57f333c2d`
- `ArrowPushouts.lean`: `763ee1b08f7d79eec9438c9919a9a69f458f8888b1406450ce2199279fcaee9d`
- `Structure.lean`: `40b4bfee6700c9ccbd64c53d5e59d76855ac0cdd4d50b2c84acc84ac62291ceb`
- `Cofiber.lean`: `305f19824a69a8fe7f931b57866cd5fb1ac37f0f3d7dc11eaeb7a1bf16f4491b`

## Evidence

Directory: `logs/extension-category-independent-20261009/`

- `check.log`: fresh ordered six-source compilation
- `audit.log`: fixed64 recursive origin scan and exact consumers
- `deps.log`: selected dependency paths
- `hashes-before.log`, `hashes-after.log`: source rechecks
- `artifacts.sha256`: exact independent audit, logs, report and six fresh oleans

Independent audit SHA-256:
`cc134660164207074add644f2ce35fc8f429790cfa0131a710ec781ef670cba7`

Audit log SHA-256:
`ddf496e0899d80d9839b47bbcccc87e0ac4670de516d986fa73a67bb77ba73f6`
