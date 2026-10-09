# Literal canonical K-group additivity and K₀ commutativity

## Checked mathematical endpoint

Import `Quillen.Waldhausen.Additivity.GroupFormula`.
All three implementation modules compile warning-free.

- `Additivity.K_mul_comm W n a b` proves commutativity of the existing actual
  homotopy-group multiplication in every K-degree, including K₀.
- `Additivity.KCommGroup W n` packages a commutative-group structure whose
  underlying Group is definitionally the original Group. It is explicitly
  available and does not replace any operations globally.
- `Additivity.KMap_sum_apply V W hH hF n x` identifies the original canonical
  K-map of the actual chosen coproduct functor with literal multiplication
  of the original two canonical K-maps.
- `Additivity.KMap_additivity_mul V W a b hs n x` proves the actual structural
  cofibration-sequence formula in subobject-then-quotient order:

      KMap hs.exactG n x = KMap hs.exactF n x * KMap hs.exactH n x.

The formula retains the displayed genuine `IsCofibrationSequence`, the
original KMap normalization, and the original group multiplication.

## Proof mechanism

The genuine coproduct exact functor C×C→C induces a group homomorphism from
K(C)×K(C) to K(C), through the already-checked original projection product
K-equivalence. The actual exact functors X↦(X,0) and X↦(0,X), their original
canonical K-maps, and the literal coproduct-inclusion natural isomorphisms
prove both unit restrictions are the identity.

Every pair (a,b) factors as (a,1)(1,b). Homomorphism multiplicativity therefore
identifies coproduct with the existing product a*b. Factoring the same pair
in the opposite order proves commutativity, without assuming it at degree
zero. Original K-map composition and actual exact pairing identify the
pointwise coproduct functor map with that homomorphism. The accepted based
cofibration-sequence theorem then supplies the displayed literal formula.

## Frozen boundary and verification

The manifest `logs/waldhausen-kgroup-formula-sources.sha256` lists:

- `Quillen/Waldhausen/Product/Functoriality.lean`
- `Quillen/Waldhausen/Additivity/GroupMultiplication.lean`
- `Quillen/Waldhausen/Additivity/GroupFormula.lean`

Its fingerprint is
`c52e5c99641eb25de464ad156c8262410e2dfd0350c055ff42973a415f2c737d`.
The recursive origin audit is `audits/WaldhausenKGroupFormulaAudit.lean`.
It includes arbitrary common object/hom universes, explicit K₀ consumers,
exact preservation of the original Group structure, and the genuine
bounded-acyclic truncation sequence. All 32 defining-module declarations passed recursive standard-axiom audit,
and every consumer passed warning-free. The initial evidence is
`logs/waldhausen-kgroup-formula-check.log`; the final fixed32 rerun passed
in `logs/quillen-kgroup-adapter-check.log`.

## Scope retained

The generic product theorem allows arbitrary common object/hom universes.
The full extension-category product equivalence retains its honest common
object/hom-universe restriction. No unrestricted realization-product
homeomorphism, fibration theorem, Gillet–Waldhausen equivalence, or vanishing
of the isomorphism-model acyclic K-theory is assumed or asserted.

## Original Quillen K-group adapters

The separately frozen pair `QuillenComparison/KCommutativity.lean` and
`QuillenComparison/ExactAdditivity.lean` transfers these results along the
accepted canonical Q/S group equivalence and its canonical exact-functor
naturality square.

- `ExactStructure.K_mul_comm E n a b` proves commutativity of the original
  Quillen K-group law, including K₀.
- `ExactStructure.KCommGroup E n` extends exactly its original Group.
- `ExactFunctor.KMap_conflation_additivity F G H a b w hc n x` proves
  `G.KMap n x = F.KMap n x * H.KMap n x` from a pointwise actual conflation
  sequence of three genuine exact functors.

No strict-zero-preservation assumption is added. The relative-cofibration
condition is derived by the accepted genuine exact-functor sequence adapter.
The original Quillen KMap API, its zero normalization, and its multiplication
remain unchanged. No Grothendieck presentation comparison is asserted.

Both sources compile warning-free. All three defining-module constants and
arbitrary-universe/original-group/n=0/exact-KMap consumers passed the final
fixed3 recursive standard-axiom audit in
`logs/quillen-k-adapter-and-coverage-review-fixed.log` before the independently
checked coverage3 rebuild. The source manifest is
`logs/quillen-kgroup-adapter-sources.sha256`; the audit is
`audits/QuillenKGroupAdditivityAudit.lean`.
