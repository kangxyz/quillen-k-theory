# Canonical based Waldhausen additivity

## Checked endpoint

Import `Quillen.Waldhausen.Additivity.BasedAdditivity`.
For genuine Waldhausen structures `V : Structure C`, `W : Structure D`, exact
functors `F,G,H : C ⥤ D`, and an actual structural cofibration sequence
`hs : IsCofibrationSequence V W a b`, the theorem

```lean
Quillen.Waldhausen.Additivity.KMap_additivity V W a b hs n :
  Waldhausen.KMap hs.exactG n =
    Waldhausen.KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n
```

holds for every `n : ℕ`. The right side is the map of the actual pointwise sum
functor `H ⨿ F`. Both sides are the unchanged public canonical chosen-zero
`Waldhausen.KMap`, not replacement group maps.

The contract permits arbitrary independent universe levels `u,v`, with
`C,D : Type u` and `[Category.{v} C] [Category.{v} D]`. It retains a chosen
`[HasBinaryCoproducts D]` instance, whose existence follows from `W` through
`hasBinaryCoproducts W`. No preadditive or exact-category hypothesis is used.

## Proof and basepoints

1. The actual pushout deformation functor is conjugated by a genuine natural
   isomorphism so its value at `Arrow.mk (𝟙 V.zero)` is exactly `W.zero`.
   This internal normalization allows independent source/target universes.
2. Every interval comparison on a constant chosen-zero grid is exactly that
   identity arrow. Consequently the normalized mixed deformation has constant
   chosen-zero values for every mixed cut, including all intermediate cuts.
3. The common pair-sum endpoint is normalized at `(V.zero,V.zero)`; both the
   original and split cofibration sequences use precisely this same endpoint.
4. The genuine endpoint natural isomorphisms are conjugated by these actual
   normalization isomorphisms. Their independent reindexing coherence is
   proved componentwise. The weak nerve-cylinder theorem then produces
   actual homotopies with constant chosen-zero tracks.
5. The minimum-cut mixed-cylinder homotopy is independently proved fixed at
   the exact subdivided zero vertex. `subdividedBasedAdditivityHomotopy`
   assembles the three homotopies relative to `subdivisionBasepoint V`.
6. The original based forward ordinary-subdivision map is surjective on each
   homotopy group because its underlying realization map is a proved
   homotopy equivalence. Only this forward surjectivity is used to cancel
   subdivision. No inverse space map or inverse homotopy is assumed based.
7. `diagonalKMap_naturality` is the exact square for the original diagonal
   realization homeomorphism and the original public `KMap`. Its actual
   forward group equivalence transports the equality to the stated endpoint.

The endpoint functor normalization agrees exactly with the existing
`Quillen.rebaseFunctor` used by `Waldhausen.KMap`.

## Evidence

All fifteen new implementation sources are frozen in
`logs/additivity-based-sources.sha256` (manifest SHA-256
`0cee6e9bde96dff2ea38b9537a5bc1cd4dbbaf2d5b279d318a663782b5f36dea`).
The final three author-owned sources have their own manifest
`logs/additivity-based-final-sources.sha256` (SHA-256
`a7aabf3553d868a5f1cd7cad241ef7088ba4abac0e50f38331ebc98c63ead7ef`).

- Focused implementation checks passed warning-free and produced importable outputs.
- `audits/AdditivityBasedAudit.lean` recursively checks every defining-module
  declaration in all fifteen sources and asserts the fixed count **148**.
- Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms.
- Arbitrary-universe consumers verify the exact public K-map equality,
  relative homotopy, and canonical rebased-map formula.
- An actual bounded-acyclic truncation consumer instantiates the theorem
  using `boundedAcyclicTruncation_isCofibrationSequence`; no target-equivalence
  hypothesis is supplied.
- The final audit passed warning-free in `logs/additivity-based-audit.log`;
  `logs/additivity-based-hash-recheck.log` confirms all source hashes afterward.
- The earlier completed audit, which had only a consumer `letI` style warning,
  is preserved as `audits/AdditivityBasedAuditInitial.lean` and
  `logs/additivity-based-audit-initial.log`. It was not edited while running.

Independent reviews cover the normalization core, endpoint families,
subdivision basepoint bridge, and final group assembly separately. The
coordinator maintains their acceptance records.

## Boundary

The earlier unbased additivity twenty-source boundary and the original
Quillen Q/S comparison forty-two-source boundary remain unchanged. This
result identifies the K-map of a cofibration sequence's middle functor with
that of its actual split sum. It does not by itself identify the sum map with
pointwise multiplication of homomorphisms, assert a change-of-weak-equivalences
fibration, or finish the Gillet–Waldhausen equivalence.
