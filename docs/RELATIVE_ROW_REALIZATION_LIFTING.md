# Lifting for original normalized row comparisons

The three sources recorded in `logs/row-realization-lifting-sources.sha256`
retain the actual relative S-row maps, their complete path coordinates, and
all ordinal-transition squares.

`RelativeRows.FiberTransport` defines the unchanged original transition on
homotopy fibers at every point of the original base row. Genuine row
connectedness supplies an individual path from its chosen zero. The independently
proved arbitrary-square basepoint transport transfers full compact HELP from
the chosen fiber to that particular fiber. There is no continuous selection
of paths or inverse maps over the base.

`MappingPath.strictComparison_fiber_compactHELP` compares the genuine strict
fibers of the normalized mapping-path comparison with the original square's
homotopy fibers. The two actual fiber homeomorphisms retain the whole paths;
full HELP cancellation therefore applies. Its companion theorem applies the
accepted fiberwise realization lifting theorem to the actual mapping-path
endpoint fibrations and their strict base change. The original maps in the
square need not themselves have HLP.

For every nested Waldhausen weak-equivalence structure N and every ordinal
transition, `rowNormalizedComparison_endpoint_realization_mono` derives
right lifting of the original normalized comparison's actual mapping-path
endpoint against every realized simplicial monomorphism. Its fiber hypotheses
are proved from N. The test realization may be infinite or noncompact, and
dimension zero is included. This is a relative-cell lifting input, not the
missing finite weak-cartesian gluing or global diagonal-fiber theorem.

All three final authored source checks and the authored 9-origin, 12-consumer
audit passed warning-free. Independent semantic review, fresh isolated rebuilds,
the fixed-nine recursive-origin audit and 15 exact consumers passed. See
[the review](REVIEW_20261009_ROW_REALIZATION_LIFTING.md). These sources are
outside the frozen 09:45 archive.
