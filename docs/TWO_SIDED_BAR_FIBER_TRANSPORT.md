# Original-map bar transport on homotopy fibers

The two sources `Realization/TwoSidedBarFiber.lean` and
`Realization/TwoSidedBarFiberEquivalence.lean`, beneath `Quillen/Topology`,
are frozen in `logs/two-sided-bar-fiber-sources.sha256`.

For every actual bisimplicial transformation H→J, the bar augmentations give
strict commuting squares. Their original homotopy-fiber maps are
`dropFiberMap` and `evaluationFiberMap`. The source coordinate is the actual
realized augmentation; the entire original path is postcomposed with the
actual base augmentation. All four coordinate formulas are literal rfl
lemmas. The original simplicial vertex and its realized evaluation point
are retained explicitly.

Both original fiber maps satisfy the complete empty-aware weak property,
by the genuine augmentation homotopy equivalences and the checked generic
strict-square weak transport theorem. The APIs are
`dropFiberMap_isWeakHomotopyEquivalence`,
`evaluationFiberMap_isWeakHomotopyEquivalence`, and their `_bijective`
consequences for every finite degree, including zero. No Whitehead upgrade
and no based inverse choice are used.

Both sources compile warning-free. The own recursive origin scan passed all
18 declarations and thirteen exact source/path/map/vertex/component and
arbitrary-universe consumers. The count-frozen audit is
`audits/TwoSidedBarFiberAudit.lean`, with final log
`logs/two-sided-bar-fiber-fixed18.log`. This source boundary is separate
from the accepted seven-module augmentation boundary. Its generic
WeakSquareTransport dependency was kernel-checked and awaiting independent
acceptance when this report was written.

This transfers any subsequently proved replacement-fiber result to the
unchanged diagonal fibers. The missing finite weak-cartesian gluing theorem
and the final original Waldhausen canonical-fiber-map identification remain
separate obligations; neither is assumed as a theorem here.
