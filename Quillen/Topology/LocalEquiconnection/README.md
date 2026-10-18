# Local equiconnection

A local equiconnection provides an open permitted-pair domain and a jointly
continuous connector with exact endpoints that fixes the whole diagonal.

## Source modules

- [LocalEquiconnection](../LocalEquiconnection.lean) defines the original-space interface.
- [Loops](Loops.lean) constructs the pointwise connector on the unchanged compact-open based path space.
- [LoopConvexCover](LoopConvexCover.lean) constructs open connector-convex loop neighborhoods from an open connector-convex cover, using a finite compact shrinking of interval carriers.
- [OpenComponents](OpenComponents.lean) provides the component geometry.

The [path-space guide](../PathSpace/README.md) records the compact-open
construction and clients. The [metric-order guide](../MetricOrderComplex/README.md)
records the positive-common-mass domain and its geometric specialization.
