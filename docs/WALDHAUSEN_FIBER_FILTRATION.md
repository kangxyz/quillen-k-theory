# Original split-fiber initial filtration

The new `RelativeRows/FiberFiltration.lean` retains the existing fiber and
initialFiltrationFunctor exactly. Each initial interval [0,i+1] collapses
to the one-row interval [0,1], hence its object is the original X, every
structural arrow is the original identity, and a morphism's component is
literally that original morphism. The resulting functor equality identifies
the original fiber followed by initial filtration with the actual constant-
chain functor.

The statement has independent object and hom universes and requires only
the original nested weak-equivalence structures. It assumes no extension,
saturation, cylinder or realization-equivalence hypothesis. It supplies a
small categorical input for the separately owned canonical total fiber /
change-of-weak-class triangle; it does not claim that triangle by itself.

The source and fixed4-origin/eight-consumer audit passed warning-free, with
only the standard three axioms. Consumers retain original components,
independent universes, degree0, actual zero, ordinal restriction and an
arbitrary-scheme bounded-term instance. Source hashes are unchanged. The
driver is `audits/RelativeFiberFiltrationAudit.lean`; the frozen manifest is
`logs/relative-fiber-filtration-sources.sha256`. Independent review is pending.
