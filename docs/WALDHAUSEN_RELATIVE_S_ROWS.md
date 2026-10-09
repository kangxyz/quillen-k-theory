# Actual relative S-row diagram and strict local split maps

Three sources are frozen in `logs/relative-rows-simplicial-sources.sha256`:
`Fibration/RelativeRows/{TailSection,Simplicial,FirstTailSSet}`. All source
checks passed without warnings. Both the initial and fixed55 own audits passed all55 origins
and22 actual-map consumers without warnings. Final evidence is
`logs/relative-rows-simplicial-audit-final.log`.

`tailSection N n` duplicates the initial vertex of an actual acyclic quotient
row. It is genuinely exact, retains the chosen relative zero, has an actual
zero first object, and its composite with the original tail functor is
strictly the identity. This structural section allows independent ambient
object/hom universes. It is degreewise; arbitrary outer naturality is not
claimed for this section.

With the explicit common universe `C : Type u`, `Category.{u} C`,
`relativeSRows N` is the actual outer simplicial diagram of the inner
S-constructions of the genuine relative-row Waldhausen categories.
`ordinarySRows (acyclicStructure N)` is the corresponding genuine tail-row
diagram. `tailSRows` and `fiberSRows` use the original exact functor S-maps,
with strict outer naturality and strict composite equal to the genuine
constant-zero map. Literal postcomposition formulas for the underlying
original grids are exposed.

`firstTailSSet N n` is the original degreewise first/tail S-map followed by
the accepted actual product-category S-isomorphism. Its second projection
is exactly the original tail S-map; its first projection is the original
first-object evaluation S-map. The original split inclusion composes with
it to exactly `ProductRealization.vertexSection` at the actual zero vertex.
Every inner source and tail S-realization is path-connected by the accepted
genuine Waldhausen S-connectedness theorem.

No realization-product homeomorphism, relative-additivity equivalence or
homotopy-fiber theorem is an input or conclusion here. The actual first/tail
realization homotopy equivalence remains the next relative-additivity proof;
the global connected-row diagonal fiber theorem remains separate.
