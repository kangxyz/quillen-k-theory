# Independent review: ordinary twofold subdivision

Accepted 2026-10-09 05:28 UTC. Scope: the four `OrdinalSubdivision*.lean`
modules below `Quillen/Topology/Realization/`.

This is the actual ordinary ordinal functor [n] ↦ [n] ⋆ [n], with neither
copy reversed. Both inclusions are natural; the prescribed forward map is
restriction to the first copy. It is distinct from the reversed-half edgewise
subdivision used in the Q/S comparison.

The representable contraction is explicit in every simplicial degree. The
first homotopy lowers first-copy values to zero while retaining the second
copy. The second lowers the second-copy values. Monotonicity across the join
and naturality for every ordinal map, not merely endpoint-preserving ones,
are proved. Their realized concatenation gives a genuine contraction.

The already independently reviewed cellular realization criterion then applies:
ordinary precomposition preserves colimits and monomorphisms, and the actual
first-copy endpoint is a homotopy equivalence on every representable. Thus it
is a genuine realization homotopy equivalence for arbitrary simplicial sets,
including infinite-dimensional ones, with exactly that forward map. Naturality
and the original chosen-vertex formula are proved. Partial inner/outer
bisimplicial subdivision follows from actual adjacent composites and homotopy
two-out-of-six, retaining the exact diagonal endpoint maps.

All four sources were read fully and independently rebuilt, in dependency
order, into a fresh artifact overlay excluding their live artifacts. Checks
were warning/error-free. Before/after source hashes matched. The fixed89-origin
recursive audit passed, including private/generated declarations, with only
the three standard Lean logical foundations. Arbitrary-universe consumers
checked the actual indexing functor, forward endpoints, based vertices,
naturality and partial-diagonal maps.

Evidence: `audits/OrdinalSubdivisionIndependentAudit.lean`,
`logs/ordinal-independent-{check,audit,hashes}.log`, and
`logs/ordinal-independent-sources.sha256`, manifest SHA-256
`e6ff9e81f3ab0eeb39a4357d83d33283ebe62cbc155c7a94d4b0aabc8a83291c`.

The variable-suffix mixed cylinder and Waldhausen additivity are separate
constructions. These sources are outside the frozen 05:00 checkpoint.
