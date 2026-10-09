# The original total-tail fiber comparison and its all-weak square

The new `RelativeRows/TotalFiber.lean` names the actual diagonal tail map,
the actual double-S zero vertex and its realization point, and the literal
constant-path comparison from the original fine delooping into that tail
map's actual homotopy fiber. The stored source coordinate is the original
totalFiberInclusion; the complete path is constant at the original double-S
zero. The original fine zero maps to the original constant-path relative
zero point.

The tail-after-inclusion identity is proved using the accepted strict
fiberSRows_tailSRows identity, whose proof uses fiber_tail from the original
oneChain and ordinal construction. Totalization retains that equality; the
constant simplicial map realizes to the literal constant continuous map.
No chosen nullhomotopy or eventual weak comparison is inserted as data.

`AllWeak/TotalFiberSquare.lean` realizes the original ordinaryRows diagonal
isomorphism as an actual homeomorphism, preserving the actual double-S zero.
The original relative inclusion then gives the exact realized tail square.
Its induced map of actual homotopy fibers retains the original source map
and postcomposes the entire stored path by the actual ordinary inclusion.
The square with both original total-tail comparisons and the original
acyclic inclusion commutes strictly, including every path point.

These modules use the explicit common object/hom universe required by the
original total S-constructions. No saturation, extension, cylinder or kernel
closure is required for these actual maps and identities. In particular,
neither totalTailFiberComparison is asserted to be weak: those are precisely
the two still-missing global relative-tail comparisons needed by the later
fibration assembly. The bounded-term GW application also retains its
separate genuine kernel/cycle-closure requirements.

Both source checks passed warning-free. The single-pass audit measured
all31 origins, split [15,16], and all15 consumers passed with only the
standard three axioms recursively. `audits/RelativeTotalFiberAudit.lean`
now has its fixed31 guard. Independent fresh3/fixed[10,15,16]=41
review, covering the transport and this pair, passed all33 consumers with
unchanged full dependency hashes on 2026-10-09 at14:07:08 UTC.
The unchanged pair is frozen together with the already checked transport
source in `logs/common-base-total-fiber-sources.sha256`.
