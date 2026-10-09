# Independent review: the original constant fine-chain diagonal inclusion

Accepted 2026-10-09 11:33:37 UTC. Both targets rebuilt freshly in an
excluded-target overlay. Fixed origin counts 33+8 and all 19 consumers passed
warning-free, with unchanged source, 3,688 dependency-source, 17,189 artifact,
and toolchain hashes. Recursive axioms are the standard Lean logical three.

The underlying category of fine chains retains all natural transformations;
only its horizontal weak category restricts maps to pointwise coarse weak
ones. Constant diagrams preserve the original objects and coarse arrows.
Evaluation at zero is a strict left inverse. The original arrows from zero
to every finite-chain vertex are fine weak, hence coarse weak by the original
nested-class inclusion. They define the displayed genuine natural
transformation from constant-after-evaluation to identity. Its realization
is an actual continuous homotopy, so the prescribed rowwise constant map
has an actual homotopy inverse.

The forward constant inclusion commutes strictly with every fine-index
ordinal restriction. No such naturality is asserted for evaluation at zero.
The accepted rowwise-to-diagonal realization theorem applies to those actual
forward maps and their rowwise homotopy equivalences. Composing only with the
canonical constant-diagonal isomorphism gives the stated homotopy equivalence
whose forward is literally the original constantHorizontalDiagonalMap.

The categorical construction has independent object and morphism universes.
The realization construction states object universe max(u,v) with hom universe
v, so the original and finite-chain category realizations share their actual
universe; this is not silently generalized to arbitrary mismatched spaces.
No coarse saturation, extension axiom, or cylinder is required.

The original 17 consumers were retained. Two further tests verify every
actual diagonal simplex object and arrow: the object is the corresponding
original vertex and the map is the original coarse arrow, unchanged in the
constant fine direction. Degree-zero and arbitrary-scheme structural
consumers also passed. A prescribed reverse diagonal evaluation, the original
S-grid bridge, and the full fibration/Gillet-Waldhausen remain separate.
This endpoint is outside the delivered 10:55 version7 archive.

Audit: `audits/MixedConstantChainsIndependentAudit.lean`.
Preparation and replay: `logs/prepare-mixed-constant-chains-independent.py`
and `logs/verify-mixed-constant-chains-independent.sh`.
Evidence: `logs/mixed-constant-chains-independent-20261009/artifacts.sha256`.
