# Original mixed weak-cofibration inclusion

New source boundary under `Fibration/MixedNerves`:
`Cylinder`, `RowCylinder`, `Realization`, and `RowRealization`.
This boundary is separate from the frozen exact transpose presentation.

## Structural construction

`chainCylinder N D hD k` applies the actual base `CylinderData` to each
original component arrow of a fine-weak chain. The full fine-chain category
retains all natural transformations. Its middle stays inside the original
fine-weak object condition because `hD` is actual fine-square preservation
of the base middle functor. This condition contains no nerve or realization
conclusion. The first endpoint, second endpoint, and projection are the
original component maps. Their actual factorization/section identities,
pointwise cofibrations, and coarse projection weakness are proved directly.
The middle commutes strictly with ordinal restrictions.

`rowChainCylinder` instantiates that data using the accepted genuine joint
cylinder on the unchanged fine quotient rows. The fine-square condition is
discharged by the original row middle's proved exactness. The concrete
`complexRowChainCylinder` uses the original identity-cone cylinder.
These structural sources retain independent object/hom universes and need
no coarse saturation themselves.

## Realization theorem

In the common object/hom universe, with coarse two-out-of-three:

1. The actual pointwise cylinder supplies GW's proved original comma
   contractions and the prescribed-forward Quillen-A theorem, yielding
   `horizontalClassifyingHomotopyEquiv` in every fine degree.
2. The accepted generic bisimplicial realization invariance applies to
   the literal natural horizontal inclusion. Chosen row inverses need
   not be ordinal-natural.
3. The checked exact transpose square transports that genuine diagonal
   equivalence back to the original fine-weak nerve of coarse-weak chains.

`chainInclusionRealizationHomotopyEquiv` has forward map definitionally
`SSet.toTop.map (TheoremA.diagonalMap (chainInclusion N))`. The actual
row and complex wrappers retain that identical map. No naturality of a
chosen inverse is assumed. Fine saturation and a fine-weak cylinder
projection are not required.

## Concrete scope and remaining assembly

For complex subcategories the input is zero/replete/extension closure,
finite-product closure, actual mapping-cone closure, and shift-by-one
closure. The bounded-terms specialization derives the latter conditions
from its accepted construction, with no kernel closure. The realized
endpoint keeps the explicit common-universe scope of the proved Quillen-A
API; the structural data is more universe-general.

This compares the two original mixed nerves. The explicit identification
with relative-inner-S rows and the original GridBridge is separate. The
constant-chain comparison, its prescribed diagonal-evaluation inverse,
and the global relative-realization homotopy-fiber theorem are separate
assembly steps. No global fibration or Gillet-Waldhausen conclusion is
claimed here.

## Verification

All four sources compile warning-free. All 58 declaration origins
(26+9+14+9) and all 25 consumers passed warning-free. The terminal fixed58 replay also passed.
Evidence manifest: `logs/mixed-nerves-realization-artifacts.sha256`. Source manifest:
`logs/mixed-nerves-realization-sources.sha256`, fingerprint
`c74012dd4eebb7669f6a9361c816dd1f0667bdf963f00f7518adc999e34570ee`. `audits/MixedNervesRealizationAudit.lean` recursively
checks all four module origins, plus actual cylinder component formulas,
cofibrations, genuine fine-object closure, strict restrictions, degree
zero, independent structural universes, common-universe realized forward
maps, and actual bounded-term complex projections.
