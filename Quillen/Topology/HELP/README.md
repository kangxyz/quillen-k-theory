# Finite homotopy extension and lifting

## Public imports

Module paths are relative to `Quillen.` unless fully qualified.

| Import | Interface |
| --- | --- |
| [`Quillen.Topology.HELP.Basic`](Basic.lean) | Homotopy extension and continuous cylinder coordinates |

## Finite HELP and cone-fiber excision

`IsHomotopyConnectedMap` uses nonempty actual fibers and vanishing homotopy
sets below the finite bound at every fiber point.
[`cube_fullHELP`](Connectivity.lean) fills cubes
through that bound while retaining the entire prescribed boundary homotopy.
The independent client [`Consumer.FiniteHELP`](../../../examples/downstream/Consumer/FiniteHELP.lean)
uses complete weak equivalence, full finite cube HELP, degree zero, and the
empty-source obstruction. Finite cube HELP supplies no arbitrary compact HELP.

For `p`- and `q`-connected attaching maps, the original double-cylinder gap is
`r`-connected when `r + 1 ≤ p + q`. The
[`gap_isHomotopyConnectedMap`](../DoubleMappingCylinder/GapConnectivity.lean)
statement includes fiber nonemptiness and every fiber point, without separation,
CW, attaching-cofibration, or connectivity-growth premises.

For `f : E ⟶ F`, the canonical comparison is
`mappingConeFiberComparison f : E ⟶ homotopyFiber (mappingConeInclusion f)`.
Its fiber path is the original cone cylinder. Cone-fiber excision means stable
equivalence of this specified map.
[`ConeLinearExcision`](../Prespectrum/ConeLinearExcision.lean)
requires chosen-point HEP and all-point vanishing in degrees `k < n+2` at
levels `n+c+2`, for a fixed `c : ℕ`. The original S-level growth and point HEP
discharge this comparison for original S-model maps in
[`Iterated.ConeFiberExcision`](../../Waldhausen/SConstruction/Iterated/ConeFiberExcision.lean).

The resulting signed cone sequences retain the original inclusion and boundary.
Whole cone/pushout homotopy squares need their supplied tracks and explicit
row-excision premises; equality of stable maps alone does not supply those
tracks. [Finite Bass stages](../../KTheory/Bass/README.md) discharge their own excision hypotheses.
General stable cone excision for arbitrary prespectra remains separate, as does
any levelwise weak-equivalence criterion inferred solely from a trivial cone.
