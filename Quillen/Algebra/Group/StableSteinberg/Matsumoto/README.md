# Actual finite Matsumoto constructions

`Torus`, `Weyl`, `LiftedWeyl` and `Normalizer` construct the determinant-one torus,
its explicit Milnor-valued cocycle, the concrete signed Weyl action and lifted
normalizer. `MatrixBasics` and `NormalizerMatrix` compare these actual objects
with literal finite matrices, retaining the actual rank and field hypotheses.
`TorusTransporter` and `WeylTransporter` prove transport in that normalizer; the
Weyl endpoint takes the displayed matrix projection and the positive transport
of the specified adjacent ordered pair.

`BruhatActions`, `BruhatCoherence`, `BruhatLeftGroup` and `BruhatExtension` provide
the finite Bruhat permutations and their genuine central extension of the
actual determinant-one matrices. These statements range over every field and
coroot rank; indexed simple-root statements take actual `Fin n` indices. The
coefficient is the existing ordered Milnor group, with the stated injectivity,
centrality, projection and marking equations.

`RootSections` is a conditional construction over every field from a central
kernel projection covering determinant-one matrices, a specified torus lift,
one additive base-root section for a distinct ordered pair, and that base
section's exact diagonal covariance. It constructs the whole family and its
simultaneous common-diagonal covariance. Its optional relation endpoint retains
`CharZero F` and the bound `5 <= n + 1`; those hypotheses are not premises of the
all-field section construction.

`FiniteRootLifting` retains the accepted conditional original-root-law
interface. `DetectorTransfer` retains the eventual-product and conditional
original stable detector transfer interfaces, including all finite detector,
marking and commutator hypotheses. The existing `RootCoordinate`,
`EventualProduct`, `FiniteDetectorTransfer`, `CommutatorDetectorTransfer`,
`FiniteRootLifting` and `RootSectionProducer` public namespaces remain unchanged.

`Injectivity.lean` constructs the actual finite roots, literal original-word
marking, finite detectors and coefficient readout, then proves
`Quillen.StableSteinberg.milnorToKernel_injective_charZero` for every field of
characteristic zero. Its original-map statement has no residual finite-model
premise. Positive characteristic and separate Quillen product-marking claims
are outside this provider. Nontrivial Weyl transport, rational root sections
and the original five-dimensional root-law client live in `QuillenTest`.
