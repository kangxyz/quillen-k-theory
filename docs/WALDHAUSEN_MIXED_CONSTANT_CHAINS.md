# The original constant fine-chain comparison

`MixedNerves/ConstantChains.lean` uses the previously constructed actual fine
chain objects and coarse horizontal maps. The original constant diagram
functor sends a coarse weak arrow to the literal constant transformation.
Evaluation at the original vertex0 is a strict left inverse. The other
composite has an actual coarse natural transformation to identity, with
components precisely the original fine chain arrows F₀→Fᵢ, viewed as coarse
weak through the given nested-class inclusion.

These actual maps give a classifying-space homotopy equivalence at every
fine degree. Its forward map is literally the original constant inclusion;
its inverse is the actual first-vertex evaluation. Only the forward functor
is asserted to commute with all ordinal restrictions. No ordinal-natural
first-vertex inverse is assumed.

`ConstantDiagonal.lean` applies the accepted arbitrary-bisimplicial
rowwise-diagonal equivalence theorem to that original natural forward map.
The prescribed diagonal forward map is the original constant-chain map,
preceded only by the canonical inverse constant-diagonal identification.
The actual diagonal homotopy equivalence retains that precise map.

The categorical construction has independent object/hom universes. The
realization endpoint uses object universe max(u,v) and hom universe v, to
match the actual classifying-space comparison API without hiding a universe
condition. It requires no cylinder, saturation, extension, projectivity,
acyclicity, or global boundedness hypothesis beyond the original nested weak
classes. The separate mixed transpose, weak-cofibration comparison and
relative-inner-S interchange remain separate inputs to eventual fibration.

Both defining sources compile warning-free. The all41-origin recursive audit
(33+8) and17 consumers passed with only the standard three axioms. The fixed41
guard was independently confirmed. Source hashes were rechecked.
The driver is `audits/MixedConstantChainsAudit.lean`.
The frozen manifest is `logs/mixed-constant-chains-sources.sha256`. Independent
review accepted both fresh sources, fixed41 origins and19 consumers warning-
free, including literal diagonal simplex objects/arrows and full dependency,
artifact and toolchain rehash. The production sources remained unchanged.
It tests original objects and maps, the literal natural-transformation arrows,
strict ordinal restriction, degree0, the original zero object, prescribed
realization maps, independent universes and the actual scheme categorical use.
