# The actual joint-endpoint source functor

`Quillen/Waldhausen/Cylinder/JointSource.lean` constructs the source part needed
for a genuine joint-cylinder arrow functor. It uses the existing full subcategory
of actual cochain complexes and leaves the chosen object and maps unchanged.

## Exact formulas

For an abelian category with independent object/hom universes, and an
extension-closed complex object property `P`:

- `(subcategoryJointSourceFunctor P).obj f = subcategoryJointSource P f` by `rfl`;
- its underlying object is `f.left.obj ⊞ f.right.obj` by `rfl`;
- `((subcategoryJointSourceFunctor P).map α).hom =
  biprod.map α.left.hom α.right.hom` by `rfl`.

The object membership comes from ordinary inherited exact extension closure.
These formulas, the endpoint inclusion natural transformations, and their
actual binary-coproduct universal property need no cone, shift, kernel, or
acyclicity assumptions, and no zero/repleteness assumptions on `P`.

The coproduct universal property is proved explicitly inside the full
subcategory using the ambient `biprod.desc`, its two inclusion equations, and
`biprod.hom_ext'`. Under `P.IsClosedUnderFiniteProducts`, the resulting natural
isomorphism identifies the existing `Additivity.sumFunctor` of the two actual
arrow evaluations with the literal ambient-biproduct source functor.

## Structural exactness

`subcategoryJointSourceFunctor_isExact P W`, for **any** genuine
`W : Structure P.FullSubcategory`, proves exactness from the entire arrow
category with its actual pointwise Waldhausen structure into `W`.

The proof uses the previously proved structural exactness of both original
arrow evaluations, actual sum-functor exactness, and natural-isomorphism
transport. It does not require a source-exactness assumption. This simultaneously
proves preservation of genuine zero objects, the original cofibrations and weak
maps, and actual pushouts along pointwise cofibrations.

`subcategoryJointSourceFunctor_map_isPushout P W hf hL hR` accepts the actual two
component pushout squares and the actual pair of component cofibrations, and
returns the displayed pushout on the original joint-source maps. No unrelated
pushout object or isomorphic replacement is substituted in the conclusion.

With the standard additional `P.ContainsZero` and repleteness inputs that
construct the inherited structures, the module exposes:

- `subcategoryJointSourceFunctor_isoExact`: inherited admissible cofibrations
  and actual isomorphism weak equivalences;
- `subcategoryJointSourceFunctor_quasiExact`: inherited admissible cofibrations
  and actual quasi-isomorphisms.

The generic theorem is stronger and needs neither of those additional property
instances once the actual Waldhausen structure `W` is supplied.

## Verification and scope

The direct production check passed warning-free under `lean -j1` and slot1;
`logs/joint-source-20261009/check2.log` records acquisition and success. Source
hashes are fixed by `logs/joint-source-20261009/sources.sha256`. The authored
origin audit and exact consumer tests are in `audits/JointSourceAudit.lean`.
The final fixed **32-origin** recursive audit passed, permitting only `propext`,
`Classical.choice`, and `Quot.sound`; all 13 actual consumers passed warning-free.
The final source hash was rechecked unchanged. The initial audit detected only
a parenthesization error in one consumer, repaired before the fixed-count run;
no implementation source change was needed.
Consumers retain arbitrary independent object/hom universes, the exact object
and map formulas, the actual coproduct universal property, structural exactness,
zero/cofibration/weak preservation, displayed pushout preservation, and both
inherited specializations. No cone/shift/kernel closure is supplied.

This is the actual source functor and its structural exactness. The whole
joint-cylinder arrow functor, its middle exactness, relative Reedy condition,
and any fibration conclusion are separate modules owned by the parent author.
Independent review of this new source is assigned to that parent.

Evidence: `audit-final.log`, `rehash.log`, and `artifacts.sha256` in the same
log directory. Source SHA-256:
`958d9a5ac3dea3763f4e12f8480f0241b55cf867b7339a4c43125cab9f5a8659`.
Source-manifest SHA-256:
`15730c8311cc4401e9238b8d6767c735c7909535a824ecff6e6fbaa754766642`.
