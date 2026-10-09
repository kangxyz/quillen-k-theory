# General noetherian open G-localization

## Geometric extension

The completed geometric extension proof is in
`Quillen/Scheme/Coherent/Localization/ObjectExtension.lean`.
Its public conclusions have only actual geometric assumptions:
`X` is a noetherian scheme, `U` is locally noetherian, and
`j : U ⟶ X` is an open immersion. The local noetherianity of `U`
follows from that of `X`; it is retained as the category's typeclass argument.

The proof uses the actual ambient quasicoherent sheaf throughout:

1. Extend an open coherent subobject to its actual quasicoherent preimage kernel.
2. On a noetherian affine chart, use finite approximation to produce a coherent
   subsheaf with unchanged restriction on the chart's overlap.
3. Glue this subsheaf with the existing coherent restriction using a paired
   obstruction kernel. The glued object is globally quasicoherent.
4. Enlarge the coherent locus by that affine chart. The restricted map on the
   previous coherent locus is an isomorphism.
5. Apply `compact_open_induction_on` to the top open. This is induction over an
   actual finite affine cover, and it preserves the original restriction.
6. For object extension, take the ambient sheaf to be the actual direct image
   `j_* A` and use the restriction-pushforward counit isomorphism.

The geometric declarations are:

- `exists_coherent_subsheaf_restrict_isIso_noetherian`
- `coherent_subobject_extension_noetherian`
- `coherent_extension`
- `coherentRestriction_essSurj`

The compact-open induction helper takes an enlargement step as an argument;
`ObjectExtension.lean` supplies the proved `coherent_affine_enlargement`.
No object-extension or quotient-equivalence assumption remains in these
geometric conclusions.

## Localization endpoint

Import `Quillen.Scheme.Coherent.GlobalLocalization` for the actual supported
Serre quotient equivalence, genuine coherent-restriction localization, and
connective long exact sequence on the public `G` and `SupportedG` groups.
The ambient-to-open map is the existing actual `restrictionGMap`, defined
by the exact restriction functor's canonical `smallKMap`.

Main categorical declarations:

- `coherentSupportQuotientEquivalence`
- `coherentRestriction_isLocalization`
- `coherentRestriction_isLocalization_kernel`

Main group-level declarations:

- `globalInclusionGMap`
- `globalConnectingHom`
- `global_localization_longExact`
- `global_localization_canonical_longExact`
- `global_localization_GZero_tail`
- `global_GZero_surjective`

The support comparison uses the actual category of coherent sheaves whose
ordinary stalk support is contained in the complement of the open. All
small-model comparisons are made in the public global universe `u + 1`.
The support comparison commutes definitionally with actual inclusion at the
exact-functor level. `globalInclusionGMap_eq_smallKMap` identifies the support
arrow with the actual inclusion's canonical `smallKMap`; the canonical long
exact theorem writes this map directly.

This result is for arbitrary open immersions into noetherian schemes; it
does not infer a nonaffine theorem from principal-open localization.

## Validation

- `lake build Quillen.Scheme.Coherent.Localization.ObjectExtension`: passed.
- `lake build Quillen.Scheme.Coherent.GlobalLocalization`: passed.
- `audits/GlobalObjectExtensionAudit.lean`: nine geometric declarations and
  independent essential-surjectivity instance inference passed.
- `logs/GlobalObjectExtension-audit.log`: only `propext`, `Classical.choice`,
  and `Quot.sound` appear.
- `audits/GeneralGLocalizationAudit.lean`: categorical localization, actual
  support identification, all-degree exactness, and the G-zero tail are audited
  with only the standard three axioms. Its printed theorem signatures expose
  no extension, essential-surjectivity, or quotient-equivalence hypotheses.
- `scripts/check_placeholders.py`: passed, no proof placeholders or custom assumptions.
- `scripts/check_library_layout.py`: passed, all 364 migrated implementation
  bodies remain preserved; the later canonical-only cleanup removes their old aliases.

These new modules are standalone imports. No root export or publication is
implied by their addition.
