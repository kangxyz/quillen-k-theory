# Independent acceptance: genuine Quillen Q / Waldhausen S comparison

Accepted 2026-10-09 04:58 UTC. This endpoint is newer than the delivered
04:11 archive. Exact-source archive validation remains a separate release gate.

## Endpoint and exact forward maps

For every actual Quillen exact structure E on a preadditive category with
finite biproducts, in arbitrary object and hom universes:

- `realizationComparisonHomotopyEquiv E` is an actual homotopy equivalence
  from the edgewise subdivision of the existing exact S-model to the
  already-defined Q-space. Its forward map is definitionally
  `realizationComparison E`.
- `comparisonKEquiv E n : (ofExactCategory E).K n ≃* E.K n` holds for every
  nonnegative degree. Its underlying homomorphism is definitionally the
  previously constructed `comparisonK E n`.
- Both maps from the subdivided source preserve their actual chosen zero
  vertices. The K-equivalence is formed from these two based group maps.
  It does not assume the chosen inverse of a space equivalence is pointed.
- The raw simplicial comparison is strictly natural under genuine exact
  functors. Normalized based K-map naturality is a separate coherence result.

No abelian-category, finiteness, split-exactness, chain-reconstruction or
comparison-equivalence hypothesis is added to the original exact structure.
The input finite biproducts and genuine exact axioms are the existing library
contract, not fields containing any of these conclusions.

## Semantic proof review

1. An S-row supplies actual conflations through its zero-corner pushouts.
   Overlapping quotient rectangles are pullbacks, so their admissible
   epi-left/mono-right spans compose to the original Q-morphisms.
2. Original isomorphisms correspond bijectively to Q-isomorphisms. An
   invertible Q-span has two invertible legs by admissibility and explicit
   splitting; no unproved balancedness of an exact category is used.
3. The central intervals in the reversed-first-half edgewise ordinal define
   the actual row-to-Q-chain functor. Full faithfulness reconstructs upper
   subobjects from span apices and lower ones from actual kernels, then all
   quotient objects/maps from cokernel universal properties.
4. Essential surjectivity is an induction on finite Q-chain length. The base
   row is zero-to-object. For the next arrow, an actual admissible span
   representative pulls back the prior admissible flag. Prefixing zero and
   adjoining the target gives an actual new admissible flag; its cokernel
   completion gives the new exact row.
5. Pullback preserves each old interval quotient by a proved kernel and
   cokernel calculation. Explicit middle, apex and terminal isomorphisms
   identify the last Q-arrow with exactly the supplied span. Ordinal casts
   and the precise terminal component of the old chain are retained in the
   final induction. Reconstruction is a theorem, not an input structure.
6. The resulting row functors are actual categorical equivalences. The
   reviewed generic bisimplicial theorem realizes them on the diagonal.
   Partial edgewise subdivision and the classification-diagonal deformation
   complete the comparison. Their composite is proved to be precisely the
   original simplicial comparison map.
7. The based homotopy-group argument uses the already-proved canonical
   positive homotopy-group map of a homotopy equivalence. It applies also
   in degree K0 = pi1, without presupposing K0 commutativity.

## Independent checking

- The 26 stable row/map/flag modules received a separate source rebuild,
  semantic review and complete 465-declaration recursive audit.
- The remaining pullback/extension, reconstruction-index and actual
  reconstructed-span sources were read independently. Their authors supplied
  frozen source checks and recursive origin audits. The final induction and
  equivalence assembly received an additional independent warning-free
  source rebuild and 31-declaration endpoint audit.
- A separate final audit covered all 43 defining modules: the 41 Q/S files,
  revised `SpecialFractions`, and `QConstruction.Core`. All 766 declarations,
  including private/generated helpers, recursively use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Independent external consumers check arbitrary object/hom universes,
  actual row full/faithful/essential-surjective instances, existence of the
  exact row reconstruction, the exact realized forward map, its zero point,
  the original canonical K-map, bijectivity, and the based zigzag identity.
- All 43 source hashes match before and after the full independent audit.
  The earlier 26-source independent manifest also remains unchanged.

Evidence:

- `logs/q-s-full-independent-sources.sha256`
- `logs/q-s-full-independent-hashes.log`
- `audits/QuillenSComparisonIndependentAudit.lean`
- `logs/q-s-full-independent-audit.log`
- `docs/REVIEW_20261009_QS_STABLE_ROWS.md`
- `docs/REVIEW_20261009_QS_FUNCTORIALITY.md`
- The separate final endpoint review and reconstruction support reports.

## Remaining scope

Q/S identifies exact-category S-theory (weak equivalences are isomorphisms)
with the genuine Q-theory. It does not change chain isomorphisms into
quasi-isomorphisms for free. Gillet–Waldhausen, strict/local perfect
comparison, perfect localization, spectra and nonconnective tails remain
separate theorem work. The accepted split/ambient comparison changes only
the cofibration convention on the same actual perfect-complex objects.
