# Independent localization endpoint review

Reviewed 2026-10-09, 00:21 UTC, against Lean 4.34.0 and the locked mathlib revision.

## Result

No mathematical adequacy blocker was found for the stated endpoint: the
canonical weak homotopy-fiber comparison and the complete connective
localization exact sequence for a small abelian category and a Serre class.
The final theorem has no assumed Theorem B, cartesian-stage, comparison,
filtration, or quotient-equivalence input.

## Mathematical checks

- **Actual maps.** `SkeletalCartesian.Cartesian` requires an ordinary homotopy
  equivalence whose forward map is exactly the constant-path homotopy-pullback
  comparison. Product coordinates, coproduct assembly, pasting, and the finite
  pushout cube preserve that requirement.
- **Finite-domain descent.** `finiteDomain_cartesian` derives the whole-domain
  comparison from all actual simplex charts into one fixed target. Its
  induction derives boundary comparisons rather than assuming them. The
  dimension bound applies to the domain, not the coefficient; infinitely many
  cells are allowed. No local-compactness assumption is placed on an arbitrary
  finite-dimensional domain.
- **Simultaneous induction.** `restrictedSimplexChart_cartesian` factors each
  face through its genuine first-vertex transition and the previous skeleton's
  chart. Both incoming cube faces are derived. New characteristic charts come
  from actual coproduct-component inclusions; old charts propagate through the
  outgoing stage face. Nondegenerate ancestors and their coefficient
  isomorphisms cover all degeneracies. The induction starts from the empty
  skeleton and retains no caller-supplied chart or stage conclusion.
- **Point coordinates.** Augmentations `H(d) → Δ[0]` are never assumed to be
  equivalences. The boundary product comparison uses the identity on `H(d)`;
  point-valued replacements are then identified with the actual base domains.
- **Sequential passage.** Compact factorization includes the entire family of
  paths and relative homotopies. The actual replacement towers supply the
  closed-embedding and T₁ hypotheses. The conclusion is bijectivity of finite
  homotopy sets, including π₀, without claiming a global homotopy inverse.
- **Serre hypotheses and normalization.** The final
  `SerreLocalization.basedLocalizationFiberComparison_bijective` assumes only
  `C : Type u`, `Category.{u} C`, `Abelian C`, and `P.IsSerreClass`.
  Proved raw Serre transitions pass through the normalized quotient and the
  structured/opposite comparison. The comparison uses the actual normalized
  inclusion and quotient defining the K-maps, with a homotopy fixing the
  chosen zero/constant-path basepoint.
- **Maps and degrees.** Since `Kₙ = πₙ₊₁(BQ)`, `connectingHom P n` has domain
  `Kₙ₊₁(C/P)` and codomain `Kₙ(P)`. It is the actual path-space connecting
  homomorphism transported through the inverse canonical comparison.
  `comparison_comp_connectingHom` records this identification. The three
  range-equals-kernel positions hold for every `n : ℕ`; the terminal canonical
  `K₀(C) → K₀(C/P)` map is surjective. The latter uses the comparison on π₀ and
  connectedness of `BQ(P)`, not an unproved Grothendieck-group identification.

## Exact scope

The generic comma theorem `TheoremB.fiberComparison_bijective` is at
`d = F.obj c` and its identity-arrow basepoint. The replacement theorem
quantifies over every **existing** source point. Neither statement alone
handles an empty comma by inferring that its target fiber is empty. Localization
has a zero object and a path-connected source, so this caveat does not weaken
the reviewed Serre endpoint.

This review does not claim an ordinary global homotopy inverse, full naturality
for exact functors of Serre pairs, homotopical K₀ commutativity/Grothendieck
comparison, general exact-category localization, or essentially-small/universe
transport. The established exact sequence is formulated in groups.

## Independent verification

- Focused rebuild of `Quillen.CategoryTheory.TheoremB.WeakComparison` and
  `Quillen.Localization.Serre.LocalizationTheorem`: **success, 2739 jobs**. Evidence:
  `localization-independent-focused-build-20261009.log` (in the original checkpoint).
- Twenty-six focused `#print axioms` checks, spanning finite-domain descent,
  assembly/induction, both comma orientations, unconditional Serre transitions,
  canonical fiber comparison, boundary, and both final LES statements:
  **only `propext`, `Classical.choice`, and `Quot.sound`**. The same run prints
  final signatures showing the absence of extra theorem hypotheses. Evidence:
  `localization-independent-axioms-20261009.log` (in the original checkpoint).
- The complete integrated-project build and all-declaration audit are recorded
  separately in `STATUS.md`; the focused checks here do not substitute for them.

The source review included the Domains, Boundary, Coordinates, CoproductAssembly,
StageCube, Assembly, StageRestriction, CoordinateTransport, StageExtraction,
and Induction modules; WeakComparison and StructuredWeakComparison; and the
Serre based comparison, structured transport, LES adapter, Endpoint, and
unconditional LocalizationTheorem modules.
