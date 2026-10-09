# Independent review: genuine relative cutoff, quotient and product section

All nine frozen sources in `logs/relative-cut-section-independent-sources.sha256`
were read completely. No semantic defect was found. **Accepted for this scope.**

The cutoff is the actual ordinal restriction retaining the added vertex and
collapsing tail vertices to the first tail vertex. Its inclusion uses the
original interval maps. Cofibrancy is verified on genuine Reedy relative
squares and cubes, including every degenerate and zero-source case; it is
not inferred from pointwise cofibrancy alone. The cutoff arrow functor is
proved exact using the original row/arrow interchange and faithful reflection.

The first-object fiber reconstruction is identified with this cutoff by the
actual zero/identity/zero one-row natural isomorphism. Its tail quotient is
the literal original acyclic tail with the first vertex duplicated. Actual
interval quotient pushouts prove the cutoff/identity/tail structural cofiber
sequence. The pair-to-row section is the original tail-section/fiber coproduct;
its exactness is genuine and the inverse first/tail natural isomorphism uses
the original coproduct inclusions. Arbitrarily chosen binary coproducts are
permitted, and their existence is separately derived from the actual
Waldhausen structure in the consumer check.

These categorical statements permit independent object/hom universes. They
assume only the displayed nested weak-equivalence structure, with no
saturation, cylinder, extension axiom or fiber-equivalence hypothesis.
They supply the ingredients for degreewise additivity; no diagonal fiber or
quasi-isomorphism comparison follows merely from this boundary.

## Independent Lean verification

An isolated first-`LEAN_PATH` overlay excludes all nine target artifact stems.
Each source was freshly compiled in dependency order under slot2, with
`--deps` logs showing the actual fresh reviewed prerequisites. The fixed77
initial-cut audit and fixed26 quotient/section audit pass recursively with
only `propext`, `Classical.choice`, and `Quot.sound`. All36 consumers pass,
including exact interval maps, genuine pushouts, original coproduct maps,
both natural-isomorphism identities, independently chosen universes, derived
coproduct existence and outer degree zero. Logs are warning-free, and all
nine hashes match before and after the run.

Replay: `logs/verify-relative-cut-section-independent.sh`.
Audits: `audits/RelativeCutSectionIndependentAudit.lean` and
`audits/RelativeRowsTailSectionAudit.lean`.
Evidence: the source manifest and `logs/relative-cut-section-independent-*`
build, audit, prehash and posthash records.
