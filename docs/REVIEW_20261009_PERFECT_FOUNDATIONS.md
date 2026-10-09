# Independent review: Waldhausen and perfect-complex foundations

Reviewed 2026-10-09. This review covers precisely the ten `Quillen/Waldhausen/*.lean` modules and the seven `Quillen/PerfectComplexes/` leaves Strict, VectorBundleInclusion, Restriction, Local, LocalRestriction, Support, and LocalLifting. It excludes the active LocalHomotopyStep development and every subsequent comparison theorem. The frozen set comprises 17 modules and 1,533 source lines.

## Accepted semantic scope

- The Waldhausen structure has the conventional structural inputs: a genuine zero object, composable cofibrations and weak equivalences containing isomorphisms, cofibrant objects, pushouts and cobase-change stability, and the gluing axiom. No additivity, localization, or equivalence conclusion is a field.
- The S-construction is genuinely the diagonal nerve/S diagram: an n-simplex is a functor from `[n] × Ar[n]`, with zero diagonals, row cofibrations, quotient pushout squares, and pointwise weak equivalences in the nerve direction. Reindexing simultaneously handles both simplex coordinates. Weak equivalences are not replaced by arbitrary maps or just chain isomorphisms.
- Realization and the chosen zero vertex define the actual shifted homotopy groups. Exact functors induce the actual simplicial and continuous maps. A natural-isomorphism rebase gives a group map at the specified zero objects.
- Exact categories become Waldhausen categories with admissible monomorphisms and isomorphisms. For ambient abelian complexes the weak equivalences are genuine quasi-isomorphisms; gluing follows from the pushout short exact sequence and homology comparison.
- Extension-closed full subcategories inherit cofibrations whose quotients remain inside. The full inclusion preserves the actual cofibration pushouts, so quasi-isomorphism gluing descends legitimately.
- Strict perfect complexes are globally termwise bounded complexes of finite locally free sheaves. Extension closure uses degreewise exactness and the proved local vector-bundle extension theorem. StrictK and its supported version use the actual quasi-isomorphism S-construction.
- The degree-zero vector-bundle map preserves all ambient exact sequences, including ones which only split locally. Its source is the vector-bundle S-theory, not the public vector-bundle Quillen Q-theory.
- Open restriction acts termwise, preserves quasi-isomorphisms and strict boundedness, and induces the stated strict K-map. Support is actual acyclicity after this restriction; the supported-to-zero quasi-isomorphism is proved without asserting a localization theorem.
- The locally perfect predicate uses the actual localization at quasi-isomorphisms and local isomorphisms to strict perfect representatives. Derived-isomorphism invariance and open-restriction stability use actual localization and restriction functors. No global strict representative is demanded.
- LocalLifting constructs actual sections/lifts on open neighborhoods through arbitrary epimorphisms, using pullbacks and local vector-bundle splitting. This is a single-degree local lemma, not global projectivity or a completed complex comparison.

No semantic correctness blocker was found in this scope. On a non-quasi-compact scheme the local predicate does not impose a uniform global Tor-amplitude condition. The distinction is correctly retained in the development documentation.

## Explicit exclusions

This review establishes none of the Quillen Q/S comparison, Gillet–Waldhausen equivalence, extension closure or Waldhausen K-theory of all locally perfect complexes, strict-versus-all-perfect equivalence, K₀ commutativity from additivity, nonconnective spectra, or Thomason–Trobaugh localization. There is no claimed identity between StrictK and the existing public Scheme.K.

## Verification

All source fingerprints match `logs/perfect-complexes-checked-sources.sha256`; the manifest SHA-256 is `12fd52193d7089a265050f5321da3262ef39144d5b3927814986939b23a46174`. That author manifest also records its focused audit source. This independent review changes no source or import in the frozen set.

A focused current-source rehash build of LocalLifting, Support, LocalRestriction, and ChangeWeakEquivalences passed with 2,880 jobs. Their transitive imports cover all seventeen leaves. The evidence is `logs/perfect-foundations-independent-build.log`. This does not claim a full repository or archive build.

The separate current-source post-build audit `audits/PerfectFoundationsIndependentAudit.lean` passed all 270 stable Waldhausen/perfect declarations, including private/generated helpers, with only propext, Classical.choice, and Quot.sound. Its output is `logs/perfect-foundations-independent-all-axioms.log`. The final frozen-source hash check is `logs/perfect-foundations-independent-hash-check.log`.

Independent source, contract, current-source build, and transitive-assumption review are accepted for these foundations only. The exclusions above remain in force.
