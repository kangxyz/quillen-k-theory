# Independent review: full finite-resolution theorem

Reviewed 2026-10-09 independently of the proof author. This extends the earlier length-one review; public facade integration remains a separate coordinator action.

## Contract

The inputs are a small preadditive category with finite biproducts, a genuine exact structure, and a replete full object class containing zero and closed under extensions and kernels of admissible epimorphisms between its objects. Finite-product closure is an explicit interface instance and is derivable from the other closure hypotheses. Every ambient object has an actual finite admissible resolution. Resolution lengths may vary without a common bound.

This matches the algebraic hypotheses and length-stratum reduction of [Weibel, The K-book, Chapter V, Theorem 3.1 and Proposition 3.1.1](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.V.pdf), chapter pages 20–21. No K-equivalence, inverse, homotopy equivalence, comma contraction, projective lifting property, or ambient admissible-subobject closure is an input to the unrestricted theorem.

## Source review

All fourteen canonical resolution modules were inspected, with the substantive new review concentrated on Transport, Presentation, Strata, SubcategoryComparison, Bounded, Union, and Theorem. The frozen set contains 2,004 source lines.

- FiniteResolution records genuine conflations, resolving middle terms, and a resolving terminal syzygy. Its zero case is actual membership. Transport changes the augmentation through an isomorphism without altering length.
- Presentation independence uses a genuine pullback and the assumed kernel/extension closure. The simultaneous stratum induction uses a cover of the actual middle object and the kernel sequences of composite deflations; it does not use an unjustified projective horseshoe or comparison-map lift.
- Nested inherited exact categories are identified by a fully faithful, essentially surjective exact functor which reflects admissibility. Actual length-one resolutions inside the successor stratum establish every adjacent comparison. Ordered transitions preserve the specified forward inclusion map.
- Union constructs an actual categorical diagram and cocone. An arbitrary ambient Q-arrow is represented in one stage by bounding the resolutions of its source, target, apex, left kernel, and right cokernel. Including the latter two witnesses is essential for inherited admissibility.
- The stage legs are faithful; their object maps reflect equality. The categorical finite-chain lifting and eventual-equality arguments therefore prove a genuine simplicial nerve colimit, rather than merely an objectwise union.
- The filtered-realization theorem is applied to these constructed colimit and transition-equivalence data. It constructs actual homotopy equivalences with the canonical stage legs, without requiring coherent chosen inverses or a uniform bound.
- The zero-stratum comparison composes to the actual original Q-inclusion. The canonical zero-object natural isomorphism supplies exactly the normalized functor used by ExactFunctor.KMap. The final group equivalence has the original inclusionKMap as its forward homomorphism by a definitional identity.

No semantic correctness blocker was found. The accepted mathematical scope is the full objectwise-finite resolution theorem, including classifying-space homotopy equivalence and all nonnegative canonical K-map bijections. It proves no geometric resolution property for an arbitrary regular scheme.

## Verification

The independent focused current-source command `lake --rehash build Quillen.Resolution.Theorem` passed with 2,230 jobs on Lean 4.34.0 and pinned mathlib 5ed2965256430c3649e86755f9576b54eca72435. Only style/linter warnings were emitted. The log is `logs/resolution-full-independent-build.log`.

This explicit rehash check addresses source timestamps later than some cached objects after the canonical-only cleanup. No resolution source or import was changed by this review.

All fourteen frozen source hashes match `logs/resolution-full-source-sha256.txt` before and after the build. The manifest SHA-256 is `0879ae6f0434928202846ab204026e123eea84ef7e03191f35732a52869c7989`.

The independent expanded audit `audits/ResolutionPerfectIndependentAudit.lean` passed all 630 resolution-origin declarations, including private/generated helpers, with only propext, Classical.choice, and Quot.sound. Its output is `logs/resolution-perfect-independent-all-axioms.log`. The same audit independently checks the separately reviewed Waldhausen/perfect foundations; these are not assumptions of the resolution theorem.

Independent source, contract, current-source build, and transitive-assumption review are accepted for the full finite-resolution endpoint. Public integration and archive verification remain separate coordinator-owned steps.
