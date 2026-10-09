# Quillen K-theory through the Q-construction

This is an incremental formalization project, not a claim that all of algebraic K-theory is already implemented. Every completion claim must identify Lean-checked declarations. An unproved field in an input structure is an assumption on that structure, not a theorem about exact categories.

## Mathematical target

For a small exact category E, construct the category Q(E). A morphism X → Y is an isomorphism class of spans X ← M → Y whose left leg is an admissible epimorphism and right leg is an admissible monomorphism. Compose using pullback. Form the nerve N(Q(E)); after supplying geometric realization and based homotopy infrastructure define K_n(E) = π_(n+1)(B Q(E), 0) for n ≥ 0. The basepoint is the zero object. Defining this expression is distinct from proving its expected properties or computing groups.

## Milestones and acceptance criteria

1. **Reproducible foundation.** Pin Lean and mathlib, build a minimal library, record dependency versions and exact build commands. No `sorry` or project axioms.
2. **Admissible spans and their equivalence.** Define admissible morphism classes and span isomorphisms. Prove reflexivity, symmetry and transitivity, then form quotient hom types. Check all declarations.
3. **Pullback composition.** Use actual pullbacks, prove admissibility of both composite legs from stability/composition assumptions, and prove independence of chosen representatives. Do not assume quotient compatibility.
4. **The category Q.** Prove unit and associativity laws via canonical pullback isomorphisms. Instantiate the category structure; test it on elementary cases.
5. **Exact-category interface.** Connect the needed span calculus to a standard exact-category definition, making all prerequisites explicit. A generic span calculus alone does not prove this connection.
6. **Nerve.** Construct the simplicial nerve of the resulting category using mathlib. Identify the vertex determined by the zero object and document universe restrictions.
7. **Classifying space and K-groups.** Audit existing realization and homotopy APIs. Implement the missing bridge rather than postulating it. Define the based groups with the correct indexing, and prove group/abelian group structures wherever supported. If substantial infrastructure is missing, state exactly where verified results stop.
8. **Theorems and examples.** Functoriality, zero-category sanity check, identification of K_0 with the Grothendieck group, then further foundational theorems. These are separate substantial milestones, not consequences of merely writing a definition.

## Validation rules

- Run `lake build` for every milestone and preserve a build log.
- Run the project assumption audit, rejecting `sorry`, `admit`, and custom `axiom` declarations.
- Use `#print axioms` on central results; distinguish Lean's foundational axioms from any new assumptions.
- Document structure hypotheses and prove adapters rather than silently identifying different notions.
- Do not count an unchecked file, intended proof, or statement encoded as a field as completed mathematics.

## Reproducible dependencies

Lean: `leanprover/lean4:v4.34.0`.
mathlib: stable tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`.
The versions were read from the official mathlib repository on 2026-10-08. Master used a release candidate; this project deliberately pins the matching stable release.

## Important mathematical safeguards

- The zero object in the exact category defines a distinguished object of Q; it is generally not a zero object in Q.
- Generic homotopy infrastructure gives a group for K_0 = π_1 and a commutative group for K_n with n ≥ 1. Proving K_0 commutative is a separate Q-specific theorem.
- mathlib v4.34.0 already supplies restricted span bicategories, simplicial nerves, geometric realization and homotopy groups. The project reuses these actual constructions, not hypothetical replacements.
- A category constructed for two abstract morphism properties is only restricted-span infrastructure until the connection to a genuine exact structure has been proved.


## Expanded required endpoints: dévissage and localization

Both are explicitly requested goals. Implement the classical abelian versions with precise hypotheses, then prove the homotopical results; algebraic Grothendieck-group shadows alone do not satisfy them.

1. Finite admissible filtrations: actual towers of conflations, telescoping, exact-inclusion algebraic generation.
2. Full abelian subcategory inclusion: no extra extension closure for dévissage.
3. Serre quotient: reuse mathlib's actual quotient, exact quotient functor, and universal property; connect to Q and K.
4. Geometric realization of simplicial/categorical homotopies, including based natural-isomorphism coherence.
5. Quillen Theorems A and B with contractible comma categories and actual homotopy fibers.
6. Topological homotopy-fiber sequence and connecting maps, exactness, and naturality for higher homotopy groups.
7. Dévissage equivalence from finite filtration categories and the homotopical comparison.
8. Localization homotopy-fiber theorem and the resulting long exact K-sequence; identify the K₀ tail correctly.

No stage may replace these target theorems with fields or new assumptions. Existing connected-comma Final/Initial, skeletal-category folklore, or a partially implemented model category do not prove these missing results.

## Expanded required endpoints: exact-category versions (2026-10-08, 21:26 UTC)

The user explicitly requested that exact-category dévissage and localization also be formal goals, beyond the completed small abelian dévissage theorem. The general exact-category Q-construction and K-functor already exist. The new theorem endpoints remain open.

First establish primary-source theorem contracts with precise admissibility, closure, filtering, quotient-existence, and size hypotheses. Do not mechanically remove `Abelian` from the current proof or claim finite filtrations alone suffice. Audit all uses of ordinary subobject intersections, cokernels, image arguments, and quotient abelianness. Consider the appropriate exact dévissage theorem and s-filtering exact localization framework, but verify the exact source statement and connective/nonconnective low-degree scope before choosing an implementation.

Required acceptance: proved actual Q-classifying-space or canonical homotopy-fiber comparisons under legitimate explicit exact-category hypotheses; induced maps must agree with the existing exact-functor KMap. No target-equivalence fields, hidden extra axioms, or nonconnective theorem silently presented as a connective K₀-surjectivity statement. Under the later priority change below, general exact-category results and unrelated K₀ extensions are parked unless required for localization or schemes.

## Required subsequent phase: scheme K/G-theory (2026-10-08, 21:27 UTC)

Updated order, explicitly requested on 2026-10-08 at 22:18 UTC: finish the current abelian localization theorem, then proceed directly to scheme K/G-theory and its basic properties, including localization sequences. General exact-category dévissage/localization is pursued in parallel only when required by the scheme work; it is not a prerequisite. Unrelated K₀ extensions must not delay that transition. The user authorized ongoing end-to-end work on the assistant's cloud computer, with milestone reports and no publication.

Do not start the large scheme phase prematurely. Its initial theorem-contract audit must distinguish vector-bundle K-theory, perfect-complex K-theory, and G-theory of coherent sheaves. State quasi-compactness, quasi-separatedness, noetherian/regular/finite-dimensional/ample-family or resolution-property hypotheses exactly where required. Comparison maps between these models and connective/nonconnective localization tails are separate theorems, not definitional identifications. Reuse the proved genuine exact-category Q-theory where appropriate and connect every claimed sequence to actual canonical functors.
