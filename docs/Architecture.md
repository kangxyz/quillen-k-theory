# Architecture

The source is organized by mathematical objects and reusable interfaces.
Directories are extensible: add a subject when it has actual definitions or
proofs, rather than creating empty layers for a future programme.

## Source boundaries

| Location | Purpose |
| --- | --- |
| `Quillen/` | Reusable mathematics |
| `Quillen.lean` | Generated complete import surface |
| `Quillen/<Subject>.lean` | Whole-topic imports; generated or manually maintained |
| `Tests/` | Maintained tests and the library axiom audit |
| `examples/downstream/` | Independently configured client package |
| `docs/` | Reader documentation for the library |
| `scripts/` | Import generation, cache acquisition, and checks |

Tests and clients depend on the library; the library does not depend on them.
Implementation modules import individual modules rather than broad entrypoints.
The structural checker rejects import cycles and reverse test/client dependencies.

## Mathematical organization

Algebra, category theory, and topology provide foundations. K-theory, dévissage,
localization, schemes, resolution, perfect complexes, and Waldhausen constructions
build on those interfaces. Category theory and topology interact, so subject
directories do not impose an artificial total order on dependencies.

A module should have a useful independent consumer. Split a growing development
along its objects or interfaces, keeping comparisons dependent on foundations.
Module paths describe ownership; declaration namespaces need not mirror them.

## Entry points and extension

`Quillen.Library`, `Quillen.Scheme`, and `Quillen.Resolution` select public
interfaces. Generated subject facades offer whole-topic imports, while the
generated root enrolls every library module. Generation preserves manually
authored facades and discovers new subject directories.

The generator discovers modules and subjects as the library grows. CI validates
each change against the current source graph. See
[CONTRIBUTING.md](../CONTRIBUTING.md) for extension and compatibility rules.

## Trust checks

`scripts/check.sh` builds the library and `Tests`, then explicitly runs
`Tests/Axioms.lean` and the downstream package's `Audit.lean`. Explicit replay
is needed because reusing a cached compiled module does not rerun its audit
commands.

The library audit discovers declaration names from imported module inventories
and from declarations local to the current environment. It selects declarations
whose defining module belongs to `Quillen`, including private helpers, together
with declarations in the `Quillen` namespace. It deduplicates names and rechecks
the defining-origin predicate before examining dependencies. Declaration
selection depends on source origin and namespace rather than a fixed list of
public theorem names.

For each selected declaration, `collectAxioms` follows transitive dependencies
and rejects any axiom outside `propext`, `Classical.choice`, and `Quot.sound`.
The inventory discovery avoids eagerly inspecting unrelated constant bodies.
Audit success concerns the selected kernel declarations; it does not establish
the mathematical interpretation of a definition, a comparison with an external
source, or a theorem absent from the library.
