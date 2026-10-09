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
| `QuillenTest/` | Maintained tests and the library axiom audit |
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
