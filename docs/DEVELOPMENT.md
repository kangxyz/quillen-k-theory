# Development policy

[CONTRIBUTING](../CONTRIBUTING.md) remains the authority for setup, general
authoring, incremental checks and dependency changes. This page owns the
candidate-specific authoring and admission workflow and the affected-check configuration.

## Normal task

Use the prepared workspace: encode/prove, compile the exact changed leaf, and
repair from its diagnostics. For example:

```sh
lake build Quillen.KTheory.Functor
```

At meaningful final delivery, run the selected check once:
`python3 -m lean_ci check --config .github/lean-ci.toml --root . --requested-base ACCEPTED_COMMIT`. Use a consumer only for a concrete
interface question. After a failure, keep completed categories and use the
[incremental recovery](../CONTRIBUTING.md#tests-and-checks). Consult
setup, dependency/cache or environment guidance only for an actual missing or
invalid input; preserve the prepared workspace and matching evidence.

## Aglib candidates

The [`Quillen/Aglib/` source tree](../Quillen/Aglib/README.md) holds maintained
general-theory source developed in Quillen for later inclusion in Aglib. Follow the [shared candidate policy](https://github.com/kangxyz/aglib/blob/main/docs/DEVELOPMENT.md#downstream-candidates-for-aglib).

Use `Quillen/Aglib/` as the source location and `Quillen.Aglib` as the temporary
module prefix. Mirror the intended Aglib mathematical path below it. Keep
native mathematical declaration namespaces, so migration normally changes
imports rather than the meaning or names of the interfaces. A package-root
`Aglib/` tree would shadow the upstream dependency and must not be used here.

Before adding a candidate, check existing Mathlib and Aglib APIs. Keep its
imports in Mathlib, Aglib, or explicitly designated general candidate leaves;
keep host applications and their adapters outside this subtree. Coordinate
one implementation owner across downstream libraries. Record the intended
upstream module, exact hypotheses and current consumer in the module docstring,
and describe interfaces and main results in each occupied family's README.

Candidates are enrolled and checked as ordinary Quillen production modules.
They are not scratch, a separate Lake library, or proof of upstream acceptance.
Once an accepted upstream revision is pinned, retarget the consumers and remove
the local implementation; avoid duplicate implementations and default legacy
facades.

Existing general-theory implementations are staged here before admission to
Aglib. Specialized applications remain in their mathematical host families and
import the focused candidate leaves. Mixed files separate their general
constructions from their curve, arithmetic or K-theory endpoints.

The candidate module prefix records the temporary implementation owner. Source
relocation preserves existing declaration names, objects, hypotheses and chosen
comparison maps; it does not by itself redesign the public mathematical API.
Future upstream admission selects canonical native namespaces and removes the
accepted local implementation together with its old imports.

## Affected check scope

[`.github/lean-ci.toml`](../.github/lean-ci.toml) is this library's declarative input
to the common `lean_ci` implementation. It identifies root production `Quillen`,
positive tests `QuillenTest`, support sources and the separately built downstream
package `examples/downstream`, whose Lake library is `Consumer`. Package identity,
source root and namespace are distinct. This repository supplies no Python
adapter, selector, binding callback or CI bootstrap implementation.

Install the compatible `lean-incremental-ci` distribution from the immutable Aglib
tooling revision pinned by the reusable workflow. That revision is independent of
the mathematical Aglib pin. For an already obtained tooling checkout, install its
`ci/` package with Python 3.11 or later. Do not discover tooling from ambient sibling
checkouts or mutable branches. The consumer workflow delegates setup, cache restore,
checks, finalization and qualified publication to that same shared release.

The local entry is:

```sh
python3 -m lean_ci check --config .github/lean-ci.toml --root .
```

Use `--requested-base REF` to widen the accepted comparison, `--target MODULE` for
an explicitly selected module, and external `--state PATH` / `--progress PATH` to
retain compatible successes after repair. The common selector includes affected
production, Test and client consumers through old/new reverse-import edges,
including deleted/renamed identities. It builds only modules present in the current
source. Import-only facades remain enrolled; they are not a reason to build an
unrelated umbrella or omit a reachable defining origin.

Source checks run before native work and need no Lean for documentation-only scope.
Native checking requires the pinned toolchain, dependencies and compatible caches.
Prepare only the selected dependency/cache closure when needed:

```sh
python3 -m lean_ci prepare --config .github/lean-ci.toml --root .
```

The preparation entry accepts the same `--requested-base` and `--target` selection.
It restores compatible artifacts; it does not supply passed checker evidence.
The common runtime owns setup/resource limits and admitted remote profiles. Source
style and budgets use source inputs; declaration/builtin and axiom checks retain
their own environment-dependent predicates. Selected tests execute through Lake.
Client checks use their own cwd and package identity, with exact defining-origin
coverage, including private and generated declarations.
`QuillenTest.lean`, `QuillenTest/Axioms.lean` and
`examples/downstream/Audit.lean` remain enrolled as `formal_only` exhaustive audit
entrypoints for explicit mathematical adoption work. They are not expected-failure
fixtures or ordinary selected positive tests. Ordinary checks
use the common selected-origin axiom and private/generated inventory predicates;
that does not claim equivalence with an older whole-library audit. Mathematical
audit/support sources remain available; common drivers own ordinary execution.

Every successful individual checker result is retained under its actual input key.
A new common predicate does not inherit incompatible old checker success. Until
all required obligations close, initialization remains explicitly incomplete across
subsequent heads; failed/interrupted work does not erase compatible successes.
Missing coverage requires uncovered checks, not cleaning or recompiling compatible
artifacts. API failure remains an error rather than invented empty history.

Hosted CI uses the common `plan`, `source`, `native`, `finalize` lifecycle with the
same config and external state. Source/preflight is independent of long native
work. Only qualified completed coverage can become a native baseline or publish
complete-coverage cache evidence. Finalization aggregates existing results and
input correspondence; it does not execute checkers again. Native artifact exports
retain the root and downstream workspace identities and use the common cache action.

Historical receipts retain their actual source and predicate. The former umbrella
and target-first declaration checks are not the new runtime-first exact-origin
predicate. The shared compatibility policy may import only genuinely matching old
coverage; there is no hardcoded initial or repair-parent commit in this consumer.
