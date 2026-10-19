# Agent guidance

- Follow [CONTRIBUTING.md](CONTRIBUTING.md) for source, checks and documentation.
- Follow the [normal task recipe](docs/DEVELOPMENT.md#normal-task): prove and compile the exact changed leaf in the prepared workspace. Preserve caches and compatible validation across review, merge, integration and publication; missing artifacts, receipts or a phase transition do not assign a whole-library rebuild.
- At meaningful final delivery, include applicable declaration/text-style lint, affected `QuillenTest`/client tests and source/trust checks, with provider compilation/lint before expensive consumers. Reuse completed categories after repairs. Helper returns, commits and merges do not trigger standalone lint/tests; compilation alone does not supply their separate coverage. [CONTRIBUTING.md](CONTRIBUTING.md#tests-and-checks) owns the commands and scope.
- For new general theory intended for Aglib, follow the
  [candidate convention](docs/DEVELOPMENT.md#aglib-candidates) before choosing an implementation
  owner; keep application adapters outside that subtree.
- Keep history, workflow, evidence/provenance, package summaries and operational
  guidance in `docs/`.
  Source-family READMEs and focused guides under `Quillen/` own mathematical
  results, API/interfaces, exact hypotheses and remaining inputs. Maintain one
  authority and update inbound links when moving content.
