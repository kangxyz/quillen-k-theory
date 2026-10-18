# Agent guidance

- Follow [CONTRIBUTING.md](CONTRIBUTING.md) for source, checks and documentation.
- Use incremental checks and preserve trusted caches and compatible validation
  throughout normal work, including review, merge, integration, and publication.
  Include applicable compilation, declaration/text-style lint, affected
  `QuillenTest` and client tests, and source/trust checks; build success alone
  does not supply separate lint or test coverage.
  Develop with incremental compilation and its diagnostics. Run independent
  lint and tests only at the task's final validation before delivery;
  helper returns, internal commits and merges do not trigger them. Reuse valid
  evidence and rerun only failed or newly affected checks after final-check repairs.
  Follow the affected-scope checks in
  [CONTRIBUTING.md](CONTRIBUTING.md#tests-and-checks); a phase transition alone
  does not request the complete check pipeline or a whole-library rebuild.
- For new general theory intended for Aglib, follow the
  [candidate convention](Quillen/Aglib/README.md) before choosing an implementation
  owner; keep application adapters outside that subtree.
- Keep package-wide summaries, navigation and operational guidance in `docs/`.
  Source-family READMEs and focused guides under `Quillen/` own mathematical
  results, API/interfaces, exact hypotheses and remaining inputs. Maintain one
  authority and update inbound links when moving content.
