# Agent guidance

- Follow [CONTRIBUTING.md](CONTRIBUTING.md) for source, checks and documentation.
- Use incremental checks and preserve trusted caches and compatible validation
  throughout normal work, including review, merge, integration, and publication.
  Follow the affected-scope checks in
  [CONTRIBUTING.md](CONTRIBUTING.md#tests-and-checks); a phase transition alone
  does not request the complete check pipeline or a whole-library rebuild.
- For new general theory intended for Aglib, follow the
  [candidate convention](Quillen/Aglib/README.md) before choosing an implementation
  owner; keep application adapters outside that subtree.
