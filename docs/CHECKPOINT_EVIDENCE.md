# Source checkpoint evidence

A source release contains the canonical checked import closure, compatible
Lean audit programs, downstream examples, review reports and concise
verification evidence. `CHECKPOINT.json` lists every actual file member and
its SHA256 digest. The exact archived sources are validated separately;
packaging alone is never a successful build.

The default compact packaging policy omits raw evidence files larger than
128 KiB, except the final `logs/checkpoint-rebuild.log`, which is always
included. Repeated dependency inventories and per-file before/after success
logs account for most of this reduction. `logs/RELEASE_EVIDENCE.json` records
the relative path, size and exact preparation-time digest of each omitted
raw evidence file. Those records are receipts, not claims that the omitted
files are archive members. Full raw evidence remains in the working evidence
store. `--full-evidence` produces the larger source/evidence package when
needed.

Compilation overlays, Lean build products, symbolic links and Python caches
are excluded. The verifier checks the exact initial inventory, rebuilds the
frozen source boundary, runs public and independent downstream checks plus
all-declaration and central original-map audits, removes generated caches,
and records the final archive inventory. A retained project cache can be
used only after its existing verified marker, complete cache hashes and
pinned dependencies agree. The resulting metadata distinguishes that
incremental mode from a clean independent rebuild.

Released archives are immutable. Later packaging improvements and new
mathematical endpoints apply to the next checkpoint; they do not modify
previously delivered bytes.
