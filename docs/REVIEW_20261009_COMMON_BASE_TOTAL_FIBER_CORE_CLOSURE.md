# Supplement: implicit core import provenance

The independent transport/total-tail replay was strengthened after detecting
that the textual import scanner did not seed Lean's implicit Init umbrella.
The original accepted evidence remains unchanged. No production proof changed.

A separate fresh excluded-target overlay now seeds Init and recursively hashes
its source and artifact closure, adding 156 source files and 468 artifacts with
no removed prerequisite and no changed prior hash. The complete final boundary
has 4,032 prerequisite sources and 17,942 artifacts, plus exact project pins.
All three original source files were freshly rebuilt, and the fixed 41 origins
and 33 original-map consumers passed warning-free at 2026-10-09 14:18:30 UTC.
Every before/after hash matched. This supplemental result supersedes the earlier
explicit-import-only provenance scope, without altering its mathematical result.

Evidence: `logs/common-base-total-fiber-core-closure-20261009`.
Preparation: `logs/prepare-common-base-total-fiber-core-closure.py`.
Replay: `logs/verify-common-base-total-fiber-core-closure.sh`.
This remains outside the delivered 12:10 source boundary.
