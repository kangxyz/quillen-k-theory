> Preserved original record. [Original source](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#shared-cache-metadata-during-final-checks) · [Context](original-context.md) · [Case index](README.md) · [Previous record](full-node-overlap-reanchoring.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Shared cache metadata during final checks

During the 0.10.0 upgrade with Lean 4.34.1 and Aglib `2c34f185`, the native
entry reported `Reflective input changed during this attempt` on shared `.ilean`
artifacts after successful checker commands. The
[pinned input observer](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/scripts/lean_ci/state.py)
includes inode identity and `ctime` in its stability checks.
[Linux inode metadata](https://man7.org/linux/man-pages/man7/inode.7.html)
changes when hard-link counts change, even with unchanged bytes and `mtime`.
Read-only artifact sharing therefore needs a stable metadata interval too.

The successful preparation replaced hardlinked native artifacts in an idle,
task-owned workspace's root and dependency `.lake/build` trees with private
reflink inodes. Every file retained its bytes, permissions, ownership and
modification time; Lake hashes and traces, sources, pins and checking rules
were preserved. The observed input families include generated C files.
Check quota headroom before preparing reflinks, which still consume allocation
allowance in the measured XFS project quota.

The unchanged native final entry then passed the library and in-package tests,
entry and text checks, declaration lint and the 89,314-declaration axiom audit.
Its retained compilation artifacts required no new Lean frontend invocations.
This addresses repeated input invalidation; further declaration-elaboration
optimization remains open.
