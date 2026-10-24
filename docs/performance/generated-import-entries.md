> Preserved original record. [Original source](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#generated-import-entries) · [Context](original-context.md) · [Case index](README.md) · [Previous record](ci-dependency-handoff-and-native-resource-limits.md) · [Next record](vector-bundle-instance-inference.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Generated import entries

A fixed line allowance on an import-only entry can expire as the source graph
grows; see the [Aglib failure and pinned-linter reproduction](https://github.com/kangxyz/aglib/blob/main/docs/performance/generated-import-entries-and-file-length-limits.md#generated-import-entries-and-file-length-limits).
The existing generator now always writes `set_option linter.style.longFile 0`
for its import-only outputs, including new subjects. Generator fixtures cover
small and 1600-import entries, source growth and unchanged implementation files.
Ordinary implementation limits and native CI commands are unchanged.

