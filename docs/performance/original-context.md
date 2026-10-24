> Preserved original record. [Original source](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#typechecking-performance) · [Context](original-context.md) · [Case index](README.md) · [Next record](repair-workflow.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

# Typechecking performance

Use focused imports and explicit mathematical interfaces when extending the
library. Proof iteration may use a temporary finite declaration-local budget
to establish correctness. Before adopting the proof, restore the standard
200,000 budget or settle a necessary finite local increase with an adjacent
explanation, then recompile the module. Keep package defaults unchanged and
retain a finite limit. Targeted profiling helps settle the retained budget;
the [contributor guide](../../CONTRIBUTING.md) gives the pinned profiling command.
This development reference records measurements and resource requirements;
mathematical interfaces and hypotheses belong to the [source-family guides](../../Quillen/README.md).

