# Homotopy equivalences and component products

## Generic component products

`Topology.HomotopyEquiv.ComponentSigma`,
`Topology.HomotopyGroups.Loop.ComponentProduct` and
`NormalizedComponentProduct`, with `Topology.Realization.OpenComponents`,
construct generic component products and their normalized identity slice at
the exact assumptions. See the
[component-product client](../../../examples/downstream/Consumer/LoopComponentProduct.lean).

The displayed right concatenation is order-sensitive. The standard product
retains the order of its actual zero-component loop and selected representative.
The [original Q-loop application](../../KTheory/GrothendieckComparison/README.md)
retains its continuous discrete K₀ classifier, normalized neutral slice,
representative-change homotopies and ordinary forward-map naturality. Its
[plus-model specialization](../../KTheory/Plus/README.md) retains the original
completion component, positive labels and track. No natural chosen inverse,
H-space, A∞ or infinite-loop splitting is asserted.
