# The actual all-acyclic double-S base

`AllWeak/OrdinaryRows.lean` transports the proved actual all-acyclic
inclusion/lift exact equivalence through the original quotient-row
postcomposition and original S-maps. It supplies:

- `ordinaryRowsInclusion` and `ordinaryRowsLift`, retaining every original
  nested diagram component and arrow;
- strict naturality in every outer ordinal map, while the inner S-map is
  the existing original simplicial postcomposition;
- `ordinaryRowsIso`, whose two natural maps are strictly inverse;
- preservation of the original all-zero simplex in every pair of degrees;
- `ordinaryDiagonalIso`, the corresponding actual original double-S
  diagonal isomorphism.

The source diagram is literally
`ordinarySRows (acyclicStructure (AllWeak.nested W))`, and the target is
literally `ordinarySRows W`. Both retain the original fine weak structure.
The original categorical results had independent universes; this assembly
explicitly uses the common object/hom universe required by ordinarySRows.
No double-S loop equivalence or global fiber theorem is asserted.

Source-origin and original-map/arrow/zero/ordinal/degree-zero consumers are
in `audits/AllWeakOrdinaryRowsAudit.lean`; the terminal fixed17-origin audit and all12 consumers pass warning-free
in `logs/all-weak-ordinary-rows-audit-final.log`, with standard-only recursive
axioms. Frozen hashes are in `logs/all-weak-ordinary-rows-sources.sha256`.
Independent review passed: fresh two-source rebuild of this and the
contractible-source companion, fixed42 combined origins and29 consumers,
warning-free with all hashes unchanged. The earlier frozen all-weak3 and
categorical2 sources are not modified.
