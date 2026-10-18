# Finite fields and the Milnor tame kernel

These general candidates extend the supplied Aglib Milnor groups and maps.
Their intended upstream modules are `Aglib.KTheory.MilnorK.K2.FiniteField`
and `Aglib.KTheory.MilnorK.K2.DVR.TameKernel`. The independently configured
[`MilnorInterfaces` client](../../../../examples/downstream/Consumer/MilnorInterfaces.lean)
consumes both; the separate R5 Milnor retarget proposal also consumes the
finite-field theorem. These are algebraic inputs to the low-degree field
and actual-DVR comparisons under development.

[`K2/FiniteField`](K2/FiniteField.lean) proves integral degree-two vanishing
for every `[Field k] [Finite k]`, including characteristic two and the fields
with two and three elements. The original tensor endpoint is
`MilnorK.K2.k2_eq_zero_of_finite`; `MilnorK.k2_eq_zero_of_finite` and the
named subsingleton instances give the same result for `MilnorK.K k 2` through
the supplied ordered-symbol comparison `MilnorK.twoEquiv`.

[`K2/DVR/TameKernel`](K2/DVR/TameKernel.lean) defines the integer span
`MilnorK.K2.DVR.unitSymbolSpan` of original field symbols of two ring units.
For every actual DVR and fraction field, `ker_tame_eq_unitSymbolSpan` and
`ker_chosenTame_eq_unitSymbolSpan` identify it with the original tame kernel.
There is no residue-cardinality or characteristic restriction. The ordered
convention remains `∂{u,π}=ū` and `∂{π,u}=ū⁻¹`.

For the canonical public residue,
`MilnorK.DVR.ker_residue_one_eq_unitSymbolSpan_comap` identifies the kernel
of `MilnorK.DVR.residue R K 1` with the comap of this span under
`MilnorK.twoEquiv K`. The pointwise theorem
`residue_one_eq_zero_iff_mem_unitSymbolSpan` retains the same normalization.
These statements use Aglib's actual `oneEquiv` residue compatibility; they
do not identify a Milnor group with Quillen K₂ or determine an actual Quillen
localization boundary.

Use focused candidate imports under `Quillen.Aglib.KTheory.MilnorK`; all
tensor, symbol, field-map, valuation, residue-data and tame definitions come
directly from Aglib. No old Quillen Milnor implementation is retained.
