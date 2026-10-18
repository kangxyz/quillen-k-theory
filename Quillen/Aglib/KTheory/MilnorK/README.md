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

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.Aglib.KTheory.MilnorK.K2.DVR.TameKernel` | Additional actual-DVR tame-kernel/unit-symbol-span proof on Aglib objects, with canonical uniform-residue transport |
| `Quillen.Aglib.KTheory.MilnorK.K2.FiniteField` | Additional integral finite-field Milnor K2 vanishing on Aglib objects, including uniform degree two; actual Quillen-G2 comparison remains separate |

## Native Milnor symbols

Milnor objects, symbols, field maps and residue maps are imported directly from
Aglib `16aa08a9` through their precise native leaves. Its public group is
`MilnorK.K F 2`; `MilnorK.twoEquiv` is the canonical ordered-symbol and field-map
comparison to the retained tensor quotient `MilnorK.K2.Group F`.
The additional candidate
[`FiniteField`](K2/FiniteField.lean) proves
`k2_eq_zero_of_finite` and `finiteField_k2_subsingleton` for both presentations
under exactly `[Field k] [Finite k]`, including orders two and three. Quillen
keeps no duplicate Milnor foundational implementation or old module aliases.

The original Steinberg, projective/module K2 maps and their characteristic-zero
equivalences are documented in the [field family](../../../KTheory/Field/README.md).
Their original scalar-operation marking and DVR normalization belong to the
[scalar-action family](../../../KTheory/LowDegreeScalarAction/README.md).
