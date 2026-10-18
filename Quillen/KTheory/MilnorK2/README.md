# Milnor tensor quotient, finite fields and DVRs

The namespace `Quillen.MilnorK2` retains the original R5 tensor presentation:
`Additive Kˣ ⊗[ℤ] Additive Kˣ` modulo the integer span of Steinberg tensors.
`Basic` constructs symbols, bilinearity, Steinberg and the universal property;
`Map` gives original field functoriality; `Symbols` derives sign identities,
skew symmetry, powers and additive symbol lifts.

`FiniteField` proves `k2_eq_zero_of_finite` and
`finiteField_k2_subsingleton` for every `[Field k] [Finite k]`. The proof uses
cyclicity of finite-field units and a finite-set Steinberg contradiction. It
has no characteristic or cardinality exclusion.

`Residue` constructs the bilinear Steinberg tame map on this same quotient,
with ordered convention `∂{u,π}=ū` and `∂{π,u}=ū⁻¹`. `DVR.Basic` realizes
its valuation and residue data for every actual DVR and its fraction field.
`DVR.TameKernel.ker_tame_eq_unitSymbolSpan` proves that its kernel is the
integer span of field symbols of two actual ring units, for every
irreducible uniformizer; `ker_chosenTame_eq_unitSymbolSpan` supplies the
chosen-uniformizer form. This does not assert Quillen unit generation,
DVR Quillen injectivity, or a marked Quillen product.

Migration comparisons preserve the tensor, span, quotient, symbol and field
maps by transparent identities. The separately returned R5 retarget patch is
unapplied. These are Milnor groups; the symbol-preserving comparison with
actual Quillen K2, positive marking, and actual finite-field G2 vanishing
remain separate obligations in the
[field and support plan](../../../docs/development/LowDegreeFieldSupport.md).
