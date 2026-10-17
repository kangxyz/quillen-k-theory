/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.SupportedQCDenominators
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenGluing.OneChartDenominator
/-! # Original global roofs across a one-affine-chart complement

The actual geometric one-chart denominator theorem supplies the exact supported
QC input, and the proved unit-cone bridge gives the unchanged global roof
interface. Compactness of the ambient scheme follows from its actual cover by
the compact original open and the affine chart; it is not an extra hypothesis.
No factorization or roof property is supplied in these geometric conclusions.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
variable (R : CommRingCat.{u}) {U X : Scheme.{u}}
  [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) (k : Spec R ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)

include R k hcover

/-- Genuine one-chart geometry supplies supported QC denominators for the original open. -/
lemma oneChart_hasSupportedQCDenominators : HasSupportedQCDenominators j := by
  intro A B hA b hb hB hz α
  let := hb
  exact exists_perfect_denominator_across_spec_of_qc_target R j k hcover hA b hB hz α

/-- Unconditional original global roofs when the complement is covered by one affine chart. -/
lemma oneChart_hasDerivedRoofs : HasDerivedRoofs j := by
  let : CompactSpace X := ⟨by
    convert (isCompact_range j.continuous).union (isCompact_range k.continuous) using 1
    ext x
    simp only [Set.mem_univ, Set.mem_union, true_iff]
    exact hcover x⟩
  exact hasDerivedRoofs_of_supportedQCDenominators j
    (oneChart_hasSupportedQCDenominators R j k hcover)

omit R k hcover in
/-- The supported denominator theorem retains an arbitrary affine chart presentation. -/
lemma affineChart_hasSupportedQCDenominators {V : Scheme.{u}} [IsAffine V]
    (k : V ⟶ X) [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) :
    HasSupportedQCDenominators j := by
  apply oneChart_hasSupportedQCDenominators Γ(V, ⊤) j (V.isoSpec.inv ≫ k)
  intro x
  rcases hcover x with hx | ⟨y, hy⟩
  · exact Or.inl hx
  · refine Or.inr ⟨V.isoSpec.hom y, ?_⟩
    change (V.isoSpec.hom ≫ V.isoSpec.inv ≫ k) y = x
    simpa only [Iso.hom_inv_id_assoc] using hy

omit R k hcover in
/-- Original global roofs are independent of the chosen presentation of the affine chart. -/
lemma affineChart_hasDerivedRoofs {V : Scheme.{u}} [IsAffine V]
    (k : V ⟶ X) [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k) : HasDerivedRoofs j := by
  apply oneChart_hasDerivedRoofs Γ(V, ⊤) j (V.isoSpec.inv ≫ k)
  intro x
  rcases hcover x with hx | ⟨y, hy⟩
  · exact Or.inl hx
  · refine Or.inr ⟨V.isoSpec.hom y, ?_⟩
    change (V.isoSpec.hom ≫ V.isoSpec.inv ≫ k) y = x
    simpa only [Iso.hom_inv_id_assoc] using hy

end Quillen.PerfectComplexes.OpenDerivedImage
