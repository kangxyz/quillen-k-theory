/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.StabilizedExtension
public import Quillen.AlgebraicGeometry.PerfectComplexes.RestrictionFunctoriality

/-!
# Stabilized extension along arbitrary compact affine open immersions

The proved Spec R stabilization transports along the actual open-image and
scheme-isomorphism restriction comparisons. An arbitrary compact open immersion
into an affine scheme admits a global strict-perfect extension of the original
complex plus its positive shift. The literal restriction, biproduct and integer
shift are retained. No presentation of the source as a chosen open is supplied.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedModules Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Original restriction preserves the literal stabilization, with the actual
integer-shift and biproduct comparisons. -/
def restrictStabilizationIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (E : Complex X) :
    (restrict j).obj (E ⊞ E⟦(1 : ℤ)⟧) ≅
      (restrict j).obj E ⊞ ((restrict j).obj E)⟦(1 : ℤ)⟧ := by
  let : PreservesBinaryBiproducts (restrict j) := preservesBinaryBiproducts_of_preservesBiproducts _
  exact (restrict j).mapBiprod E (E⟦(1 : ℤ)⟧) ≪≫
    biprod.mapIso (Iso.refl _) (((restrict j).commShiftIso (1 : ℤ)).app E)

lemma exists_strict_stabilized_extension_into_spec (R : CommRingCat.{u})
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j] [CompactSpace U]
    (E : Complex U) (hE : locallyPerfect U E) :
    ∃ Q : Complex (Spec R), strictPerfect (Spec R) Q ∧
      Nonempty ((toDerived U).obj ((restrict j).obj Q) ≅
        (toDerived U).obj (E ⊞ E⟦(1 : ℤ)⟧)) := by
  let W := j.opensRange
  have hW : IsCompact (W : Set (Spec R)) := isCompact_range j.continuous
  let E' := (restrict j.isoOpensRange.inv).obj E
  have hE' := locallyPerfect_restrict j.isoOpensRange.inv hE
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ :=
    Affine.locallyPerfect_exists_global_strict_stabilized_extension R W hW E' hE'
  let eleft : (restrict j).obj Q ≅
      (restrict j.isoOpensRange.hom).obj ((restrict W.ι).obj Q) :=
    ((restrictCompIso j.isoOpensRange.hom W.ι ≪≫
      eqToIso (restrict_congr j.isoOpensRange_hom_ι)).symm).app Q
  let eE : (restrict j.isoOpensRange.hom).obj E' ≅ E :=
    (restrictCompIso j.isoOpensRange.hom j.isoOpensRange.inv ≪≫
      eqToIso (restrict_congr j.isoOpensRange.hom_inv_id) ≪≫ restrictIdIso U).app E
  let eright := restrictStabilizationIso j.isoOpensRange.hom E' ≪≫
    biprod.mapIso eE ((shiftFunctor (Complex U) (1 : ℤ)).mapIso eE)
  exact ⟨Q, hQ, ⟨(toDerived U).mapIso eleft ≪≫
    restrictDerivedIso j.isoOpensRange.hom eQ ≪≫ (toDerived U).mapIso eright⟩⟩

lemma exists_strict_stabilized_extension_into_affine {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [IsAffine X] [CompactSpace U]
    (E : Complex U) (hE : locallyPerfect U E) :
    ∃ Q : Complex X, strictPerfect X Q ∧
      Nonempty ((toDerived U).obj ((restrict j).obj Q) ≅
        (toDerived U).obj (E ⊞ E⟦(1 : ℤ)⟧)) := by
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := exists_strict_stabilized_extension_into_spec _ (j ≫ X.isoSpec.hom) E hE
  exact ⟨(restrict X.isoSpec.hom).obj Q, strictPerfect_restrict X.isoSpec.hom hQ,
    ⟨(toDerived U).mapIso ((restrictCompIso j X.isoSpec.hom).app Q) ≪≫ eQ⟩⟩

end Quillen.PerfectComplexes
