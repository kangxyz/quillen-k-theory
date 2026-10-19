/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawGeometry
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliarySupportMaps

/-!
# The three actual support rows inside the existing quasi-compact pair geometry

The acyclicity opens are the union with the localization open, the auxiliary open, and its
inverse image on the localization open. Only the two ambient schemes need be quasi-compact.
The two row arrows retain the existing support-enlargement and restriction squares. Applying
the existing polynomial or Laurent endofunctor therefore stays in the same pair category.
No localization nullhomotopy or raw-stage map is supplied by these geometric wrappers.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Bass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedRawBass.Rows
open GlobalSectionChangeIndex.ParameterAuxiliarySupport
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [CompactSpace U] [CompactSpace X] (T : X.Opens)

/-- The source row vanishes on the original union open. -/
def source : Scheme.QuasiCompactOpenPairs.{u} :=
  ⟨supportOpenPair (unionOpen j T), (by change CompactSpace X; infer_instance)⟩

/-- The middle row vanishes on the original auxiliary open. -/
def middle : Scheme.QuasiCompactOpenPairs.{u} :=
  ⟨supportOpenPair T, (by change CompactSpace X; infer_instance)⟩

/-- The target row vanishes on the original inverse-image open. -/
def target : Scheme.QuasiCompactOpenPairs.{u} :=
  ⟨supportOpenPair (inverseOpen j T), (by change CompactSpace U; infer_instance)⟩

/-- The contravariant source-to-middle arrow retains the existing enlargement square. -/
def enlargement : middle T ⟶ source j T :=
  ObjectProperty.homMk (enlargementPair j T)

/-- The contravariant middle-to-target arrow retains the existing restriction square. -/
def restriction : target j T ⟶ middle T :=
  ObjectProperty.homMk (supportRestrictionPair j T)

omit [CompactSpace U] in
/-- Forgetting the compactness wrapper changes no part of the enlargement square. -/
theorem enlargement_pair :
    Scheme.quasiCompactOpenPairsInclusion.map (enlargement j T) = enlargementPair j T := rfl

omit [IsOpenImmersion j] in
/-- Forgetting the compactness wrapper changes no part of the restriction square. -/
theorem restriction_pair :
    Scheme.quasiCompactOpenPairsInclusion.map (restriction j T) = supportRestrictionPair j T := rfl

omit [CompactSpace U] in
/-- The support-enlargement ambient morphism is still the literal identity. -/
theorem enlargement_right : (enlargement j T).hom.hom.right = 𝟙 X := rfl

omit [IsOpenImmersion j] in
/-- The supported restriction ambient morphism is still the specified open immersion. -/
theorem restriction_right : (restriction j T).hom.hom.right = j := rfl

/-- Polynomial closure retains the actual composite of both row arrows. -/
theorem polynomial_row_comp :
    pairPolynomialFunctor.map (restriction j T ≫ enlargement j T) =
      pairPolynomialFunctor.map (restriction j T) ≫
        pairPolynomialFunctor.map (enlargement j T) :=
  pairPolynomialFunctor.map_comp _ _

/-- Laurent closure retains the actual composite of both row arrows. -/
theorem laurent_row_comp :
    pairLaurentFunctor.map (restriction j T ≫ enlargement j T) =
      pairLaurentFunctor.map (restriction j T) ≫
        pairLaurentFunctor.map (enlargement j T) :=
  pairLaurentFunctor.map_comp _ _

end Quillen.PerfectComplexes.GlobalSupportedRawBass.Rows
