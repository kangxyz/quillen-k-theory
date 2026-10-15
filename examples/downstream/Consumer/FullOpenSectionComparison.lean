/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassRestrictionTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassLocalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenConeStable
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationNaturality
public import Quillen.Topology.Prespectrum.StableLocalization

/-!
# Original finite cones and completed full-open localization as coefficient diagrams

The original finite cone comparison becomes an isomorphism of coefficient diagrams.
Its inverse is natural for every original coefficient arrow, without any caller-supplied
null, image-exactness or stability input. The constructed telescope restriction and supported
cone comparison also give isomorphisms of the actual localized coefficient diagrams.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Consumer.FullOpenSectionComparison
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The actual original finite cone descents assemble into a localized coefficient isomorphism. -/
def originalFiniteConeDiagramIso (i : ℕ) :
    mappingConeDiagram (boundedFlatAffineSectionFullOpenBassRestriction j i) ⋙
        toStableLocalization ≅
      boundedFlatAffineFullOpenGradedSectionBassDiagram j i ⋙ toStableLocalization :=
  NatIso.ofComponents
    (fun a ↦ stableLocalizationIso
      ((boundedFlatAffineSectionFullOpenBassGradingConeMap j i).app a)
      (boundedFlatAffineSectionFullOpenBassGradingConeMap_isStableEquivalence j i a))
    (fun f ↦ by
      simpa only [stableLocalizationIso_hom, Functor.comp_map, Functor.map_comp] using
        congrArg toStableLocalization.map
          ((boundedFlatAffineSectionFullOpenBassGradingConeMap j i).naturality f))

/-- Inverting the actual comparison preserves every original coefficient square. -/
theorem originalFiniteConeInverse_naturality (i : ℕ) {a b : Under R} (f : a ⟶ b) :
    (toStableLocalization.map
        ((boundedFlatAffineFullOpenGradedSectionBassDiagram j i).map f)) ≫
        (originalFiniteConeDiagramIso j i).inv.app b =
      (originalFiniteConeDiagramIso j i).inv.app a ≫
        toStableLocalization.map
          ((mappingConeDiagram (boundedFlatAffineSectionFullOpenBassRestriction j i)).map f) :=
  (originalFiniteConeDiagramIso j i).inv.naturality f

/-- The unchanged coarse-to-fine completed restriction is an actual coefficient-diagram iso. -/
def originalCompletedRestrictionDiagramIso :
    boundedFlatAffineSectionOpenBassTelescopeFunctor j ⋙ toStableLocalization ≅
      boundedFlatAffineFullOpenSectionBassTelescopeFunctor j ⋙ toStableLocalization :=
  NatIso.ofComponents
    (fun a ↦ stableLocalizationIso
      ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).app a)
      (boundedFlatAffineSectionFullOpenBassTelescopeRestriction_isStableEquivalence j a))
    (fun f ↦ by
      simpa only [stableLocalizationIso_hom, Functor.comp_map, Functor.map_comp] using
        congrArg toStableLocalization.map
          ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).naturality f))

/-- The inverse completed comparison keeps arbitrary original coefficient arrows. -/
theorem originalCompletedRestrictionInverse_naturality {a b : Under R} (f : a ⟶ b) :
    toStableLocalization.map
        ((boundedFlatAffineFullOpenSectionBassTelescopeFunctor j).map f) ≫
      (originalCompletedRestrictionDiagramIso j).inv.app b =
    (originalCompletedRestrictionDiagramIso j).inv.app a ≫
      toStableLocalization.map ((boundedFlatAffineSectionOpenBassTelescopeFunctor j).map f) :=
  (originalCompletedRestrictionDiagramIso j).inv.naturality f

/-- The actual supported cone compares to the fine completion with no supplied null premise. -/
def originalSupportedCompletedConeDiagramIso :
    mappingConeDiagram (boundedFlatAffineSupportedSectionBassTelescopeForget j) ⋙
        toStableLocalization ≅
      boundedFlatAffineFullOpenSectionBassTelescopeFunctor j ⋙ toStableLocalization :=
  NatIso.ofComponents
    (fun a ↦ stableLocalizationIso
      ((boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap j).app a)
      (boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap_isStableEquivalence j a))
    (fun f ↦ by
      simpa only [stableLocalizationIso_hom, Functor.comp_map, Functor.map_comp] using
        congrArg toStableLocalization.map
          ((boundedFlatAffineSupportedSectionBassTelescopeFullOpenConeMap j).naturality f))

end Consumer.FullOpenSectionComparison

namespace Consumer.NativeGlobalSectionComparison
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- Native global canonical cone descents give a coefficient-diagram iso without extra inputs. -/
def originalNativeConeDiagramIso :
    mappingConeDiagram (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f) ⋙
        toStableLocalization ≅
      boundedFlatCoefficientGradedOpenPrespectrumFunctor f ⋙ toStableLocalization :=
  NatIso.ofComponents
    (fun a ↦ stableLocalizationIso
      ((boundedFlatCoefficientOpenConeComparisonTransformation f).app a)
      (boundedFlatCoefficientOpenConeComparison_isStableEquivalence f a))
    (fun {a b} g ↦ by
      change toStableLocalization.map
          ((mappingConeDiagram
            (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f)).map g) ≫
          toStableLocalization.map
            ((boundedFlatCoefficientOpenConeComparisonTransformation f).app b) =
        toStableLocalization.map
            ((boundedFlatCoefficientOpenConeComparisonTransformation f).app a) ≫
          toStableLocalization.map ((boundedFlatCoefficientGradedOpenPrespectrumFunctor f).map g)
      simpa only [Functor.map_comp] using
        congrArg toStableLocalization.map
          ((boundedFlatCoefficientOpenConeComparisonTransformation f).naturality g))

/-- The inverse global comparison preserves every actual coefficient arrow. -/
theorem originalNativeConeInverse_naturality {a b : Under R} (g : a ⟶ b) :
    toStableLocalization.map ((boundedFlatCoefficientGradedOpenPrespectrumFunctor f).map g) ≫
        (originalNativeConeDiagramIso f).inv.app b =
      (originalNativeConeDiagramIso f).inv.app a ≫
        toStableLocalization.map
          ((mappingConeDiagram
            (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f)).map g) :=
  (originalNativeConeDiagramIso f).inv.naturality g

end Consumer.NativeGlobalSectionComparison

namespace Consumer.NativeCoefficientEvaluation
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]

/-- Inverting actual native perfect evaluation preserves arbitrary original coefficient maps. -/
theorem perfectEvaluationInverse_naturality {a b : Under R} (g : a ⟶ b) :
    (boundedFlatCoefficientPerfectLocalizedSpectrumFunctor P).map g ≫
        (boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P).inv.app b =
      (boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P).inv.app a ≫
        ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.row P) ⋙
          boundedFlatCoefficientSectionLocalizedSpectrumFunctor R).map g :=
  (boundedFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P).inv.naturality g

end Consumer.NativeCoefficientEvaluation
