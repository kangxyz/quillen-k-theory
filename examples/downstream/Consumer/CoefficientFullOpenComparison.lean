/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientFullOpenBassLocalization
public import Quillen.Topology.Prespectrum.StableLocalization

/-!
# Native global coefficient completion comparisons

The original global P/Q restriction and supported cone comparisons assemble into
isomorphisms of localized coefficient diagrams. Their inverses preserve arbitrary
original coefficient arrows. The fine cone comparison uses the constructed whole
null and its original signed boundary from the imported localization API.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PerfectComplexes
universe u
namespace Consumer.CoefficientFullOpenComparison
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The actual global coarse-to-fine completion is a coefficient-diagram isomorphism. -/
def completedRestrictionDiagramIso :
    boundedFlatCoefficientOpenBassTelescopeFunctor f ⋙ toStableLocalization ≅
      boundedFlatCoefficientFullOpenBassTelescopeFunctor f ⋙ toStableLocalization :=
  NatIso.ofComponents
    (fun a ↦ stableLocalizationIso
      ((boundedFlatCoefficientOpenBassTelescopeRestriction f).app a)
      (boundedFlatCoefficientOpenBassTelescopeRestriction_isStableEquivalence f a))
    (fun g ↦ by
      simpa only [stableLocalizationIso_hom, Functor.comp_map, Functor.map_comp] using
        congrArg toStableLocalization.map
          ((boundedFlatCoefficientOpenBassTelescopeRestriction f).naturality g))

/-- The inverse comparison preserves every original global coefficient arrow. -/
theorem completedRestrictionInverse_naturality {a b : Under R} (g : a ⟶ b) :
    toStableLocalization.map ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).map g) ≫
        (completedRestrictionDiagramIso f).inv.app b =
      (completedRestrictionDiagramIso f).inv.app a ≫
        toStableLocalization.map ((boundedFlatCoefficientOpenBassTelescopeFunctor f).map g) :=
  (completedRestrictionDiagramIso f).inv.naturality g

/-- The supported cone agrees with the fine full-open completion as a diagram. -/
def supportedFullOpenConeDiagramIso :
    mappingConeDiagram (boundedFlatCoefficientSupportedBassTelescopeForget f) ⋙
        toStableLocalization ≅
      boundedFlatCoefficientFullOpenBassTelescopeFunctor f ⋙ toStableLocalization :=
  NatIso.ofComponents
    (fun a ↦ stableLocalizationIso
      ((boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a)
      (boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence f a))
    (fun g ↦ by
      simpa only [stableLocalizationIso_hom, Functor.comp_map, Functor.map_comp] using
        congrArg toStableLocalization.map
          ((boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).naturality g))

/-- The inverse comparison preserves every original global coefficient arrow. -/
theorem supportedFullOpenConeInverse_naturality {a b : Under R} (g : a ⟶ b) :
    toStableLocalization.map ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).map g) ≫
        (supportedFullOpenConeDiagramIso f).inv.app b =
      (supportedFullOpenConeDiagramIso f).inv.app a ≫
        toStableLocalization.map
          ((mappingConeDiagram (boundedFlatCoefficientSupportedBassTelescopeForget f)).map g) :=
  (supportedFullOpenConeDiagramIso f).inv.naturality g

end Consumer.CoefficientFullOpenComparison
