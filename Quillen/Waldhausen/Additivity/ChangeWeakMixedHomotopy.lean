/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Additivity.ChangeWeakDeformation
public import Quillen.Waldhausen.Additivity.NormalizedMixedHomotopy
public import Quillen.Topology.Realization.HomotopyNaturality

/-!
# The original mixed additivity track under fine-to-coarse comparison

The actual cylinder equation descends to the unchanged realization homotopy at every point
and time. This treats the mixed part of the based additivity pasting; its two endpoint
homotopies and the final localization-boundary comparison are separate obligations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Quillen.MixedOrdinalCylinder
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (N : Fibration.NestedWeakEquivalences W)
  {F G : C ⥤ D} (a : F ⟶ G)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hc : IsCofibrationTransformation W a V)

/-- Fine-to-coarse comparison preserves the exact original mixed simplicial cylinder. -/
theorem normalizedMixedEndpointHomotopy_changeWeak :
    (normalizedMixedEndpointHomotopy V W a hF hG hc).h ≫
        TheoremA.diagonalMap
          (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)) =
      (normalizedMixedEndpointHomotopy V N.coarse a
        (hF.comp (Fibration.changeWeak_exact N))
        (hG.comp (Fibration.changeWeak_exact N))
        (isCofibrationTransformation_changeWeak V W N a hc)).h := by
  have h := congrArg (fun k =>
    TheoremA.diagonalMap (outerOneSection (bisimplicialSSet V)) ▷ Δ[1] ≫
      (outerContraction (bisimplicialSSet V)).h ≫ TheoremA.diagonalMap k)
    (normalizedMixedMap_changeWeak V W N a hF hG hc)
  have hd := TheoremA.diagonalFunctor.map_comp (normalizedMixedMap V W a hF hG hc)
    (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N))
  change TheoremA.diagonalMap (_ ≫ _) =
    TheoremA.diagonalMap _ ≫ TheoremA.diagonalMap _ at hd
  rw [hd] at h
  simpa only [normalizedMixedEndpointHomotopy, mixedEndpointHomotopy,
    Category.assoc] using h

/-- Both original realization parameters survive the actual fine-to-coarse comparison. -/
theorem normalizedMixedRealizationHomotopy_changeWeak (t : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    SSet.toTop.map (TheoremA.diagonalMap
      (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
        (realizationSimplicialHomotopy
          (normalizedMixedEndpointHomotopy V W a hF hG hc) (t, x)) =
      realizationSimplicialHomotopy
        (normalizedMixedEndpointHomotopy V N.coarse a
          (hF.comp (Fibration.changeWeak_exact N))
          (hG.comp (Fibration.changeWeak_exact N))
          (isCofibrationTransformation_changeWeak V W N a hc)) (t, x) := by
  simpa using realizationSimplicialHomotopy_naturality
    (normalizedMixedEndpointHomotopy V W a hF hG hc)
    (normalizedMixedEndpointHomotopy V N.coarse a
      (hF.comp (Fibration.changeWeak_exact N))
      (hG.comp (Fibration.changeWeak_exact N))
      (isCofibrationTransformation_changeWeak V W N a hc))
    (𝟙 _) (TheoremA.diagonalMap
      (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
    (by simpa using normalizedMixedEndpointHomotopy_changeWeak V W N a hF hG hc) t x

end Quillen.Waldhausen.Additivity
