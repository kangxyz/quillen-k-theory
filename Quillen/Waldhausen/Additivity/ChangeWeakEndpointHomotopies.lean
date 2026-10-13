/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.ChangeWeakDeformation
public import Quillen.Waldhausen.Additivity.NormalizedEndpointHomotopies
public import Quillen.Topology.Realization.HomotopyNaturality

/-!
# Original additivity endpoint tracks under weak enlargement

The same structural cofibration sequence and original normalization isomorphisms give the
literal fine-to-coarse squares for both endpoint cylinders.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (N : Fibration.NestedWeakEquivalences W)
  {F G H : C ⥤ D} (a : F ⟶ G)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hc : IsCofibrationTransformation W a V)

/-- The identity-endpoint cylinder retains the actual normalization and comparison maps. -/
theorem normalizedIdentityEndpointHomotopy_changeWeak :
    (normalizedIdentityEndpointHomotopy V W a hF hG hc).h ≫
        TheoremA.diagonalMap
          (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)) =
      (normalizedIdentityEndpointHomotopy V N.coarse a
        (hF.comp (Fibration.changeWeak_exact N))
        (hG.comp (Fibration.changeWeak_exact N))
        (isCofibrationTransformation_changeWeak V W N a hc)).h := by
  cases W
  rcases N with ⟨coarse, hcof, hzero, hw⟩
  cases coarse
  cases hzero
  rfl

/-- The original realized identity-endpoint track commutes at every time and point. -/
theorem normalizedIdentityEndpointRealizationHomotopy_changeWeak (t : unitInterval)
    (x : |TheoremA.diagonalSSet (bisimplicialSSet V)|) :
    SSet.toTop.map (TheoremA.diagonalMap
      (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
        (normalizedIdentityEndpointRealizationHomotopy V W a hF hG hc (t, x)) =
      normalizedIdentityEndpointRealizationHomotopy V N.coarse a
        (hF.comp (Fibration.changeWeak_exact N))
        (hG.comp (Fibration.changeWeak_exact N))
        (isCofibrationTransformation_changeWeak V W N a hc) (t, x) := by
  simpa only [normalizedIdentityEndpointRealizationHomotopy,
    CategoryTheory.Functor.map_id, TopCat.id_app] using
    realizationSimplicialHomotopy_naturality
      (normalizedIdentityEndpointHomotopy V W a hF hG hc)
      (normalizedIdentityEndpointHomotopy V N.coarse a
        (hF.comp (Fibration.changeWeak_exact N))
        (hG.comp (Fibration.changeWeak_exact N))
        (isCofibrationTransformation_changeWeak V W N a hc))
      (𝟙 _) (TheoremA.diagonalMap
        (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
      (by simpa using normalizedIdentityEndpointHomotopy_changeWeak V W N a hF hG hc) t x

variable (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

include hs in
/-- The unchanged actual cofiber squares give a cofibration sequence in the coarse structure. -/
theorem isCofibrationSequence_changeWeak : IsCofibrationSequence V N.coarse a b where
  exactF := hs.exactF.comp (Fibration.changeWeak_exact N)
  exactG := hs.exactG.comp (Fibration.changeWeak_exact N)
  exactH := hs.exactH.comp (Fibration.changeWeak_exact N)
  cofibration := isCofibrationTransformation_changeWeak V W N a hs.cofibration
  cofiber X := by
    have h := hs.cofiber X
    cases W
    rcases N with ⟨coarse, hcof, hzero, hw⟩
    cases coarse
    cases hzero
    exact h

variable [HasBinaryCoproducts D]

/-- The separated endpoint keeps the original cofiber and normalized split comparison. -/
theorem normalizedSeparatedEndpointHomotopy_changeWeak :
    (normalizedSeparatedEndpointHomotopy V W a b hs).h ≫
        TheoremA.diagonalMap
          (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)) =
      (normalizedSeparatedEndpointHomotopy V N.coarse a b
        (isCofibrationSequence_changeWeak V W N a b hs)).h := by
  cases W
  rcases N with ⟨coarse, hcof, hzero, hw⟩
  cases coarse
  cases hzero
  rfl

/-- Every point of the original separated realization track is preserved. -/
theorem normalizedSeparatedEndpointRealizationHomotopy_changeWeak (t : unitInterval)
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    SSet.toTop.map (TheoremA.diagonalMap
      (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
        (normalizedSeparatedEndpointRealizationHomotopy V W a b hs (t, x)) =
      normalizedSeparatedEndpointRealizationHomotopy V N.coarse a b
        (isCofibrationSequence_changeWeak V W N a b hs) (t, x) := by
  simpa only [normalizedSeparatedEndpointRealizationHomotopy,
    CategoryTheory.Functor.map_id, TopCat.id_app] using
    realizationSimplicialHomotopy_naturality
      (normalizedSeparatedEndpointHomotopy V W a b hs)
      (normalizedSeparatedEndpointHomotopy V N.coarse a b
        (isCofibrationSequence_changeWeak V W N a b hs))
      (𝟙 _) (TheoremA.diagonalMap
        (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
      (by simpa using normalizedSeparatedEndpointHomotopy_changeWeak V W N a b hs) t x

end Quillen.Waldhausen.Additivity
