/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SquareConeStable
public import Quillen.Topology.Prespectrum.StableLocalization

/-!
# The actual cone strength gives a natural stable-localized equivalence

Both the literal forward map and the inverse coefficient square are retained.
This is a finite Model-stage comparison, with no seed or telescope assertion.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass
open SquareConeStrength SquareConeStable
universe u v w
namespace QuillenTest.SquareConeStable
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (i : ℕ) (M : Arrow (Arrow (C ⥤ Model.{w})))

/-- The actual finite-stage chi, localized objectwise, is a natural isomorphism. -/
def localizedChi :
    mappingConeDiagram (comparison (bassSquare (modelSquare Q i M) Q)) ⋙
        toStableLocalization ≅
      (strictDiagramFunctor Q).obj (mappingConeDiagram (comparison (modelSquare Q i M))) ⋙
        toStableLocalization :=
  NatIso.ofComponents
    (fun X => stableLocalizationIso ((chi (modelSquare Q i M) Q).app X)
      (modelSquare_chi_isStableEquivalence Q i M X))
    (fun k => (CategoryTheory.Functor.whiskerRight (chi (modelSquare Q i M) Q)
      toStableLocalization).naturality k)

/-- Its forward map remains the original two positive-direction cone maps. -/
theorem localizedChi_hom_app (X : C) :
    (localizedChi Q i M).hom.app X =
      toStableLocalization.map ((chi (modelSquare Q i M) Q).app X) := rfl

/-- The inverse is natural for the original coefficient maps on both sides. -/
theorem localizedChi_inverse_naturality {X Y : C} (k : X ⟶ Y) :
    toStableLocalization.map (((strictDiagramFunctor Q).obj
      (mappingConeDiagram (comparison (modelSquare Q i M)))).map k) ≫
        (localizedChi Q i M).inv.app Y =
      (localizedChi Q i M).inv.app X ≫
        toStableLocalization.map
          ((mappingConeDiagram (comparison (bassSquare (modelSquare Q i M) Q))).map k) :=
  (localizedChi Q i M).inv.naturality k

#print axioms Quillen.KTheory.Bass.SquareConeStable.modelSquare_chi_isStableEquivalence
#print axioms localizedChi
#print axioms localizedChi_inverse_naturality

end QuillenTest.SquareConeStable
