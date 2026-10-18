/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.PushoutStable
public import Quillen.Topology.Prespectrum.StableLocalization

/-!
# The original forward comparison gives a natural localized equivalence

The forward components remain the literal quotient maps. The inverse then has
coefficient naturality as an actual natural isomorphism, rather than separately
chosen inverses on stable homotopy groups. Adopted independent reconstruction.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass
open PushoutStrength PushoutStable
universe u v w
namespace QuillenTest.BassPushoutStable
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (i : ℕ) (M₀ M₁ M₂ : C ⥤ Model.{w})
  (f : (strictDiagramIterate Q i).obj (M₀ ⋙ prespectrumFunctor) ⟶
    (strictDiagramIterate Q i).obj (M₁ ⋙ prespectrumFunctor))
  (g : (strictDiagramIterate Q i).obj (M₀ ⋙ prespectrumFunctor) ⟶
    (strictDiagramIterate Q i).obj (M₂ ⋙ prespectrumFunctor))

/-- The original comparison, localized objectwise, is naturally invertible. -/
def localizedComparison :
    pushout ((strictDiagramFunctor Q).map f) ((strictDiagramFunctor Q).map g) ⋙
        toStableLocalization ≅
      (strictDiagramFunctor Q).obj (pushout f g) ⋙ toStableLocalization :=
  NatIso.ofComponents
    (fun X => stableLocalizationIso (comparison f g Q X)
      (modelIterate_comparison_isStableEquivalence Q i M₀ M₁ M₂ f g X))
    (fun k => (CategoryTheory.Functor.whiskerRight (rho f g Q)
      toStableLocalization).naturality k)

/-- Localization preserves the literal forward component. -/
theorem localizedComparison_hom_app (X : C) :
    (localizedComparison Q i M₀ M₁ M₂ f g).hom.app X =
      toStableLocalization.map (comparison f g Q X) := rfl

/-- The inverse commutes with all original coefficient maps. -/
theorem localizedComparison_inverse_naturality {X Y : C} (k : X ⟶ Y) :
    toStableLocalization.map (((strictDiagramFunctor Q).obj (pushout f g)).map k) ≫
        (localizedComparison Q i M₀ M₁ M₂ f g).inv.app Y =
      (localizedComparison Q i M₀ M₁ M₂ f g).inv.app X ≫
        toStableLocalization.map ((pushout ((strictDiagramFunctor Q).map f)
          ((strictDiagramFunctor Q).map g)).map k) :=
  (localizedComparison Q i M₀ M₁ M₂ f g).inv.naturality k

end QuillenTest.BassPushoutStable

#print axioms
  Quillen.KTheory.Bass.PushoutCofiberSquare.coneSquare
#print axioms
  Quillen.KTheory.Bass.PushoutStable.comparison_isStableEquivalence_of_linearGrowth
#print axioms
  Quillen.KTheory.Bass.PushoutStable.modelIterate_comparison_isStableEquivalence
#print axioms QuillenTest.BassPushoutStable.localizedComparison
