/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Affine.OpenPairBaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionModel

/-!
# The actual supported section diagram over a fixed original affine open

Each algebra over R uses the one specified pullback of the original open j. Its original
coefficient arrows induce the exact supported Model maps already constructed. Their genuine
identity/composition laws and the literal fixed-endpoint pullback equations give a strict diagram.
The identity-algebra object is still its actual pullback; it has not been identified with j.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- For fixed original coefficient map, support witnesses do not change the actual Model arrow. -/
theorem boundedFlatAffineSupportedSectionModelMap_openMap_irrel
    {S : CommRingCat.{u}} {V : Scheme.{u}} (j' : V ⟶ Spec S) [IsOpenImmersion j']
    (f : R ⟶ S) (l l' : V ⟶ U)
    (h : l ≫ j = j' ≫ Spec.map f) (h' : l' ≫ j = j' ≫ Spec.map f) :
    boundedFlatAffineSupportedSectionModelMap j j' f l h =
      boundedFlatAffineSupportedSectionModelMap j j' f l' h' := by
  apply Model.Hom.ext
  rfl

/-- The original supported models on fixed pullbacks form a genuine coefficient diagram. -/
def boundedFlatAffineSupportedSectionModelFunctor : Under R ⥤ Model.{u+1} where
  obj a := boundedFlatAffineSupportedSectionModel (inclusion j a)
  map {a b} f := boundedFlatAffineSupportedSectionModelMap
    (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f)
  map_id a := by
    have h : 𝟙 (openSpace j a) ≫ inclusion j a =
        inclusion j a ≫ Spec.map (𝟙 a.right) := by simp
    exact (boundedFlatAffineSupportedSectionModelMap_openMap_irrel
      (inclusion j a) (inclusion j a) (𝟙 a.right) (openMap j (𝟙 a)) (𝟙 _)
      (openMap_inclusion j (𝟙 a)) h).trans
        (boundedFlatAffineSupportedSectionModelMap_id (inclusion j a) h)
  map_comp {a b c} f g := by
    have h : (openMap j g ≫ openMap j f) ≫ inclusion j a =
        inclusion j c ≫ Spec.map (f.right ≫ g.right) := by
      rw [← openMap_comp]
      exact openMap_inclusion j (f ≫ g)
    exact (boundedFlatAffineSupportedSectionModelMap_openMap_irrel
      (inclusion j a) (inclusion j c) (f.right ≫ g.right)
      (openMap j (f ≫ g)) (openMap j g ≫ openMap j f)
      (openMap_inclusion j (f ≫ g)) h).trans
        (boundedFlatAffineSupportedSectionModelMap_comp
          (inclusion j a) (inclusion j b) (inclusion j c) f.right g.right
          (openMap j f) (openMap j g) (openMap_inclusion j f) (openMap_inclusion j g) h)

/-- Apply the actual original iterated-S realization to the strict supported Model diagram. -/
def boundedFlatAffineSupportedSectionPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatAffineSupportedSectionModelFunctor j ⋙ prespectrumFunctor

/-- Every diagram arrow is the unchanged original supported coefficient prespectrum map. -/
theorem boundedFlatAffineSupportedSectionPrespectrumFunctor_map
    {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineSupportedSectionPrespectrumFunctor j).map f =
      boundedFlatAffineSupportedSectionPrespectrumMap
        (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f) := rfl

end Quillen.PerfectComplexes
