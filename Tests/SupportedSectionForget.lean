/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionForgetLaurent

/-!
# Consumers of the original exact supported inclusion

The original section arrows, chosen zero, all four pushout edges, arbitrary open-pair square,
fixed-pullback coefficient diagram and whole Laurent action retain their actual parameters.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.Scheme.AffineOpenPair Quillen.PolynomialBaseChange
universe u
namespace Quillen.Tests.SupportedSectionForget
open PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The genuine original supported cofibration is unchanged as an ambient section map. -/
theorem original_inclusion_cofibration {X Y : BoundedFlatAffineSupportedSections j}
    (a : X ⟶ Y) (ha : (boundedFlatAffineSupportedSectionWaldhausen j).cof a) :
    (boundedFlatAffineSectionWaldhausen R).cof a.hom :=
  (boundedFlatAffineSupportedSectionForget_exact j).cofibration a ha

/-- The same original underlying section arrow is weak after support is forgotten. -/
theorem original_inclusion_weak {X Y : BoundedFlatAffineSupportedSections j}
    (a : X ⟶ Y) (ha : (boundedFlatAffineSupportedSectionWaldhausen j).weq a) :
    (boundedFlatAffineSectionWaldhausen R).weq a.hom :=
  (boundedFlatAffineSupportedSectionForget_exact j).weak a ha

/-- All four original section maps remain the actual pushout square. -/
theorem original_inclusion_pushout {A B C D : BoundedFlatAffineSupportedSections j}
    {i : A ⟶ B} {a : A ⟶ C} {b : B ⟶ D} {k : C ⟶ D}
    (hi : (boundedFlatAffineSupportedSectionWaldhausen j).cof i) (hp : IsPushout i a b k) :
    IsPushout i.hom a.hom b.hom k.hom :=
  (boundedFlatAffineSupportedSectionForget_exact j).pushout hi hp

/-- The original Model arrow is the literal support inclusion on every section and every map. -/
theorem original_model_functor :
    (boundedFlatAffineSupportedSectionForgetModelMap j).functor =
      (boundedFlatAffineSectionSupported j).ι := rfl

/-- The actual chosen section zero agrees literally, with no geometric zero identification. -/
theorem original_model_zero :
    (boundedFlatAffineSupportedSectionForgetModelMap j).functor.obj
        (boundedFlatAffineSupportedSectionZero j) = boundedFlatAffineSectionZero R :=
  (boundedFlatAffineSupportedSectionForgetModelMap j).zero

/-- The exact inclusion square keeps an arbitrary original open-pair coefficient square. -/
theorem original_coefficient_square (j' : V ⟶ Spec S) [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    boundedFlatAffineSupportedSectionModelMap j j' f l h ≫
        boundedFlatAffineSupportedSectionForgetModelMap j' =
      boundedFlatAffineSupportedSectionForgetModelMap j ≫ boundedFlatAffineSectionModelMap f :=
  boundedFlatAffineSupportedSectionForgetModelMap_naturality j j' f l h

/-- The actual strict natural transformation retains the original fixed-pullback inclusion. -/
theorem original_diagram_component (a : Under R) :
    ((boundedFlatAffineSupportedSectionForgetModelTransformation j).app a).functor =
      (boundedFlatAffineSectionSupported (inclusion j a)).ι := rfl

/-- The original inclusion commutes with the entire structure path at its unchanged time. -/
theorem original_structure_time (n : ℕ) (t : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionForgetPrespectrumMap j).map (n + 1)
        ((prespectrum (boundedFlatAffineSupportedSectionModel j)).structureMap n x t) =
      (prespectrum (boundedFlatAffineSectionModel R)).structureMap n
        ((boundedFlatAffineSupportedSectionForgetPrespectrumMap j).map n x) t :=
  congrArg (fun p ↦ p t) ((boundedFlatAffineSupportedSectionForgetPrespectrumMap j).comm n x)

/-- Every original Laurent action value survives inclusion, including the original loop level. -/
theorem original_laurent_whole_track (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineSupportedSectionForgetPrespectrumMap
        (inclusion j ((laurentUnderFunctor R).obj a))).map n
        ((boundedFlatAffineSupportedDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedFlatAffineSectionLaurentUnitHomotopy a.right).level n
        (t, (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a)).map n x) :=
  boundedFlatAffineSupportedDiagramLaurentHomotopy_forget_apply j a n t x

end Quillen.Tests.SupportedSectionForget
