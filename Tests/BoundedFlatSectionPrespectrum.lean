/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionPrespectrum

/-!
# Consumers of the actual strict section prespectrum diagram

The strict spectrum maps retain original coefficient restrictions, literal composition and the
actual original K-map under the zero-space comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.Waldhausen
open scoped unitInterval
universe u
namespace Quillen.Tests.BoundedFlatSectionPrespectrum

/-- The model map retains the original coefficient restriction functor. -/
theorem original_coefficient_functor {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatAffineSectionModelMap f).functor = boundedFlatAffineSectionsMap f := rfl

/-- The complete actual spectrum map has literal identity preservation. -/
theorem actual_identity (R : CommRingCat.{u}) :
    boundedFlatAffineSectionPrespectrumFunctor.map (𝟙 R) =
      𝟙 (boundedFlatAffineSectionPrespectrumFunctor.obj R) :=
  boundedFlatAffineSectionPrespectrumFunctor.map_id R

/-- Two independent coefficient maps compose literally on the actual prespectra. -/
theorem actual_composition {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    boundedFlatAffineSectionPrespectrumFunctor.map (f ≫ g) =
      boundedFlatAffineSectionPrespectrumFunctor.map f ≫
        boundedFlatAffineSectionPrespectrumFunctor.map g :=
  boundedFlatAffineSectionPrespectrumFunctor.map_comp f g

/-- Every structure coordinate retains its actual independent loop parameter. -/
theorem original_structure_time {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) (t : unitInterval) :
    (boundedFlatAffineSectionPrespectrumFunctor.map f).map (n+1)
        ((boundedFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t) =
      (boundedFlatAffineSectionPrespectrumFunctor.obj S).structureMap n
        ((boundedFlatAffineSectionPrespectrumFunctor.map f).map n x) t :=
  congrArg (fun p => p t) ((boundedFlatAffineSectionPrespectrumFunctor.map f).comm n x)

/-- An arbitrary original section K-class maps through the unchanged exact coefficient K-map. -/
theorem original_coefficient_kmap {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (a : (boundedFlatAffineSectionWaldhausen R).K n) :
    boundedFlatAffineSectionZeroSpaceEquiv S n
        (KMap (boundedFlatAffineSectionsMap_exact f) n a) =
      homotopyGroupMap ((boundedFlatAffineSectionPrespectrumFunctor.map f).map 0)
        ((boundedFlatAffineSectionPrespectrumFunctor.map f).map_point 0)
        (boundedFlatAffineSectionZeroSpaceEquiv R n a) :=
  boundedFlatAffineSectionZeroSpaceEquiv_naturality f n a

end Quillen.Tests.BoundedFlatSectionPrespectrum
