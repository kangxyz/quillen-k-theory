/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionImageMap

/-!
# The original full-open coefficient diagram with its actual quotient grading

The proved original quotient action makes the unchanged section reindexing exact for
grade-equality weaknesses. The same inherited zero and literal coefficient identity and
composition laws give a genuine strict Model diagram and its original iterated-S diagram.
The change from fine to graded weakness is an actual natural transformation of those diagrams.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.CategoryTheory.StrictSections Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The actual coefficient functor preserves the genuine original quotient-grade weaknesses. -/
theorem boundedFlatAffineFullOpenGradedSectionsMap_exact {a b : Under R} (f : a ⟶ b) :
    IsExact (boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.cof
      (boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.weq
      (boundedFlatAffineFullOpenSectionGrading j b).coarseStructure.cof
      (boundedFlatAffineFullOpenSectionGrading j b).coarseStructure.weq
      (boundedFlatAffineFullOpenSectionsMap j f) where
  zero := (boundedFlatAffineFullOpenSectionsMap_exact j f).zero
  cofibration := (boundedFlatAffineFullOpenSectionsMap_exact j f).cofibration
  weak {S T} _ h :=
    (boundedFlatAffineFullOpenSectionImageMap_value j f S).symm.trans
      ((congrArg (boundedFlatAffineFullOpenSectionImageMap j f) h).trans
        (boundedFlatAffineFullOpenSectionImageMap_value j f T))
  pushout := (boundedFlatAffineFullOpenSectionsMap_exact j f).pushout

/-- The original reindexing map retains the inherited global zero literally. -/
def boundedFlatAffineFullOpenGradedSectionModelMap {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineFullOpenGradedSectionModel j a ⟶
      boundedFlatAffineFullOpenGradedSectionModel j b where
  functor := boundedFlatAffineFullOpenSectionsMap j f
  exact := boundedFlatAffineFullOpenGradedSectionsMap_exact j f
  zero := boundedFlatAffineFullOpenSectionsMap_sectionZero j f

/-- The original identity coefficient yields the identity of the same graded Model. -/
theorem boundedFlatAffineFullOpenGradedSectionModelMap_id (a : Under R) :
    boundedFlatAffineFullOpenGradedSectionModelMap j (𝟙 a) =
      𝟙 (boundedFlatAffineFullOpenGradedSectionModel j a) := by
  apply Model.Hom.ext
  exact underCocartesianReindex_id (boundedFlatAffineFullOpenProjection j) a

/-- The unchanged coefficient functors compose literally in the graded Model category. -/
theorem boundedFlatAffineFullOpenGradedSectionModelMap_comp {a b c : Under R}
    (f : a ⟶ b) (g : b ⟶ c) :
    boundedFlatAffineFullOpenGradedSectionModelMap j (f ≫ g) =
      boundedFlatAffineFullOpenGradedSectionModelMap j f ≫
        boundedFlatAffineFullOpenGradedSectionModelMap j g := by
  apply Model.Hom.ext
  exact underCocartesianReindex_comp (boundedFlatAffineFullOpenProjection j) f g

/-- Actual full-open graded Models with all original coefficient maps and strict laws. -/
def boundedFlatAffineFullOpenGradedSectionModelFunctor : Under R ⥤ Model.{u+1} where
  obj := boundedFlatAffineFullOpenGradedSectionModel j
  map := boundedFlatAffineFullOpenGradedSectionModelMap j
  map_id := boundedFlatAffineFullOpenGradedSectionModelMap_id j
  map_comp := boundedFlatAffineFullOpenGradedSectionModelMap_comp j

/-- The same actual iterated-S construction gives the strict graded prespectrum diagram. -/
def boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatAffineFullOpenGradedSectionModelFunctor j ⋙ prespectrumFunctor

/-- The actual identity functor changes only the original weakness class. -/
def boundedFlatAffineFullOpenSectionGradingModelMap (a : Under R) :
    boundedFlatAffineFullOpenSectionModel j a ⟶
      boundedFlatAffineFullOpenGradedSectionModel j a where
  functor := 𝟭 (BoundedFlatAffineFullOpenSections j a)
  exact := Fibration.changeWeak_exact (boundedFlatAffineFullOpenSectionGrading j a).nested
  zero := rfl

/-- The original fine-to-grade maps commute with every unchanged coefficient functor. -/
def boundedFlatAffineFullOpenSectionGradingModelTransformation :
    boundedFlatAffineFullOpenSectionModelFunctor j ⟶
      boundedFlatAffineFullOpenGradedSectionModelFunctor j where
  app := boundedFlatAffineFullOpenSectionGradingModelMap j
  naturality a b f := by
    apply Model.Hom.ext
    change boundedFlatAffineFullOpenSectionsMap j f ⋙ 𝟭 _ =
      𝟭 _ ⋙ boundedFlatAffineFullOpenSectionsMap j f
    simp only [Functor.id_comp, Functor.comp_id]

end Quillen.PerfectComplexes
