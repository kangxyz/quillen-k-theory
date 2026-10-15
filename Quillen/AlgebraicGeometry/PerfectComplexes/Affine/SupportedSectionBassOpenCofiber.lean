/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenBassDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassForgetTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenConeDiagram
public import Quillen.KTheory.Bass.ModelDiagramIterateCofiberPreservation

/-!
# Original supported-section cofiber comparisons at every finite Bass stage

The initial null track and cone stability are the genuine original supported-section results.
The existing Bass action iterates that same track. Transport through the original Under-to-ring
restriction isomorphism retains the already constructed support-forgetting arrow and gives the
matching relative-open arrow. Its actual cone descent is stable at every finite stage, with
no caller topology, connectivity or stability premise. The target remains the actual coarse
relative-open section Model. Original seed-relative and telescope compatibility remain separate.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The initial family is exactly the original reversed support-to-relative-open null track. -/
def boundedFlatAffineSupportedSectionOpenDiagramNull :
    DiagramNullHomotopy (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j)
      (boundedFlatAffineSectionOpenPrespectrumTransformation j) where
  homotopy a := boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a)
  naturality {a b} f := boundedFlatAffineSupportedSectionOpenNullHomotopy_coefficient
    (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f)

/-- The recursively specified actual Bass null family on the original Under-R iterated arrows. -/
def boundedFlatAffineSupportedSectionIterateOpenNull (n : ℕ) :=
  strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedFlatAffineSupportedSectionOpenDiagramNull j) n

/-- Initial geometric cone stability implies stability of the same original iterated descent. -/
theorem boundedFlatAffineSupportedSectionIterateOpenCone_isStableEquivalence
    (n : ℕ) (a : Under R) :
    IsStableEquivalence (mappingConeDesc
      (((strictDiagramIterate (laurentUnderSquareFunctor R) n).map
        (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j)).app a)
      (((strictDiagramIterate (laurentUnderSquareFunctor R) n).map
        (boundedFlatAffineSectionOpenPrespectrumTransformation j)).app a)
      ((boundedFlatAffineSupportedSectionIterateOpenNull j n).homotopy a)) :=
  modelDiagramIterateCofiberDesc_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedFlatAffineSupportedSectionModelFunctor j)
    (Under.forget R ⋙ boundedFlatAffineSectionModelFunctor)
    (boundedFlatAffineSectionOpenModelFunctor j)
    (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j)
    (boundedFlatAffineSectionOpenPrespectrumTransformation j)
    (boundedFlatAffineSupportedSectionOpenDiagramNull j)
    (fun a ↦ boundedFlatAffineSupportedSectionOpenConeMap_isStableEquivalence (inclusion j a)) n a

/-- Cancel the original ambient restriction from the unchanged support-forgetting arrow. -/
theorem boundedFlatAffineSupportedSectionBassForget_restriction (n : ℕ) :
    boundedFlatAffineSupportedSectionBassForget j n ≫
        (boundedFlatAffineSectionBassRestrictionIso R n).inv =
      (Iso.refl (boundedFlatAffineSupportedSectionBassDiagram j n)).hom ≫
        (strictDiagramIterate (laurentUnderSquareFunctor R) n).map
          (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j) := by
  have h := congrArg
    (fun f ↦ (strictDiagramIterate (laurentUnderSquareFunctor R) n).map
      (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j) ≫ f)
    (boundedFlatAffineSectionBassRestrictionIso R n).hom_inv_id
  exact (Category.assoc _ _ _).trans
    (h.trans ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- The matching original open arrow retains its exact inverse restriction transport. -/
theorem boundedFlatAffineSectionBassOpen_restriction (n : ℕ) :
    boundedFlatAffineSectionBassOpen j n ≫
        (Iso.refl (boundedFlatAffineSectionOpenBassDiagram j n)).hom =
      (boundedFlatAffineSectionBassRestrictionIso R n).inv ≫
        (strictDiagramIterate (laurentUnderSquareFunctor R) n).map
          (boundedFlatAffineSectionOpenPrespectrumTransformation j) := Category.comp_id _

/-- The same null values acquire the unchanged original ambient ring-stage middle endpoint. -/
def boundedFlatAffineSupportedSectionBassOpenNull (n : ℕ) :
    DiagramNullHomotopy (boundedFlatAffineSupportedSectionBassForget j n)
      (boundedFlatAffineSectionBassOpen j n) :=
  (boundedFlatAffineSupportedSectionIterateOpenNull j n).transport
    (Iso.refl (boundedFlatAffineSupportedSectionBassDiagram j n))
    (boundedFlatAffineSectionBassRestrictionIso R n).symm
    (Iso.refl (boundedFlatAffineSectionOpenBassDiagram j n))
    (boundedFlatAffineSupportedSectionBassForget_restriction j n)
    (boundedFlatAffineSectionBassOpen_restriction j n)

/-- The original Under restriction transport changes no value of the entire null family. -/
theorem boundedFlatAffineSupportedSectionBassOpenNull_level (n : ℕ) (a : Under R)
    (m : ℕ) (r : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j n).obj a).space m) :
    ((boundedFlatAffineSupportedSectionBassOpenNull j n).homotopy a).level m (r, x) =
      ((boundedFlatAffineSupportedSectionIterateOpenNull j n).homotopy a).level m (r, x) := rfl

/-- Descend from the cone of the unchanged original support-forgetting stage map. -/
def boundedFlatAffineSupportedSectionBassOpenConeMap (n : ℕ) :
    mappingConeDiagram (boundedFlatAffineSupportedSectionBassForget j n) ⟶
      boundedFlatAffineSectionOpenBassDiagram j n :=
  mappingConeDescTransformation (boundedFlatAffineSupportedSectionBassForget j n)
    (boundedFlatAffineSectionBassOpen j n)
    (boundedFlatAffineSupportedSectionBassOpenNull j n).homotopy
    (boundedFlatAffineSupportedSectionBassOpenNull j n).naturality

/-- The unchanged original ambient stage arrow is the actual target face of this cone descent. -/
theorem boundedFlatAffineSupportedSectionBassOpenConeMap_inclusion (n : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedFlatAffineSupportedSectionBassForget j n).app a) ≫
        (boundedFlatAffineSupportedSectionBassOpenConeMap j n).app a =
      (boundedFlatAffineSectionBassOpen j n).app a := mappingConeInclusion_desc _ _ _

/-- The original finite support cone comparison is stable, with all hypotheses discharged. -/
theorem boundedFlatAffineSupportedSectionBassOpenConeMap_isStableEquivalence
    (n : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedFlatAffineSupportedSectionBassOpenConeMap j n).app a) := by
  have h := (boundedFlatAffineSupportedSectionIterateOpenNull j n).transport_coneDesc
    (Iso.refl (boundedFlatAffineSupportedSectionBassDiagram j n))
    (boundedFlatAffineSectionBassRestrictionIso R n).symm
    (Iso.refl (boundedFlatAffineSectionOpenBassDiagram j n))
    (boundedFlatAffineSupportedSectionBassForget_restriction j n)
    (boundedFlatAffineSectionBassOpen_restriction j n) a
  apply (congrArg (fun f ↦ IsStableEquivalence f) h).mpr
  apply IsStableEquivalence.comp
  · intro d
    infer_instance
  · apply (boundedFlatAffineSupportedSectionIterateOpenCone_isStableEquivalence j n a).comp
    intro d
    change IsIso ((stableHomotopyFunctor d).map
      (𝟙 ((boundedFlatAffineSectionOpenBassDiagram j n).obj a)))
    infer_instance

end Quillen.PerfectComplexes
