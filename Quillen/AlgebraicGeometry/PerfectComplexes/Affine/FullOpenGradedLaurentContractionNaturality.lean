/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedLaurentContraction
public import Quillen.Waldhausen.SConstruction.Iterated.EndotransformationContractionNaturality

/-!
# Coefficient naturality of the same chosen graded Laurent contraction

The actual coefficient Model square and original forward-T transformation square specialize
whole naturality of the prescribed endotransformation contraction. Both original comparison
coordinates and all equality transports are retained. The actual endpoint-grade weak-zero
witnesses are proved, rather than supplied as additional geometric hypotheses.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

attribute [local irreducible] prespectrumEndotransformationContraction

/-- The actual diagram map has its unchanged prespectrum-map value. -/
private theorem original_prespectrum_map_apply {a b : Under R} (f : a ⟶ b) (n : ℕ)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x =
      (prespectrumMap ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map f)).map n x :=
  rfl

/-- The actual chosen contraction equals its literal accepted body at its original type. -/
private theorem original_contraction_eq (a : Under R) :
    boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a =
      (show
        (boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).RelHomotopy
          (LoopPrespectrum.Homotopy.refl
            ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
              ((laurentUnderCoefficient R).app a))) from
        prespectrumEndotransformationContraction
          ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
            ((laurentUnderCoefficient R).app a))
          (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a).hom
          (fun S ↦ (boundedFlatAffineFullOpenGradedSectionModel j
            ((laurentUnderFunctor R).obj a)).waldhausen.weq_iso _
            (NatIso.hom_app_isIso
              (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a) S))
          (boundedFlatAffineFullOpenGradedSectionLaurentZero_weak j a)) :=
  rfl

/-- Evaluating the checked literal whole equality keeps both original times and the point. -/
private theorem original_contraction_level_literal (a : Under R) (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).level n (r, (s, x)) =
      (show
        (boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).RelHomotopy
          (LoopPrespectrum.Homotopy.refl
            ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
              ((laurentUnderCoefficient R).app a))) from
        prespectrumEndotransformationContraction
          ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
            ((laurentUnderCoefficient R).app a))
          (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a).hom
          (fun S ↦ (boundedFlatAffineFullOpenGradedSectionModel j
            ((laurentUnderFunctor R).obj a)).waldhausen.weq_iso _
            (NatIso.hom_app_isIso
              (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a) S))
          (boundedFlatAffineFullOpenGradedSectionLaurentZero_weak j a)).level n (r, (s, x)) := by
  exact congrArg (fun J :
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).RelHomotopy
        (LoopPrespectrum.Homotopy.refl
          ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
            ((laurentUnderCoefficient R).app a))) ↦
      J.level n (r, (s, x))) (original_contraction_eq j a)

/-- The original coefficient equation typed with the literal accepted contraction bodies. -/
private theorem original_literal_contraction_naturality {a b : Under R} (f : a ⟶ b)
    (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    (prespectrumMap ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
        ((laurentUnderFunctor R).map f))).map n
      ((show
        (boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).RelHomotopy
          (LoopPrespectrum.Homotopy.refl
            ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
              ((laurentUnderCoefficient R).app a))) from
        prespectrumEndotransformationContraction
          ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
            ((laurentUnderCoefficient R).app a))
          (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a).hom
          (fun S ↦ (boundedFlatAffineFullOpenGradedSectionModel j
            ((laurentUnderFunctor R).obj a)).waldhausen.weq_iso _
            (NatIso.hom_app_isIso
              (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a) S))
          (boundedFlatAffineFullOpenGradedSectionLaurentZero_weak j a)).level n
        (r, (s, x))) =
      (show
        (boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j b).RelHomotopy
          (LoopPrespectrum.Homotopy.refl
            ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
              ((laurentUnderCoefficient R).app b))) from
        prespectrumEndotransformationContraction
          ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
            ((laurentUnderCoefficient R).app b))
          (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j b).hom
          (fun S ↦ (boundedFlatAffineFullOpenGradedSectionModel j
            ((laurentUnderFunctor R).obj b)).waldhausen.weq_iso _
            (NatIso.hom_app_isIso
              (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j b) S))
          (boundedFlatAffineFullOpenGradedSectionLaurentZero_weak j b)).level n
        (r, (s, (prespectrumMap
          ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map f)).map n x)) := by
  have he : Functor.whiskerRight
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a).hom
      ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
        ((laurentUnderFunctor R).map f)).functor =
      eqToHom (congrArg Model.Hom.functor
        (boundedFlatAffineFullOpenGradedSectionDiagramLaurentModelSquare j f)) ≫
      Functor.whiskerLeft ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map f).functor
        (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j b).hom ≫
      eqToHom (congrArg Model.Hom.functor
        (boundedFlatAffineFullOpenGradedSectionDiagramLaurentModelSquare j f).symm) := by
    apply (cancel_mono (eqToHom (congrArg Model.Hom.functor
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentModelSquare j f)))).1
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact boundedFlatAffineFullOpenGradedSectionDiagramLaurentModelUnitSquare j f
  have hraw := prespectrumEndotransformationContraction_naturality
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a))
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app b))
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map f)
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map ((laurentUnderFunctor R).map f))
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentModelSquare j f)
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a).hom
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j b).hom
    (fun S ↦ (boundedFlatAffineFullOpenGradedSectionModel j
      ((laurentUnderFunctor R).obj a)).waldhausen.weq_iso _
      (NatIso.hom_app_isIso
        (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a) S))
    (fun S ↦ (boundedFlatAffineFullOpenGradedSectionModel j
      ((laurentUnderFunctor R).obj b)).waldhausen.weq_iso _
      (NatIso.hom_app_isIso
        (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j b) S))
    (boundedFlatAffineFullOpenGradedSectionLaurentZero_weak j a)
    (boundedFlatAffineFullOpenGradedSectionLaurentZero_weak j b) he n r s x
  exact hraw

/-- Every coefficient map preserves the same chosen contraction at both independent times. -/
theorem boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
        ((laurentUnderFunctor R).map f)).map n
        ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).level n
          (r, (s, x))) =
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j b).level n
        (r, (s, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x)) := by
  refine (original_prespectrum_map_apply j ((laurentUnderFunctor R).map f) n _).trans ?_
  refine (congrArg
    ((prespectrumMap ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderFunctor R).map f))).map n)
    (original_contraction_level_literal j a n r s x)).trans ?_
  refine (original_literal_contraction_naturality j f n r s x).trans ?_
  refine (original_contraction_level_literal j b n r s
    ((prespectrumMap ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map f)).map n x)
      ).symm.trans ?_
  exact congrArg (fun y ↦
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j b).level n (r, (s, y)))
    (original_prespectrum_map_apply j f n x).symm

end Quillen.PerfectComplexes
