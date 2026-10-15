/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionCoefficientComposition

/-! Original split composition, coefficient tracks, loop time and structure time are retained. -/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped unitInterval
universe u
namespace QuillenTest.SectionCoefficientComposition

open Quillen

/-- The first face contains the unchanged split geometric composition homotopy. -/
theorem first_face {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (n : ℕ) (s : unitInterval) (x : (prespectrum (boundedFlatAffineSectionModel R)).space n) :
    (boundedFlatAffineSectionCoefficientCompositionRelHomotopy f g).level n (0, (s, x)) =
      ((boundedFlatAffineSectionEvaluationCoefficientHomotopy (f ≫ g)).trans
        (Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
          ((boundedFlatPerfectPrespectrumCompHomotopy (Spec.map g) (Spec.map f)).cast
            (congrArg boundedFlatPerfectPrespectrumMap (Spec.map_comp f g).symm) rfl))).level n
          (s, x) :=
  ((boundedFlatAffineSectionCoefficientCompositionRelHomotopy f g).level n).apply_zero _

/-- The other face is the actual prewhiskered/postwhiskered coefficient route. -/
theorem second_face {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (n : ℕ) (s : unitInterval) (x : (prespectrum (boundedFlatAffineSectionModel R)).space n) :
    (boundedFlatAffineSectionCoefficientCompositionRelHomotopy f g).level n (1, (s, x)) =
      (((Homotopy.precomp (boundedFlatAffineSectionPrespectrumFunctor.map f)
        (boundedFlatAffineSectionEvaluationCoefficientHomotopy g)).cast
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ boundedFlatAffineSectionEvaluationPrespectrumMap T)
              (boundedFlatAffineSectionPrespectrumFunctor.map_comp f g).symm))
          (Category.assoc _ _ _).symm).trans
        ((boundedFlatAffineSectionEvaluationCoefficientHomotopy f).postcomp
          (boundedFlatPerfectPrespectrumMap (Spec.map g)))).level n (s, x) :=
  ((boundedFlatAffineSectionCoefficientCompositionRelHomotopy f g).level n).apply_one _

/-- Relative comparison time and the original degree-zero loop time are independent. -/
theorem loop_boundary {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (r q : unitInterval) (γ : (prespectrum (boundedFlatAffineSectionModel R)).space 0) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T))))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T)))) from
      (boundedFlatAffineSectionCoefficientCompositionRelHomotopy f g).level 0
        (r, (0, γ))) q =
      (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T))))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T)))) from
        (boundedFlatAffineSectionPrespectrumFunctor.map (f ≫ g) ≫
          boundedFlatAffineSectionEvaluationPrespectrumMap T).map 0 γ) q := by
  have h := ((boundedFlatAffineSectionCoefficientCompositionRelHomotopy f g).level 0).eq_fst
    r (x := (0, γ)) (Or.inl rfl)
  exact congrArg (fun p : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (Spec T)))).space 0 =>
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T)))) from p) q)
    (h.trans ((boundedFlatAffineSectionCoefficientSplitRoute f g).at_zero 0 γ))

/-- Comparison, path and spectrum structure times remain separate in the original diagram. -/
theorem three_times {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (n : ℕ) (r s t : unitInterval) (x : (prespectrum (boundedFlatAffineSectionModel R)).space n) :
    (boundedFlatAffineSectionCoefficientCompositionRelHomotopy f g).level (n + 1)
      (r, (s, (prespectrum (boundedFlatAffineSectionModel R)).structureMap n x t)) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen (Spec T)))).structureMap n
      ((boundedFlatAffineSectionCoefficientCompositionRelHomotopy f g).level n (r, (s, x))) t :=
  (boundedFlatAffineSectionCoefficientCompositionRelHomotopy f g).comm n r s x t

end QuillenTest.SectionCoefficientComposition
