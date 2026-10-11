/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionForgetModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionDiagramLaurent
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentHomotopy

/-!
# Forgetting support preserves the whole original Laurent-unit loop

The actual scalar forget identity gives the automorphism square of the unchanged coefficient
Model arrows. Its realized square preserves every level and interval value of the original
Laurent track. The specified fixed pullbacks and original Laurent coordinate remain explicit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.Scheme.AffineOpenPair Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

attribute [local irreducible] boundedFlatAffineSupportedSectionUnitIso
  boundedFlatAffineSectionUnitIso boundedFlatAffineOriginalEvaluation

/-- The original target scalar action commutes literally with forgetting support. -/
theorem boundedFlatAffineSupportedSectionUnitIso_forget (r : (Γ(Spec R, ⊤))ˣ) :
    Functor.whiskerRight (boundedFlatAffineSupportedSectionUnitIso j r).hom
        (boundedFlatAffineSectionSupported j).ι =
      Functor.whiskerLeft (boundedFlatAffineSectionSupported j).ι
        (boundedFlatAffineSectionUnitIso R r).hom :=
  Quillen.FunctorIdentityAutomorphism.whisker_hom_eq_of_evaluation
    (boundedFlatAffineSectionSupported j).ι (𝟭 _) (boundedFlatAffineSectionSupported j).ι rfl
    (boundedFlatAffineSupportedSectionUnitIso j r)
    (boundedFlatAffineSectionUnitIso R r) (boundedFlatAffineSectionUnitIso R r)
    (boundedFlatAffineSupportedSectionUnitIso_hom j r) (fun _ ↦ rfl)

/-- The exact original Laurent Model coefficient square commutes with the actual inclusion. -/
theorem boundedFlatAffineSupportedDiagramLaurentForgetModelSquare (a : Under R) :
    (boundedFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderCoefficient R).app a) ≫
        boundedFlatAffineSupportedSectionForgetModelMap
          (inclusion j ((laurentUnderFunctor R).obj a)) =
      boundedFlatAffineSupportedSectionForgetModelMap (inclusion j a) ≫
        boundedFlatAffineSectionModelMap (laurentCoefficient a.right) :=
  (boundedFlatAffineSupportedSectionForgetModelTransformation j).naturality
    ((laurentUnderCoefficient R).app a)

/-- The actual forget square intertwines the original forward Laurent automorphisms. -/
theorem boundedFlatAffineSupportedDiagramLaurentForgetUnitSquare (a : Under R) :
    Functor.whiskerRight (boundedFlatAffineSupportedDiagramLaurentPullbackUnitIso j a).hom
        (boundedFlatAffineSupportedSectionForgetModelMap
          (inclusion j ((laurentUnderFunctor R).obj a))).functor ≫
        eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineSupportedDiagramLaurentForgetModelSquare j a)) =
      eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineSupportedDiagramLaurentForgetModelSquare j a)) ≫
        Functor.whiskerLeft
          (boundedFlatAffineSupportedSectionForgetModelMap (inclusion j a)).functor
          (boundedFlatAffineSectionLaurentPullbackUnitIso a.right).hom :=
  Quillen.FunctorIdentityAutomorphism.onFunctor_whisker_square _ _ _ _ _ _ _
    (boundedFlatAffineSupportedSectionUnitIso_forget
      (inclusion j ((laurentUnderFunctor R).obj a))
      (Quillen.Scheme.PolynomialLaurent.laurentGlobalUnit a.right))

/-- Forgetting support retains every original time value of the realized Laurent action. -/
theorem boundedFlatAffineSupportedDiagramLaurentHomotopy_forget_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineSupportedSectionForgetPrespectrumMap
        (inclusion j ((laurentUnderFunctor R).obj a))).map n
        ((boundedFlatAffineSupportedDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedFlatAffineSectionLaurentUnitHomotopy a.right).level n
        (t, (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a)).map n x) :=
  prespectrumIsoHomotopy_square_apply
    ((boundedFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderCoefficient R).app a))
    (boundedFlatAffineSectionModelMap (laurentCoefficient a.right))
    (boundedFlatAffineSupportedSectionForgetModelMap (inclusion j a))
    (boundedFlatAffineSupportedSectionForgetModelMap
      (inclusion j ((laurentUnderFunctor R).obj a)))
    (boundedFlatAffineSupportedDiagramLaurentPullbackUnitIso j a)
    (boundedFlatAffineSectionLaurentPullbackUnitIso a.right)
    (boundedFlatAffineSupportedDiagramLaurentForgetModelSquare j a)
    (boundedFlatAffineSupportedDiagramLaurentForgetUnitSquare j a) n t x

end Quillen.PerfectComplexes
