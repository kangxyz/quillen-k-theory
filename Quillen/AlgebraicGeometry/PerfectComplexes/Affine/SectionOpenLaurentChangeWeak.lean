/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenDiagramLaurent

/-!
# Changing section weaknesses preserves the original Laurent track

The actual fine-to-coarse maps use identity section functors and the identical chosen zeros.
Their actual coefficient Model square intertwines the same original Laurent automorphism.
Consequently every realized homotopy value, including degree zero, is carried to the coarse
track without reparameterization or an assumed seed compatibility.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.Scheme.AffineOpenPair Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

private theorem identityActionSquare
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F G : C ⥤ D) (η : F ⋙ 𝟭 D ⟶ 𝟭 C ⋙ G) (e : 𝟭 D ≅ 𝟭 D) :
    Functor.whiskerRight (Quillen.FunctorIdentityAutomorphism.onFunctor F e).hom (𝟭 D) ≫ η =
      η ≫ Functor.whiskerLeft (𝟭 C)
        (Quillen.FunctorIdentityAutomorphism.onFunctor G e).hom :=
  Quillen.FunctorIdentityAutomorphism.onFunctor_whisker_square
    F G (𝟭 C) (𝟭 D) η e e (by
      apply NatTrans.ext
      funext X
      rfl)

/-- Original fine-to-coarse Model maps retain the same Laurent coefficient square. -/
theorem boundedFlatAffineSectionOpenLaurentChangeWeakModelSquare (a : Under R) :
    boundedFlatAffineSectionModelMap (laurentCoefficient a.right) ≫
        boundedFlatAffineSectionOpenModelMap (inclusion j ((laurentUnderFunctor R).obj a)) =
      boundedFlatAffineSectionOpenModelMap (inclusion j a) ≫
        (boundedFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app a) :=
  (boundedFlatAffineSectionOpenModelTransformation j).naturality
    ((laurentUnderCoefficient R).app a)

/-- The identity section functors preserve the original scalar automorphism literally. -/
theorem boundedFlatAffineSectionOpenLaurentChangeWeakUnitSquare (a : Under R) :
    Functor.whiskerRight (boundedFlatAffineSectionLaurentPullbackUnitIso a.right).hom
        (boundedFlatAffineSectionOpenModelMap
          (inclusion j ((laurentUnderFunctor R).obj a))).functor ≫
        eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineSectionOpenLaurentChangeWeakModelSquare j a)) =
      eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineSectionOpenLaurentChangeWeakModelSquare j a)) ≫
        Functor.whiskerLeft (boundedFlatAffineSectionOpenModelMap (inclusion j a)).functor
          (boundedFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a).hom :=
  identityActionSquare _ _ _ _

/-- Changing weakness preserves every original interval value of the actual Laurent loop. -/
theorem boundedFlatAffineSectionOpenDiagramLaurentHomotopy_changeWeak_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj a.right).space n) :
    (boundedFlatAffineSectionOpenPrespectrumMap
        (inclusion j ((laurentUnderFunctor R).obj a))).map n
        ((boundedFlatAffineSectionLaurentUnitHomotopy a.right).level n (t, x)) =
      (boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n
        (t, (boundedFlatAffineSectionOpenPrespectrumMap (inclusion j a)).map n x) :=
  prespectrumIsoHomotopy_square_apply
    (boundedFlatAffineSectionModelMap (laurentCoefficient a.right))
    ((boundedFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app a))
    (boundedFlatAffineSectionOpenModelMap (inclusion j a))
    (boundedFlatAffineSectionOpenModelMap (inclusion j ((laurentUnderFunctor R).obj a)))
    (boundedFlatAffineSectionLaurentPullbackUnitIso a.right)
    (boundedFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a)
    (boundedFlatAffineSectionOpenLaurentChangeWeakModelSquare j a)
    (boundedFlatAffineSectionOpenLaurentChangeWeakUnitSquare j a) n t x

end Quillen.PerfectComplexes
