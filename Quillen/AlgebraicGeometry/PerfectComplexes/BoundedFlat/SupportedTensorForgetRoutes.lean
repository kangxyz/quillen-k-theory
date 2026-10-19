/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedPullbackInputForgetIso
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedUnitorForgetIso
public import Quillen.Aglib.CategoryTheory.Functor.IsoSquareRouteWhiskering
public import Quillen.Aglib.CategoryTheory.Functor.IsoSquareRouteTargetWhiskering

/-! # Original support-forgetting routes and tensor unitor squares

The actual geometric and tensor support inclusions give two-edge routes. Changing a geometric
edge by its original tensor unitor retains the whole route on both its source and target.
The comparisons use the original inclusions, unitors, and functor associators.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open GlobalSectionChangeIndex SupportedTensorEvaluation

private theorem route_hom_app
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    {a : C₀ ⥤ C₁} {b : C₁ ⥤ C₂} {N : D₀ ⥤ D₁} {M : D₁ ⥤ D₂}
    {E₀ : C₀ ⥤ D₀} {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂}
    (s : a ⋙ E₁ ≅ E₀ ⋙ N) (t : b ⋙ E₂ ≅ E₁ ⋙ M) (K : C₀) :
    (isoSquareRoute s t).hom.app K = t.hom.app (a.obj K) ≫ M.map (s.hom.app K) := by
  simp only [isoSquareRoute, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

/-- The genuine support inclusion intertwines the original geometric pullbacks. -/
def supportedPullbackForgetIso {A B : Scheme.OpenPairs.{u}} (f : A ⟶ B) :
    boundedFlatPerfectSupportedPullback f ⋙ tensorCoefficientSupportedForget A.obj.hom ≅
      tensorCoefficientSupportedForget B.obj.hom ⋙ boundedFlatPerfectPullback f.hom.right :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro K L k
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)

private theorem pullbackForget_refl {A B : Scheme.OpenPairs.{u}} (f : A ⟶ B) :
    supportedPullbackForgetIso f = Iso.refl _ := rfl

private theorem tensorForget_refl {A B : Scheme.OpenPairs.{u}} (f : A ⟶ B) :
    tensorSupportedPairForgetIso f = Iso.refl _ := rfl

/-- The original tensor unitor commutes with both genuine support-forgetting edges. -/
theorem tensorPairUnitor_forget_square {A B : Scheme.OpenPairs.{u}} (f : A ⟶ B) :
    isoWhiskerRight (tensorPairUnitor f) (tensorCoefficientSupportedForget A.obj.hom) ≪≫
        supportedPullbackForgetIso f =
      tensorSupportedPairForgetIso f ≪≫
        isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
          (boundedFlatPerfectTensorUnitPullbackIso f.hom.right) := by
  rw [pullbackForget_refl, tensorForget_refl, Iso.trans_refl, Iso.refl_trans]
  exact tensorPairUnitor_forget f

/-- Both original geometric support-forgetting edges, with their actual associations. -/
def supportedPullbackForgetRoute {A B C : Scheme.OpenPairs.{u}} (f : A ⟶ B) (g : B ⟶ C) :=
  isoSquareRoute (supportedPullbackForgetIso g) (supportedPullbackForgetIso f)

/-- The actual two-edge geometric forgetful route has its canonical identity components. -/
theorem supportedPullbackForgetRoute_refl {A B C : Scheme.OpenPairs.{u}}
    (f : A ⟶ B) (g : B ⟶ C) : supportedPullbackForgetRoute f g = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [supportedPullbackForgetRoute, route_hom_app, supportedPullbackForgetIso,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp, NatTrans.id_app]
  exact (boundedFlatPerfectPullback f.hom.right).map_id _

/-- The whole geometric input square retains all four actual support-forgetting edges. -/
theorem supportedPullbackInputForgetSquare {A B C D : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b) :
    isoWhiskerRight (supportedPullbackInputSquareIso p q a b h)
        (tensorCoefficientSupportedForget C.obj.hom) ≪≫ supportedPullbackForgetRoute q b =
      supportedPullbackForgetRoute a p ≪≫
        isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
          (pullbackInputSquareIso p.hom.right q.hom.right a.hom.right b.hom.right
            (congrArg (fun f : C ⟶ B => f.hom.right) h)) := by
  rw [supportedPullbackForgetRoute_refl, supportedPullbackForgetRoute_refl,
    Iso.trans_refl, Iso.refl_trans]
  exact supportedPullbackInputSquareIso_forget p q a b h

/-- The tensor-first route through the actual two support-forgetting edges. -/
def tensorSupportedRawInputForgetLeftRoute {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (a : C ⟶ A) :=
  isoSquareRoute (tensorSupportedPairForgetIso p) (supportedPullbackForgetIso a)

/-- The tensor-second route through the actual two support-forgetting edges. -/
def tensorSupportedRawInputForgetRightRoute {B C D : Scheme.OpenPairs.{u}}
    (q : C ⟶ D) (b : D ⟶ B) :=
  isoSquareRoute (supportedPullbackForgetIso b) (tensorSupportedPairForgetIso q)

/-- The tensor-first unitor square retains both complete original forgetful routes. -/
theorem tensorSupportedRawInputForgetLeftRoute_unitor {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (a : C ⟶ A) :
    isoWhiskerRight
        (isoWhiskerRight (tensorPairUnitor p) (boundedFlatPerfectSupportedPullback a))
        (tensorCoefficientSupportedForget C.obj.hom) ≪≫ supportedPullbackForgetRoute a p =
      tensorSupportedRawInputForgetLeftRoute p a ≪≫
        isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
          (isoWhiskerRight (boundedFlatPerfectTensorUnitPullbackIso p.hom.right)
            (boundedFlatPerfectPullback a.hom.right)) := by
  exact (isoSquareRoute_leftIso (tensorPairUnitor p)
    (supportedPullbackForgetIso p) (supportedPullbackForgetIso a)).symm.trans
      ((congrArg (fun s => isoSquareRoute s (supportedPullbackForgetIso a))
        (tensorPairUnitor_forget_square p)).trans
        (isoSquareRoute_leftTargetIso (boundedFlatPerfectTensorUnitPullbackIso p.hom.right)
          (tensorSupportedPairForgetIso p) (supportedPullbackForgetIso a)))

/-- The tensor-second unitor square retains both complete original forgetful routes. -/
theorem tensorSupportedRawInputForgetRightRoute_unitor {B C D : Scheme.OpenPairs.{u}}
    (q : C ⟶ D) (b : D ⟶ B) :
    isoWhiskerRight
        (isoWhiskerLeft (boundedFlatPerfectSupportedPullback b) (tensorPairUnitor q))
        (tensorCoefficientSupportedForget C.obj.hom) ≪≫ supportedPullbackForgetRoute q b =
      tensorSupportedRawInputForgetRightRoute q b ≪≫
        isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
          (isoWhiskerLeft (boundedFlatPerfectPullback b.hom.right)
            (boundedFlatPerfectTensorUnitPullbackIso q.hom.right)) := by
  exact (isoSquareRoute_rightIso (tensorPairUnitor q)
    (supportedPullbackForgetIso b) (supportedPullbackForgetIso q)).symm.trans
      ((congrArg (fun t => isoSquareRoute (supportedPullbackForgetIso b) t)
        (tensorPairUnitor_forget_square q)).trans
        (isoSquareRoute_rightTargetIso (boundedFlatPerfectTensorUnitPullbackIso q.hom.right)
          (supportedPullbackForgetIso b) (tensorSupportedPairForgetIso q)))

end Quillen.PerfectComplexes
