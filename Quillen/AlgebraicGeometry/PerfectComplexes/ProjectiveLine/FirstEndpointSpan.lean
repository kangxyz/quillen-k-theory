/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FirstEndpointBeta

/-!
# The actual exact original first endpoint weak span

The left endpoint is T_P(p* p_* T_P(K RIGHTtensor L)). The right endpoint is
literal original Efirst. Both map naturally and weakly into literal T_P(U(M)),
using original alpha_M and original beta followed by the actual forward unit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
open FlasqueCoefficients
variable (R : CommRingCat.{u})

/-- The actual raw bounded-perfect source p* p_* M. -/
def source := resolved R ⋙ SelfBaseChange.source R

/-- The actual bounded-perfect center U(M), with the native alpha association. -/
def centerBounded := resolved R ⋙
  (SelfBaseChange.target R ⋙ FlasqueBoundedBelow.inclusion (twoChartLine R))

/-- The actual original alpha, restricted to the actual right-tensor total coefficient. -/
def alpha : source R ⟶ centerBounded R :=
  CategoryTheory.Functor.whiskerLeft (resolved R) (SelfBaseChange.alpha R)

lemma alpha_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((alpha R).app K).hom = ((SelfBaseChange.alpha R).app ((resolved R).obj K)).hom := rfl

lemma alpha_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (BoundedBelow.waldhausen (twoChartLine R)).weq ((alpha R).app K) :=
  SelfBaseChange.alpha_weak R ((resolved R).obj K)

/-- Original beta in the actual bounded-perfect model, with an explicit native association. -/
def betaBounded : originalFirst R ⋙ FlasqueBoundedBelow.inclusion (twoChartLine R) ⟶
    centerBounded R :=
  CategoryTheory.Functor.whiskerRight (beta R)
    (FlasqueBoundedBelow.inclusion (twoChartLine R)) ≫
      (Functor.associator (resolved R) (SelfBaseChange.target R)
        (FlasqueBoundedBelow.inclusion (twoChartLine R))).hom

private lemma weak_comp_app {C D : Type*} [Category C] [Category D]
    (W : Waldhausen.Structure D) {F G H : C ⥤ D} (f : F ⟶ G) (g : G ⟶ H) (K : C)
    (hf : W.weq (f.app K)) (hg : W.weq (g.app K)) : W.weq ((f ≫ g).app K) :=
  W.weq.comp_mem _ _ hf hg

private lemma weak_triple_app {C D : Type*} [Category C] [Category D]
    (W : Waldhausen.Structure D) {F G H I : C ⥤ D}
    (f : F ⟶ G) (g : G ⟶ H) (h : H ⟶ I) (K : C)
    (hf : W.weq (f.app K)) (hg : W.weq (g.app K)) (hh : W.weq (h.app K)) :
    W.weq ((f ≫ g ≫ h).app K) :=
  W.weq.comp_mem _ _ hf (W.weq.comp_mem _ _ hg hh)

lemma betaBounded_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (BoundedBelow.waldhausen (twoChartLine R)).weq ((betaBounded R).app K) :=
  weak_comp_app (BoundedBelow.waldhausen (twoChartLine R))
    (CategoryTheory.Functor.whiskerRight (beta R)
      (FlasqueBoundedBelow.inclusion (twoChartLine R)))
    (Functor.associator (resolved R) (SelfBaseChange.target R)
      (FlasqueBoundedBelow.inclusion (twoChartLine R))).hom K
    ((FlasqueBoundedBelow.inclusion_exact (twoChartLine R)).weak
      ((beta R).app K) (beta_weak R K))
    ((BoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance)

lemma source_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq (source R) :=
  (rightTensorTotal_exact R).comp (SelfBaseChange.source_exact R)

lemma centerBounded_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq (centerBounded R) :=
  (rightTensorTotal_exact R).comp
    ((SelfBaseChange.target_exact R).comp (FlasqueBoundedBelow.inclusion_exact (twoChartLine R)))

/-- The literal totalized first PhiG source, before any shift convention. -/
def spanLeft := source R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

/-- The literal totalized actual common target. -/
def spanCenter := centerBounded R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

/-- The left span arrow is literal total of original alpha_M. -/
def spanLeftMap : spanLeft R ⟶ spanCenter R :=
  CategoryTheory.Functor.whiskerRight (alpha R)
    (FlasqueBoundedBelow.total (twoChartLine R))

/-- The canonical native association from target totalization to the native common center. -/
def centerAssociation :
    comparisonTarget R ⋙
      (FlasqueBoundedBelow.inclusion (twoChartLine R) ⋙
        FlasqueBoundedBelow.total (twoChartLine R)) ≅
      spanCenter R :=
  (Functor.associator (comparisonTarget R) (FlasqueBoundedBelow.inclusion (twoChartLine R))
    (FlasqueBoundedBelow.total (twoChartLine R))).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.associator (resolved R) (SelfBaseChange.target R)
          (FlasqueBoundedBelow.inclusion (twoChartLine R)))
        (FlasqueBoundedBelow.total (twoChartLine R))

/-- Original beta THEN the actual forward unit on U(M); native associations are explicit. -/
def spanRightMap : originalFirst R ⟶ spanCenter R :=
  beta R ≫ CategoryTheory.Functor.whiskerLeft (comparisonTarget R)
    (FlasqueBoundedBelow.flasqueUnit (twoChartLine R)) ≫ (centerAssociation R).hom

lemma spanLeftMap_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((spanLeftMap R).app K).hom =
      (godementTotal (twoChartLine R)).map ((alpha R).app K).hom := rfl

/-- The literal model beta, forward unit and native center association are all retained. -/
lemma spanRightMap_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (spanRightMap R).app K = (beta R).app K ≫
      (FlasqueBoundedBelow.flasqueUnit (twoChartLine R)).app ((comparisonTarget R).obj K) ≫
        (centerAssociation R).hom.app K := rfl

lemma spanLeftMap_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((spanLeftMap R).app K) :=
  FlasqueBoundedBelow.total_weak ((alpha R).app K) (alpha_weak R K)

lemma spanRightMap_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((spanRightMap R).app K) :=
  weak_triple_app (FlasqueBoundedBelow.waldhausen (twoChartLine R)) (beta R)
    (CategoryTheory.Functor.whiskerLeft (comparisonTarget R)
      (FlasqueBoundedBelow.flasqueUnit (twoChartLine R)))
    (centerAssociation R).hom K (beta_weak R K)
    (FlasqueBoundedBelow.flasqueUnit_weak (twoChartLine R) ((comparisonTarget R).obj K))
    ((FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance)

lemma spanLeft_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (spanLeft R) :=
  (source_exact R).comp (FlasqueBoundedBelow.total_exact (twoChartLine R))

lemma spanCenter_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (spanCenter R) :=
  (centerBounded_exact R).comp (FlasqueBoundedBelow.total_exact (twoChartLine R))

lemma source_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((source R).obj K).obj.IsStrictlyGE a := by
  let := resolved_isStrictlyGE R K a
  exact SelfBaseChange.source_isStrictlyGE R ((resolved R).obj K) a

lemma spanLeft_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((spanLeft R).obj K).obj.IsStrictlyGE a := by
  let := source_isStrictlyGE R K a
  exact FlasqueBoundedBelow.total_isStrictlyGE (twoChartLine R) ((source R).obj K) a

lemma spanCenter_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((spanCenter R).obj K).obj.IsStrictlyGE a := by
  have : ((centerBounded R).obj K).obj.IsStrictlyGE a := comparisonTarget_isStrictlyGE R K a
  exact FlasqueBoundedBelow.total_isStrictlyGE (twoChartLine R) ((centerBounded R).obj K) a

/-- Every actual zero is retained, so the installed chosen-zero/basepoint rebasing applies. -/
lemma span_zero {K : FlasqueBoundedBelow.Obj (twoChartLine R)} (hK : IsZero K) :
    IsZero ((spanLeft R).obj K) ∧ IsZero ((spanCenter R).obj K) ∧
      IsZero ((originalFirst R).obj K) :=
  ⟨(spanLeft_exact R).zero hK, (spanCenter_exact R).zero hK, (originalFirst_exact R).zero hK⟩

end Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
