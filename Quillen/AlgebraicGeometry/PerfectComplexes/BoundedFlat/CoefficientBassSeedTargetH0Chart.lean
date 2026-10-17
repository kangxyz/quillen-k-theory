/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetH0Reference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetCharts
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeReferenceWordCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetUnitReference

/-! The exact chart-anchor route relating H0 and the added original sheets. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTargetH0Chart
open BassH0Merge BassReferenceMerge
local notation "N" => boundedFlatNormalizedPullback
local notation "C" => boundedFlatNormalizedPullbackCompIso

/-- The complete original chart anchor retains the outer projection equality transport. -/
theorem chart_anchor_total {A B C' D : Scheme.{u}}
    (p : B ⟶ A) (q : C' ⟶ B) (c : D ⟶ C') (r : C' ⟶ A) (hr : q ≫ p = r) :
    ProjectionRectangleSquareRows.chartAnchor p q c r hr ≪≫
        isoWhiskerLeft (normalizedMap p).functor (BinaryNormalizationSimplex.total c q) =
      BinaryNormalizationSimplex.total c r ≪≫
        isoWhiskerRight
          (eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) hr.symm) ≪≫
            BinaryNormalizationSimplex.total q p) (normalizedMap c).functor := by
  subst r
  simp only [eqToIso_refl, Iso.refl_trans]
  change smallIso (eqToIso (congrArg N (Category.assoc c q p).symm) ≪≫ C (c ≫ q) p) ≪≫
      isoWhiskerLeft (normalizedMap p).functor (smallIso (C c q)) =
    smallIso (C c (q ≫ p)) ≪≫ isoWhiskerRight (smallIso (C q p)) (normalizedMap c).functor
  erw [smallIso_precomp, smallIso_postcomp]
  rw [← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  have hs := anchored_factorizations_strict c q p (c ≫ q) (q ≫ p) (c ≫ q ≫ p)
    rfl rfl (Category.assoc c q p).symm rfl
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using hs


variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
open CoefficientBassSeedTargetH0Reference CoefficientBassSeedTargetChartAttachment

/-- The projection transport and positive chart total retain their literal original factors. -/
theorem projection_endpoint :
    projectionReferenceIso P (a := a) ≪≫
        BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P a) =
      eqToIso (congrArg (fun k ↦ (normalizedMap k).functor)
        (laurentPlus_projection P a).symm) ≪≫
          BinaryNormalizationSimplex.total (laurentPlus P a) (polynomialProjection P a) := by
  have h : BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P a) =
      BinaryNormalizationSimplex.total (laurentPlus P a) (polynomialProjection P a) := by
    change smallIso (eqToIso _ ≪≫ C (laurentPlus P a) (polynomialProjection P a)) =
      smallIso (C (laurentPlus P a) (polynomialProjection P a))
    apply congrArg smallIso
    simp only [eqToIso_refl, Iso.refl_trans]
  rw [h]
  rfl

/-- The actual H0 chart anchor agrees before cancelling its final binary total. -/
theorem h0_chart_total :
    h0ProjectionIso P f ≪≫
        isoWhiskerRight
          (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P a))
          (L P f).functor =
      ProjectionRectangleSquareRows.chartAnchor (polynomialProjection P a) (laurentPlus P a)
        (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentProjection P a)
        (laurentPlus_projection P a) ≪≫
          isoWhiskerLeft (normalizedMap (polynomialProjection P a)).functor (leftIso P f) := by
  rw [h0ProjectionIso, Iso.trans_assoc, ← isoWhiskerRight_trans, projection_endpoint]
  exact (chart_anchor_total (polynomialProjection P a) (laurentPlus P a)
    (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentProjection P a)
    (laurentPlus_projection P a)).symm


private theorem projection_word {X Y : Scheme.{u}} (s r t : X ⟶ Y)
    (h₀ : s = r) (h₁ : t = r) {K : _ ⥤ _} (e : N t ≅ K) :
    eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) h₀.symm) ≪≫
        smallIso (eqToIso (congrArg N (h₀.trans h₁.symm)) ≪≫ e) =
      eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) h₁.symm) ≪≫ smallIso e := by
  subst r
  subst t
  simp only [eqToIso_refl, Iso.refl_trans]

/-- Both chart projections retain their separate actual projection equations. -/
theorem projection_endpoint_for (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    projectionReferenceIso P (a := a) ≪≫ BassMJoin.projectionEndpointIso P α ha =
      eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) ha.symm) ≪≫
        BinaryNormalizationSimplex.total (coefficientMap P (α.app a)) (polynomialProjection P a) :=
  projection_word (laurentPlus P a ≫ polynomialProjection P a) (laurentProjection P a)
    (coefficientMap P (α.app a) ≫ polynomialProjection P a) (laurentPlus_projection P a) ha
    (C (coefficientMap P (α.app a)) (polynomialProjection P a))

/-- The whole H0 chart anchor equation holds for each independently chosen chart. -/
theorem h0_chart_total_for (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    h0ProjectionIso P f ≪≫
        isoWhiskerRight (BassMJoin.projectionEndpointIso P α ha) (L P f).functor =
      ProjectionRectangleSquareRows.chartAnchor (polynomialProjection P a)
        (coefficientMap P (α.app a)) (coefficientMap P ((laurentUnderFunctor R).map f))
        (laurentProjection P a) ha ≪≫
          isoWhiskerLeft (normalizedMap (polynomialProjection P a)).functor
            (BinaryNormalizationSimplex.total
              (coefficientMap P ((laurentUnderFunctor R).map f)) (coefficientMap P (α.app a))) := by
  rw [h0ProjectionIso, Iso.trans_assoc, ← isoWhiskerRight_trans, projection_endpoint_for]
  exact (chart_anchor_total (polynomialProjection P a) (coefficientMap P (α.app a))
    (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentProjection P a) ha).symm

private theorem whiskered_chart {V₀ A₀ B₀ C₀ D₀ : Type*}
    [Category V₀] [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    (E : V₀ ⥤ A₀) (J : A₀ ⥤ B₀) (K : B₀ ⥤ C₀) (L : C₀ ⥤ D₀)
    (F : A₀ ⥤ C₀) (Q : A₀ ⥤ D₀) (H : B₀ ⥤ D₀) (G : V₀ ⥤ C₀)
    (e : F ≅ J ⋙ K) (h : Q ≅ F ⋙ L) (δ : H ≅ K ⋙ L) (γ : Q ≅ J ⋙ H)
    (τ : E ⋙ F ≅ G)
    (hh : h ≪≫ isoWhiskerRight e L = γ ≪≫ isoWhiskerLeft J δ) :
    (isoWhiskerLeft E h ≪≫ (Functor.associator E F L).symm ≪≫
        isoWhiskerRight τ L) ≪≫
      (isoWhiskerRight (τ.symm ≪≫ isoWhiskerLeft E e ≪≫
          (Functor.associator E J K).symm) L ≪≫
        Functor.associator (E ⋙ J) K L ≪≫ isoWhiskerLeft (E ⋙ J) δ.symm) =
      isoWhiskerLeft E γ := by
  apply Iso.ext
  ext X
  have he := congrArg (fun i ↦ i.hom.app (E.obj X)) hh
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app] at he
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Iso.symm_hom, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.comp_obj, Functor.map_comp, Category.id_comp,
    Category.comp_id, Category.assoc]
  let ht := L.mapIso (τ.app X)
  change h.hom.app (E.obj X) ≫ ht.hom ≫ ht.inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, he]
  rw [Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (τ : (BassProjectionPath.WholeReference.reference P a E).functor ≅ G.functor)

/-- The actual ordinary sheet anchor after the given full Laurent reference change. -/
def sourceAnchor : G.functor ≅
    ((E ≫ normalizedMap (polynomialProjection P a)) ≫ Ja P (a := a)).functor :=
  τ.symm ≪≫ isoWhiskerLeft E.functor
    (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P a)) ≪≫
      (Functor.associator E.functor (normalizedMap (polynomialProjection P a)).functor
        (Ja P (a := a)).functor).symm

/-- The entire moving chart anchor agrees in the original H0 reference. -/
theorem moving_anchor :
    referenceBridge P f E G τ ≪≫
        squareAnchor P f (E ≫ normalizedMap (polynomialProjection P a)) G
          (sourceAnchor P E G τ) =
      isoWhiskerLeft E.functor
        (ProjectionRectangleSquareRows.chartAnchor (polynomialProjection P a) (laurentPlus P a)
          (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentProjection P a)
          (laurentPlus_projection P a)) := by
  exact whiskered_chart E.functor (normalizedMap (polynomialProjection P a)).functor
    (Ja P (a := a)).functor (L P f).functor (BassProjectionPath.source P a).functor
    (BassH0Diagram.reference P f).functor (H P f).functor G.functor
    (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P a))
    (h0ProjectionIso P f) (leftIso P f)
    (ProjectionRectangleSquareRows.chartAnchor (polynomialProjection P a) (laurentPlus P a)
      (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentProjection P a)
      (laurentPlus_projection P a)) τ (h0_chart_total P f)


open CommonReferenceNerve BassProjectionPath.WholeReference.FourEdge

private theorem pair_other {V₀ W₀ T₀ : Model.{u}}
    {D₀ D₁ : V₀ ⟶ W₀} {H₀ H₁ : W₀ ⟶ T₀}
    (e : D₀.functor ≅ D₁.functor) (z : H₀.functor ≅ H₁.functor) :
    (Functor.uncurry.obj (whiskeringLeft V₀ W₀ T₀)).mapIso (e.prod z) =
      isoWhiskerLeft D₀.functor z ≪≫ isoWhiskerRight e H₁.functor := by
  apply Iso.ext
  ext X
  exact z.hom.naturality (e.hom.app X)

/-- Every complete moving chart node agrees in the actual H0 reference. -/
theorem moving_nodes
    (M₀ : Node (E ≫ normalizedMap (polynomialProjection P a))) (i : Fin 5) :
    CommonReferenceProduct.reanchor (referenceBridge P f E G τ)
        (movingNode P f (E ≫ normalizedMap (polynomialProjection P a)) G
          (sourceAnchor P E G τ) M₀ i) =
      Target.chartNodes P f E (underToLaurent R) (laurentPlus_projection P a) M₀ i := by
  let Z := BassH0ChartBoundaryRows.squareNodes P f (underToLaurent R) i
  change (⟨M₀.1 ≫ Z.1, referenceBridge P f E G τ ≪≫
      (squareAnchor P f (E ≫ normalizedMap (polynomialProjection P a)) G
        (sourceAnchor P E G τ) ≪≫
        isoWhiskerLeft (E ≫ normalizedMap (polynomialProjection P a)).functor Z.2 ≪≫
          isoWhiskerRight M₀.2 Z.1.functor)⟩ : Node (Target.reference P f E)) =
    ⟨M₀.1 ≫ Z.1, Target.chartAnchor P f E (underToLaurent R) (laurentPlus_projection P a) ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso (M₀.2.prod Z.2)⟩
  apply congrArg (fun e : (Target.reference P f E).functor ≅ (M₀.1 ≫ Z.1).functor ↦
    (⟨M₀.1 ≫ Z.1, e⟩ : Node (Target.reference P f E)))
  rw [← Iso.trans_assoc, moving_anchor, pair_other]
  rfl


private theorem parameter_target_map {V₀ W₀ V₁ W₁ V₂ W₂ : Model.{u}}
    (E₀ : V₀ ⟶ W₀) (D₀ : V₁ ⟶ W₁) (F₀ : V₂ ⟶ W₂) {q₀ : ℕ}
    (g₀ : Node E₀ → Fin (q₀ + 1) → Node D₀) (h₀ : Node D₀ → Node F₀)
    (y : |nerve (Codiscrete (Node E₀))|) (z : StdSimplex ℝ (Fin (q₀ + 1))) :
    mapParameter h₀ (FiniteParameter.parameter E₀ D₀ g₀ (y, z)) =
      FiniteParameter.parameter E₀ F₀ (fun e i ↦ h₀ (g₀ e i)) (y, z) := by
  obtain ⟨k, N₀, w, rfl⟩ := exists_parameter E₀ y
  rw [FiniteParameter.parameter_characteristic, mapParameter_parameter,
    FiniteParameter.parameter_characteristic]
  rfl

/-- The complete moving attachment equals the H0 chart family at the unchanged square clock. -/
theorem moving_family (y : |nerve (Codiscrete
    (Node (E ≫ normalizedMap (polynomialProjection P a))))|) (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (referenceBridge P f E G τ))
        (moving P f (E ≫ normalizedMap (polynomialProjection P a)) G
          (sourceAnchor P E G τ) (y, t)) =
      Target.chart P f E (underToLaurent R) (laurentPlus_projection P a) (y, t) := by
  change mapParameter (CommonReferenceProduct.reanchor (referenceBridge P f E G τ))
      (FiniteParameter.parameter (E ≫ normalizedMap (polynomialProjection P a)) (G ≫ L P f)
        (movingNode P f (E ≫ normalizedMap (polynomialProjection P a)) G
          (sourceAnchor P E G τ)) (y, NativeSquareFiveSimplex.parameter t)) =
    FiniteParameter.parameter (E ≫ normalizedMap (polynomialProjection P a))
      (Target.reference P f E)
      (Target.chartNodes P f E (underToLaurent R) (laurentPlus_projection P a))
      (y, NativeSquareFiveSimplex.parameter t)
  rw [parameter_target_map]
  apply congrArg (fun ns ↦ FiniteParameter.parameter
    (E ≫ normalizedMap (polynomialProjection P a)) (Target.reference P f E) ns
      (y, NativeSquareFiveSimplex.parameter t))
  funext N₀ i
  exact moving_nodes P f E G τ N₀ i


/-- The shifted sheet acts by the full conjugated Laurent reference automorphism. -/
def shiftedReference (δ : G.functor ≅ G.functor) :
    (Target.reference P f E).functor ≅ (Target.reference P f E).functor :=
  referenceBridge P f E G τ ≪≫ isoWhiskerRight δ (L P f).functor ≪≫
    (referenceBridge P f E G τ).symm

/-- Every shifted moving node retains the conjugated unit action in the H0 reference. -/
theorem shifted_moving_nodes (δ : G.functor ≅ G.functor)
    (M₀ : Node (E ≫ normalizedMap (polynomialProjection P a))) (i : Fin 5) :
    CommonReferenceProduct.reanchor (referenceBridge P f E G τ)
        (movingNode P f (E ≫ normalizedMap (polynomialProjection P a)) G
          (δ ≪≫ sourceAnchor P E G τ) M₀ i) =
      CommonReferenceProduct.reanchor (shiftedReference P f E G τ δ)
        (Target.chartNodes P f E (underToLaurent R) (laurentPlus_projection P a) M₀ i) := by
  rw [← moving_nodes P f E G τ M₀ i]
  dsimp only [movingNode, CommonReferenceProduct.reanchor, shiftedReference, squareAnchor]
  congr 1
  simp only [isoWhiskerRight_trans, Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- The shifted whole moving family keeps its full reference action and original clock. -/
theorem shifted_moving_family (δ : G.functor ≅ G.functor)
    (y : |nerve (Codiscrete (Node (E ≫ normalizedMap (polynomialProjection P a))))|)
    (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (referenceBridge P f E G τ))
        (moving P f (E ≫ normalizedMap (polynomialProjection P a)) G
          (δ ≪≫ sourceAnchor P E G τ) (y, t)) =
      mapParameter (CommonReferenceProduct.reanchor (shiftedReference P f E G τ δ))
        (Target.chart P f E (underToLaurent R) (laurentPlus_projection P a) (y, t)) := by
  change mapParameter (CommonReferenceProduct.reanchor (referenceBridge P f E G τ))
      (FiniteParameter.parameter (E ≫ normalizedMap (polynomialProjection P a)) (G ≫ L P f)
        (movingNode P f (E ≫ normalizedMap (polynomialProjection P a)) G
          (δ ≪≫ sourceAnchor P E G τ)) (y, NativeSquareFiveSimplex.parameter t)) =
    mapParameter (CommonReferenceProduct.reanchor (shiftedReference P f E G τ δ))
      (FiniteParameter.parameter (E ≫ normalizedMap (polynomialProjection P a))
        (Target.reference P f E)
        (Target.chartNodes P f E (underToLaurent R) (laurentPlus_projection P a))
        (y, NativeSquareFiveSimplex.parameter t))
  rw [parameter_target_map, parameter_target_map]
  apply congrArg (fun ns ↦ FiniteParameter.parameter
    (E ≫ normalizedMap (polynomialProjection P a)) (Target.reference P f E) ns
      (y, NativeSquareFiveSimplex.parameter t))
  funext N₀ i
  exact shifted_moving_nodes P f E G τ δ N₀ i


open Quillen.FunctorIdentityAutomorphism LaurentUnitReferenceSpecialization

/-- The actual coefficient-unit law identifies the conjugated action with the target unit. -/
theorem shiftedReference_unit :
    shiftedReference P f E G τ (onFunctor G.functor (smallUnit P a)) =
      onFunctor (Target.reference P f E).functor (smallUnit P b) := by
  have h := CoefficientBassSeedTargetUnitReference.unit_intertwine P f G
    (Target.reference P f E) (referenceBridge P f E G τ)
  have hc := congrArg (fun e ↦ e ≪≫ (referenceBridge P f E G τ).symm) h.symm
  calc
    shiftedReference P f E G τ (onFunctor G.functor (smallUnit P a)) =
        (referenceBridge P f E G τ ≪≫
          isoWhiskerRight (onFunctor G.functor (smallUnit P a)) (L P f).functor) ≪≫
            (referenceBridge P f E G τ).symm := (Iso.trans_assoc _ _ _).symm
    _ = (onFunctor (Target.reference P f E).functor (smallUnit P b) ≪≫
          referenceBridge P f E G τ) ≪≫ (referenceBridge P f E G τ).symm := hc
    _ = onFunctor (Target.reference P f E).functor (smallUnit P b) := by
      simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

/-- The full shifted chart family is the target unit acting on the entire ordinary family. -/
theorem unit_moving_family
    (y : |nerve (Codiscrete (Node (E ≫ normalizedMap (polynomialProjection P a))))|)
    (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (referenceBridge P f E G τ))
        (moving P f (E ≫ normalizedMap (polynomialProjection P a)) G
          (onFunctor G.functor (smallUnit P a) ≪≫ sourceAnchor P E G τ) (y, t)) =
      mapParameter (CommonReferenceProduct.reanchor
        (onFunctor (Target.reference P f E).functor (smallUnit P b)))
        (Target.chart P f E (underToLaurent R) (laurentPlus_projection P a) (y, t)) := by
  rw [shifted_moving_family, shiftedReference_unit]

end Quillen.PerfectComplexes.CoefficientBassSeedTargetH0Chart
