/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedOriginalAnchorNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetChartAttachment

/-! The original moving coefficient chart retains every full node under source normalization. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTargetMovingNormalization
open BassH0Merge CommonReferenceNerve CommonReferenceProduct
open CoefficientBassSeedTargetChartAttachment CoefficientBassSeedOriginalAnchorNormalization

private theorem moving_word {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (F F' K : A ⥤ B) (J : B ⥤ C) (L : C ⥤ D) (H Z : B ⥤ D) (G : A ⥤ C)
    (sourceIso : F' ≅ F) (ε : G ≅ F' ⋙ J) (l : H ≅ J ⋙ L) (θ : H ≅ Z) (ρ : F ≅ K) :
    (isoWhiskerRight (ε ≪≫ isoWhiskerRight sourceIso J) L ≪≫
        Functor.associator F J L ≪≫ isoWhiskerLeft F l.symm) ≪≫
      isoWhiskerLeft F θ ≪≫ isoWhiskerRight ρ Z =
    (isoWhiskerRight ε L ≪≫ Functor.associator F' J L ≪≫ isoWhiskerLeft F' l.symm) ≪≫
      isoWhiskerLeft F' θ ≪≫ isoWhiskerRight (sourceIso ≪≫ ρ) Z := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  have hn := (l.symm ≪≫ θ).hom.naturality (sourceIso.hom.app x)
  have hh := congrArg (fun z ↦ L.map (ε.hom.app x) ≫ z ≫ Z.map (ρ.hom.app x)) hn
  simpa only [Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, NatTrans.comp_app, Functor.associator_hom_app,
    Category.comp_id, Category.id_comp, Functor.map_comp, Functor.comp_map,
    Iso.symm_hom, Category.assoc] using hh

/-- A proved full attachment-reference triangle transports every original moving-square node. -/
theorem moving_node_change {R : CommRingCat.{u}} (P : Over (Spec R))
    {a b : Under R} (f : a ⟶ b) {V : Model.{u + 1}}
    (D D' : V ⟶ modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a))))
    (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a))))
    (sourceIso : D'.functor ≅ D.functor)
    (ε : G.functor ≅ (D ≫ Ja P (a := a)).functor)
    (ε' : G.functor ≅ (D' ≫ Ja P (a := a)).functor)
    (hs : ε = ε' ≪≫ isoWhiskerRight sourceIso (Ja P (a := a)).functor)
    (N : Node D) (i : Fin 5) :
    movingNode P f D G ε N i = movingNode P f D' G ε' (reanchor sourceIso N) i := by
  rcases N with ⟨K, ρ⟩
  let Z : Node (H P f) := NativeSquareFiveSimplex.nodes
    (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentPlus P a)
    (laurentPlus P b) (coefficientMap P ((polynomialUnderFunctor R).map f))
    (coefficientMap_naturality P (underToLaurent R) f) i
  change (⟨K ≫ Z.1, squareAnchor P f D G ε ≪≫
    isoWhiskerLeft D.functor Z.2 ≪≫ isoWhiskerRight ρ Z.1.functor⟩ : Node (G ≫ L P f)) =
      ⟨K ≫ Z.1, squareAnchor P f D' G ε' ≪≫ isoWhiskerLeft D'.functor Z.2 ≪≫
        isoWhiskerRight (sourceIso ≪≫ ρ) Z.1.functor⟩
  apply congrArg (fun η : (G ≫ L P f).functor ≅ (K ≫ Z.1).functor ↦
    (⟨K ≫ Z.1, η⟩ : Node (G ≫ L P f)))
  rw [hs]
  exact moving_word D.functor D'.functor K.functor (Ja P).functor (L P f).functor
    (H P f).functor Z.1.functor G.functor sourceIso ε' (leftIso P f) Z.2 ρ

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c d : Under R}
  (p : a ⟶ b) (q : b ⟶ c) (f : c ⟶ d)
local notation "g" => coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) q) ≫
  coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) p)
local notation "h" => polynomialProjection P a
local notation "D₀" => BassOverlap.projectionMap P (a := a) ≫
  BassMOuterJoin.sideBinarySource P p q
local notation "G₀" => BassOverlap.commonReference P p q
local notation "ε₀" => BassMOuterJoin.oldSideIso P p q (underToLaurent R)
  (laurentPlus_projection P c)
local notation "ε₁" => normalizedAnchor P p q (underToLaurent R) (laurentPlus_projection P c)

/-- Every one of the five original coefficient-square nodes has its normalized full reference. -/
theorem moving_node (N : Node D₀) (i : Fin 5) :
    movingNode P f D₀ G₀ ε₀ N i =
      movingNode P f (normalizedMap (g ≫ h)) G₀ ε₁
        (reanchor (BinaryNormalizationSimplex.total g h) N) i :=
  moving_node_change P f _ _ _ (BinaryNormalizationSimplex.total g h) _ _
    (old_side_normalized P p q (underToLaurent R) (laurentPlus_projection P c)) N i

/-- The five shifted-square nodes keep the original common-unit anchor during normalization. -/
theorem shifted_moving_node (N : Node D₀) (i : Fin 5) :
    movingNode P f D₀ G₀
      (LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫ ε₀) N i =
      movingNode P f (normalizedMap (g ≫ h)) G₀
        (LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫ ε₁)
        (reanchor (BinaryNormalizationSimplex.total g h) N) i :=
  moving_node_change P f _ _ _ (BinaryNormalizationSimplex.total g h) _ _
    (old_side_shifted_normalized P p q (underToLaurent R) (laurentPlus_projection P c)) N i

/-- The full ordinary moving attachment retains the original square clock at every parameter. -/
theorem ordinary_moving (y : |nerve (Codiscrete (Node D₀))|) (t : I) :
    moving P f D₀ G₀ ε₀ (y, t) =
      moving P f (normalizedMap (g ≫ h)) G₀ ε₁
        (mapParameter (reanchor (BinaryNormalizationSimplex.total g h)) y, t) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter D₀ y
  rw [← hz]
  change FiniteParameter.parameter D₀ (G₀ ≫ L P f)
    (movingNode P f D₀ G₀ ε₀) (parameter D₀ N z,
      NativeSquareFiveSimplex.parameter t) =
    FiniteParameter.parameter (normalizedMap (g ≫ h)) (G₀ ≫ L P f)
      (movingNode P f (normalizedMap (g ≫ h)) G₀ ε₁)
      (mapParameter (reanchor (BinaryNormalizationSimplex.total g h)) (parameter D₀ N z),
        NativeSquareFiveSimplex.parameter t)
  erw [mapParameter_parameter, FiniteParameter.parameter_characteristic,
    FiniteParameter.parameter_characteristic]
  apply congrArg (fun ns ↦ parameter (G₀ ≫ L P f) ns
    (SimplexGrid.parameter k 4 (z, NativeSquareFiveSimplex.parameter t)))
  funext i
  exact moving_node P p q f (N ((SimplexGrid.indexEquiv k 4).symm i).1)
    ((SimplexGrid.indexEquiv k 4).symm i).2

/-- The full shifted moving attachment retains the original square clock at every parameter. -/
theorem shifted_moving (y : |nerve (Codiscrete (Node D₀))|) (t : I) :
    moving P f D₀ G₀ (LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫ ε₀) (y, t) =
      moving P f (normalizedMap (g ≫ h)) G₀
        (LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫ ε₁)
        (mapParameter (reanchor (BinaryNormalizationSimplex.total g h)) y, t) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter D₀ y
  rw [← hz]
  change FiniteParameter.parameter D₀ (G₀ ≫ L P f)
    (movingNode P f D₀ G₀ (LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫ ε₀))
    (parameter D₀ N z,
      NativeSquareFiveSimplex.parameter t) =
    FiniteParameter.parameter (normalizedMap (g ≫ h)) (G₀ ≫ L P f)
      (movingNode P f (normalizedMap (g ≫ h)) G₀
        (LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫ ε₁))
      (mapParameter (reanchor (BinaryNormalizationSimplex.total g h)) (parameter D₀ N z),
        NativeSquareFiveSimplex.parameter t)
  erw [mapParameter_parameter, FiniteParameter.parameter_characteristic,
    FiniteParameter.parameter_characteristic]
  apply congrArg (fun ns ↦ parameter (G₀ ≫ L P f) ns
    (SimplexGrid.parameter k 4 (z, NativeSquareFiveSimplex.parameter t)))
  funext i
  exact shifted_moving_node P p q f (N ((SimplexGrid.indexEquiv k 4).symm i).1)
    ((SimplexGrid.indexEquiv k 4).symm i).2

end Quillen.PerfectComplexes.CoefficientBassSeedTargetMovingNormalization
