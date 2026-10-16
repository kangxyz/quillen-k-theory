/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialSpanUnitNodes

/-! Actual shared reference nodes on the Laurent sides of the original Bass unit cube.
The unit coherence equations concern the original normalized pullback transformations, and
are used before identifying any scalar labels or realized families. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientBassUnitBoundaryNodes
open OriginalUnitSquareSimplex CoefficientPolynomialSpanUnitNodes

/-- The actual normalized right unit route has identity composite transformation. -/
theorem right_route_identity {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (rightFirst f).hom ≫ (rightSecond f).hom = 𝟙 _ := by
  have h : (boundedFlatNormalizedRightUnitFirst f).hom ≫
      (boundedFlatNormalizedRightUnitSecond f).hom = 𝟙 _ := by
    simp only [boundedFlatNormalizedRightUnitFirst, boundedFlatNormalizedRightUnitSecond,
      Iso.trans_hom, eqToIso.hom, isoWhiskerLeft_hom, Category.assoc]
    rw [boundedFlatNormalizedPullbackCompIso_right_unitality]
    simp
  apply NatTrans.ext
  funext A
  change AsSmall.up.{u, u + 1, 0}.map ((boundedFlatNormalizedRightUnitFirst f).hom.app
      (AsSmall.down.{u, u + 1, 0}.obj A)) ≫
    AsSmall.up.{u, u + 1, 0}.map ((boundedFlatNormalizedRightUnitSecond f).hom.app
      (AsSmall.down.{u, u + 1, 0}.obj A)) = 𝟙 _
  exact (AsSmall.up.{u, u + 1, 0}.map_comp _ _).symm.trans
    ((congrArg (fun η ↦ AsSmall.up.{u, u + 1, 0}.map η)
      (NatTrans.congr_app h (AsSmall.down.{u, u + 1, 0}.obj A))).trans
      (AsSmall.up.{u, u + 1, 0}.map_id _))

/-- The original left route has the same literal identity composite. -/
theorem left_route_identity {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (leftFirst f).hom ≫ (leftSecond f).hom = 𝟙 _ :=
  (two_routes f).symm.trans (right_route_identity f)

/-- The first right unit transformation is the actual inverse of its terminal unit. -/
theorem right_first_inverse {X Y : Scheme.{u}} (f : X ⟶ Y) :
    rightFirst f = (rightSecond f).symm := by
  apply Iso.ext
  apply (cancel_mono (rightSecond f).hom).1
  rw [right_route_identity, Iso.symm_hom, Iso.inv_hom_id]

/-- The first left unit transformation is the actual inverse of its terminal unit. -/
theorem left_first_inverse {X Y : Scheme.{u}} (f : X ⟶ Y) :
    leftFirst f = (leftSecond f).symm := by
  apply Iso.ext
  apply (cancel_mono (leftSecond f).hom).1
  rw [left_route_identity, Iso.symm_hom, Iso.inv_hom_id]

/-- The middle geometric identity transformation is the same under the two actual whiskerings. -/
theorem shared_second {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    isoWhiskerRight (rightSecond p) (sourceMap q).functor =
      isoWhiskerLeft (sourceMap p).functor (leftSecond q) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [rightSecond, leftSecond, boundedFlatNormalizedRightUnitSecond,
    boundedFlatNormalizedLeftUnitSecond, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.trans_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    leftUnitor_hom_app, rightUnitor_hom_app]
  rfl

/-- Equality of the original unit inverses identifies the shared initial reference. -/
theorem shared_first {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    isoWhiskerRight (rightFirst p) (sourceMap q).functor =
      isoWhiskerLeft (sourceMap p).functor (leftFirst q) := by
  rw [right_first_inverse, left_first_inverse]
  exact congrArg Iso.symm (shared_second p q)

/-- The original split geometric normalization step is also preserved, not only its composite. -/
theorem shared_geometric {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    isoWhiskerRight (rightSecondGeometric p) (sourceMap q).functor =
      isoWhiskerLeft (sourceMap p).functor (leftSecondGeometric q) := by
  rfl

/-- The whole left unit is the actual two-step original identity, whiskered by pullback. -/
theorem left_second_total {A B : Scheme.{u}} (p : B ⟶ A) :
    leftSecond p = isoWhiskerRight (unitFirst A ≪≫ unitSecond A) (sourceMap p).functor := by
  apply Iso.ext
  rw [← left_second_composite]
  simp only [isoWhiskerRight_hom, Iso.trans_hom, whiskerRight_comp]
  rfl

/-- Naturality transports a chart anchor through the actual two-step identity transformation. -/
theorem chart_anchor {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B)
    (S : modelOf (boundedFlatPerfectWaldhausen A) ⟶
      modelOf (boundedFlatPerfectWaldhausen C))
    (σ : S.functor ≅ (sourceMap p ≫ sourceMap q).functor) :
    isoWhiskerLeft (unitSourceMap A).functor σ ≪≫
        (isoWhiskerRight (leftFirst p) (sourceMap q).functor).symm =
      isoWhiskerRight (unitFirst A ≪≫ unitSecond A) S.functor ≪≫ σ := by
  rw [left_first_inverse]
  change isoWhiskerLeft (unitSourceMap A).functor σ ≪≫
      isoWhiskerRight (leftSecond p) (sourceMap q).functor = _
  rw [left_second_total]
  change isoWhiskerLeft (unitSourceMap A).functor σ ≪≫
      isoWhiskerRight (unitFirst A ≪≫ unitSecond A) (sourceMap p ≫ sourceMap q).functor = _
  exact isoWhiskerLeft_trans_isoWhiskerRight _ _

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The original positive Laurent unit square, precomposed with the polynomial projection. -/
def plusSideNodes (i : Fin 8) : Node P a :=
  ⟨sourceMap (polynomialProjection P a) ≫ vertices (laurentPlus P a) i,
    plusSourceIso P a ≪≫ isoWhiskerLeft (sourceMap (polynomialProjection P a)).functor
      (references (laurentPlus P a) i)⟩

/-- The original inverse Laurent unit square retains its separate reference anchor. -/
def minusSideNodes (i : Fin 8) : Node P a :=
  ⟨sourceMap (polynomialProjection P a) ≫ vertices (laurentMinus P a) i,
    minusSourceIso P a ≪≫ isoWhiskerLeft (sourceMap (polynomialProjection P a)).functor
      (references (laurentMinus P a) i)⟩

theorem plus_top_first : plusSideNodes P a 5 = plusNodes P a 2 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso P a ≪≫ isoWhiskerLeft
    (sourceMap (polynomialProjection P a)).functor (leftFirst (laurentPlus P a))).hom =
    (plusSourceIso P a ≪≫ isoWhiskerRight (rightFirst (polynomialProjection P a))
      (sourceMap (laurentPlus P a)).functor).hom
  rw [shared_first]

theorem minus_top_first : minusSideNodes P a 5 = minusNodes P a 2 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso P a ≪≫ isoWhiskerLeft
    (sourceMap (polynomialProjection P a)).functor (leftFirst (laurentMinus P a))).hom =
    (minusSourceIso P a ≪≫ isoWhiskerRight (rightFirst (polynomialProjection P a))
      (sourceMap (laurentMinus P a)).functor).hom
  rw [shared_first]

theorem plus_top_intermediate : plusSideNodes P a 6 = plusNodes P a 3 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso P a ≪≫ isoWhiskerLeft
    (sourceMap (polynomialProjection P a)).functor
    (leftFirst (laurentPlus P a) ≪≫ leftSecondGeometric (laurentPlus P a))).hom =
    (plusSourceIso P a ≪≫ isoWhiskerRight
      (rightFirst (polynomialProjection P a) ≪≫
        rightSecondGeometric (polynomialProjection P a))
      (sourceMap (laurentPlus P a)).functor).hom
  simp only [isoWhiskerLeft_trans, isoWhiskerRight_trans, shared_first, shared_geometric]

theorem minus_top_intermediate : minusSideNodes P a 6 = minusNodes P a 3 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso P a ≪≫ isoWhiskerLeft
    (sourceMap (polynomialProjection P a)).functor
    (leftFirst (laurentMinus P a) ≪≫ leftSecondGeometric (laurentMinus P a))).hom =
    (minusSourceIso P a ≪≫ isoWhiskerRight
      (rightFirst (polynomialProjection P a) ≪≫
        rightSecondGeometric (polynomialProjection P a))
      (sourceMap (laurentMinus P a)).functor).hom
  simp only [isoWhiskerLeft_trans, isoWhiskerRight_trans, shared_first, shared_geometric]

theorem plus_top_target : plusSideNodes P a 7 = plusNodes P a 7 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso P a ≪≫ isoWhiskerLeft
    (sourceMap (polynomialProjection P a)).functor
    (rightFirst (laurentPlus P a) ≪≫ rightSecond (laurentPlus P a))).hom =
    (plusSourceIso P a ≪≫ isoWhiskerRight
      (rightFirst (polynomialProjection P a) ≪≫ rightSecond (polynomialProjection P a))
      (sourceMap (laurentPlus P a)).functor).hom
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, right_route_identity,
    whiskerLeft_id', whiskerRight_id']

theorem minus_top_target : minusSideNodes P a 7 = minusNodes P a 7 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso P a ≪≫ isoWhiskerLeft
    (sourceMap (polynomialProjection P a)).functor
    (rightFirst (laurentMinus P a) ≪≫ rightSecond (laurentMinus P a))).hom =
    (minusSourceIso P a ≪≫ isoWhiskerRight
      (rightFirst (polynomialProjection P a) ≪≫ rightSecond (polynomialProjection P a))
      (sourceMap (laurentMinus P a)).functor).hom
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, right_route_identity,
    whiskerLeft_id', whiskerRight_id']

/-- The unchanged top reference maps to the actual projection by the original base identity. -/
def sourceToProjection : (source P a).functor ≅ (BassProjectionPath.source P a).functor :=
  isoWhiskerRight (unitFirst (space (op P, a)) ≪≫ unitSecond (space (op P, a)))
    (BassProjectionPath.source P a).functor

private theorem map_identity_comp {V W : Model.{u}} (F : V ⥤ W)
    (X : V) {Y : W} (η : F.obj X ⟶ Y) : F.map (𝟙 X) ≫ η = η :=
  (congrArg (fun f ↦ f ≫ η) (F.map_id X)).trans (Category.id_comp η)

private theorem middle_initial_reference (j : Fin 5) :
    productReference P a 0 j =
      isoWhiskerLeft (unitSourceMap (space (op P, a))).functor
        (BassProjectionPath.nodes P a j).2 := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (BassProjectionPath.source P a).functor.map
      (𝟙 ((unitSourceMap (space (op P, a))).functor.obj X)) ≫
    (BassProjectionPath.nodes P a j).2.hom.app
      ((unitSourceMap (space (op P, a))).functor.obj X) =
    (BassProjectionPath.nodes P a j).2.hom.app
      ((unitSourceMap (space (op P, a))).functor.obj X)
  exact map_identity_comp _ _ _

/-- The positive anchor is the same actual projection reference, followed by its chart total. -/
theorem plus_anchor : plusSourceIso P a =
    sourceToProjection P a ≪≫ (BassProjectionPath.nodes P a 2).2 := by
  change productReference P a 0 2 ≪≫
    (isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentPlus P a)).functor).symm = _
  exact (congrArg (fun ρ ↦ ρ ≪≫
    (isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentPlus P a)).functor).symm)
    (middle_initial_reference P a 2)).trans (chart_anchor _ _ _ _)

/-- The inverse anchor uses that identical projection reference and its transported chart total. -/
theorem minus_anchor : minusSourceIso P a =
    sourceToProjection P a ≪≫ (BassProjectionPath.nodes P a 4).2 := by
  change productReference P a 0 4 ≪≫
    (isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentMinus P a)).functor).symm = _
  exact (congrArg (fun ρ ↦ ρ ≪≫
    (isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentMinus P a)).functor).symm)
    (middle_initial_reference P a 4)).trans (chart_anchor _ _ _ _)

/-- The native reference of the projection by Laurent identity product. -/
abbrev bottomSource := BassProjectionPath.source P a ≫
  unitSourceMap (space (op P, (laurentUnderFunctor R).obj a))

/-- Change the reference of the entire product using both actual geometric unit isomorphisms. -/
def bottomSourceIso : (source P a).functor ≅ (bottomSource P a).functor :=
  sourceToProjection P a ≪≫
    (isoWhiskerLeft (BassProjectionPath.source P a).functor
      (unitFirst (space (op P, (laurentUnderFunctor R).obj a)) ≪≫
        unitSecond (space (op P, (laurentUnderFunctor R).obj a)))).symm

/-- Every original bottom product node, including its true product reference transformation. -/
def bottomNodes (i : Fin 15) : Node P a :=
  ⟨CommonReferenceProduct.vertices (fun j ↦ (BassProjectionPath.nodes P a j).1)
      (CoefficientPolynomialSpanUnitSimplex.identityVertices
        (space (op P, (laurentUnderFunctor R).obj a))) i,
    bottomSourceIso P a ≪≫ CommonReferenceProduct.references (BassProjectionPath.source P a)
      (fun j ↦ (BassProjectionPath.nodes P a j).1) (fun j ↦ (BassProjectionPath.nodes P a j).2)
      (unitSourceMap (space (op P, (laurentUnderFunctor R).obj a)))
      (CoefficientPolynomialSpanUnitSimplex.identityVertices
        (space (op P, (laurentUnderFunctor R).obj a)))
      (CoefficientPolynomialSpanUnitSimplex.identityReferences
        (space (op P, (laurentUnderFunctor R).obj a))) i⟩

/-- Reanchoring preserves the full original bottom product family before restricting support. -/
theorem bottom_family :
    ModelSimplex.ofIsos (source P a) (fun i ↦ (bottomNodes P a i).1)
      (fun i ↦ (bottomNodes P a i).2) =
      CommonReferenceProduct.simplex (BassProjectionPath.source P a)
        (fun j ↦ (BassProjectionPath.nodes P a j).1)
        (fun j ↦ (BassProjectionPath.nodes P a j).2)
        (unitSourceMap (space (op P, (laurentUnderFunctor R).obj a)))
        (CoefficientPolynomialSpanUnitSimplex.identityVertices
          (space (op P, (laurentUnderFunctor R).obj a)))
        (CoefficientPolynomialSpanUnitSimplex.identityReferences
          (space (op P, (laurentUnderFunctor R).obj a))) :=
  ModelSimplex.ofIsos_change_reference (bottomSourceIso P a) _ _

/-- The original bottom reference at an explicit pair of product vertices. -/
def bottomPairReference (j : Fin 5) (k : Fin 3) : (source P a).functor ≅
    ((BassProjectionPath.nodes P a j).1 ≫
      CoefficientPolynomialSpanUnitSimplex.identityVertices
        (space (op P, (laurentUnderFunctor R).obj a)) k).functor :=
  bottomSourceIso P a ≪≫ (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
    ((BassProjectionPath.nodes P a j).2.prod
      (CoefficientPolynomialSpanUnitSimplex.identityReferences
        (space (op P, (laurentUnderFunctor R).obj a)) k))

/-- Naturality retains both original identity-normalization steps of the bottom reference. -/
theorem bottom_pair_reference (j : Fin 5) (k : Fin 3) :
    bottomPairReference P a j k =
      (sourceToProjection P a ≪≫ (BassProjectionPath.nodes P a j).2) ≪≫
        isoWhiskerLeft (BassProjectionPath.nodes P a j).1.functor
          ((unitFirst (space (op P, (laurentUnderFunctor R).obj a)) ≪≫
              unitSecond (space (op P, (laurentUnderFunctor R).obj a))).symm ≪≫
            CoefficientPolynomialSpanUnitSimplex.identityReferences
              (space (op P, (laurentUnderFunctor R).obj a)) k) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  let τ := unitFirst (space (op P, (laurentUnderFunctor R).obj a)) ≪≫
    unitSecond (space (op P, (laurentUnderFunctor R).obj a))
  let σ := (BassProjectionPath.nodes P a j).2
  let ρ := CoefficientPolynomialSpanUnitSimplex.identityReferences
    (space (op P, (laurentUnderFunctor R).obj a)) k
  change ((sourceToProjection P a).hom.app X ≫
      τ.inv.app ((BassProjectionPath.source P a).functor.obj X)) ≫
      ((unitSourceMap (space (op P, (laurentUnderFunctor R).obj a))).functor.map
          (σ.hom.app X) ≫ ρ.hom.app ((BassProjectionPath.nodes P a j).1.functor.obj X)) =
    ((sourceToProjection P a).hom.app X ≫ σ.hom.app X) ≫
      (τ.inv.app ((BassProjectionPath.nodes P a j).1.functor.obj X) ≫
        ρ.hom.app ((BassProjectionPath.nodes P a j).1.functor.obj X))
  simp only [Category.assoc]
  rw [← τ.inv.naturality_assoc]
  rfl

/-- The row-major product enumeration preserves its actual entire dependent reference node. -/
theorem bottom_pair (j : Fin 5) (k : Fin 3) :
    bottomNodes P a (Quillen.SimplexGrid.index 4 2 (j, k)) =
      ⟨(BassProjectionPath.nodes P a j).1 ≫
        CoefficientPolynomialSpanUnitSimplex.identityVertices
          (space (op P, (laurentUnderFunctor R).obj a)) k,
        bottomPairReference P a j k⟩ := by
  exact congrArg (fun z : Fin 5 × Fin 3 ↦
    (⟨(BassProjectionPath.nodes P a z.1).1 ≫
      CoefficientPolynomialSpanUnitSimplex.identityVertices
        (space (op P, (laurentUnderFunctor R).obj a)) z.2,
      bottomPairReference P a z.1 z.2⟩ : Node P a))
    (Quillen.SimplexGrid.decode_index 4 2 (j, k))

/-- Every terminal bottom reference is the same actual projection reference followed by its node. -/
theorem bottom_terminal_reference (j : Fin 5) : bottomPairReference P a j 2 =
    sourceToProjection P a ≪≫ (BassProjectionPath.nodes P a j).2 := by
  rw [bottom_pair_reference]
  change _ ≪≫ isoWhiskerLeft _ ((_ ≪≫ _).symm ≪≫ (_ ≪≫ _)) = _
  simp

/-- The right unit is precisely the original Laurent identity, prewhiskered by pullback. -/
theorem right_second_total {A B : Scheme.{u}} (q : B ⟶ A) :
    rightSecond q = isoWhiskerLeft (sourceMap q).functor (unitFirst B ≪≫ unitSecond B) := by
  apply Iso.ext
  rw [← right_second_composite]
  simp only [isoWhiskerLeft_hom, Iso.trans_hom, whiskerLeft_comp]
  rfl

/-- The split geometric right-unit step is the original first identity transformation. -/
theorem right_geometric_total {A B : Scheme.{u}} (q : B ⟶ A) :
    rightSecondGeometric q = isoWhiskerLeft (sourceMap q).functor (unitFirst B) := rfl

theorem plus_bottom_first : plusSideNodes P a 2 = bottomNodes P a 6 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso P a ≪≫ isoWhiskerLeft
    (sourceMap (polynomialProjection P a)).functor (rightFirst (laurentPlus P a))).hom =
      (bottomPairReference P a 2 0).hom
  rw [right_first_inverse, right_second_total, bottom_pair_reference, plus_anchor]
  simp only [CoefficientPolynomialSpanUnitSimplex.identityReferences, Fin.cases_zero,
    Iso.trans_refl]
  rfl

theorem minus_bottom_first : minusSideNodes P a 2 = bottomNodes P a 12 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso P a ≪≫ isoWhiskerLeft
    (sourceMap (polynomialProjection P a)).functor (rightFirst (laurentMinus P a))).hom =
      (bottomPairReference P a 4 0).hom
  rw [right_first_inverse, right_second_total, bottom_pair_reference, minus_anchor]
  simp only [CoefficientPolynomialSpanUnitSimplex.identityReferences, Fin.cases_zero,
    Iso.trans_refl]
  rfl

theorem plus_bottom_intermediate : plusSideNodes P a 3 = bottomNodes P a 7 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso P a ≪≫ isoWhiskerLeft
    (sourceMap (polynomialProjection P a)).functor
    (rightFirst (laurentPlus P a) ≪≫ rightSecondGeometric (laurentPlus P a))).hom =
      (bottomPairReference P a 2 1).hom
  rw [right_first_inverse, right_second_total, right_geometric_total,
    bottom_pair_reference, plus_anchor]
  rfl

theorem minus_bottom_intermediate : minusSideNodes P a 3 = bottomNodes P a 13 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso P a ≪≫ isoWhiskerLeft
    (sourceMap (polynomialProjection P a)).functor
    (rightFirst (laurentMinus P a) ≪≫ rightSecondGeometric (laurentMinus P a))).hom =
      (bottomPairReference P a 4 1).hom
  rw [right_first_inverse, right_second_total, right_geometric_total,
    bottom_pair_reference, minus_anchor]
  rfl

theorem plus_bottom_target : plusSideNodes P a 7 = bottomNodes P a 8 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso P a ≪≫ isoWhiskerLeft
    (sourceMap (polynomialProjection P a)).functor
    (rightFirst (laurentPlus P a) ≪≫ rightSecond (laurentPlus P a))).hom =
      (bottomPairReference P a 2 2).hom
  rw [bottom_terminal_reference, ← plus_anchor]
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, right_route_identity,
    whiskerLeft_id']
  exact Category.comp_id _

theorem minus_bottom_target : minusSideNodes P a 7 = bottomNodes P a 14 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso P a ≪≫ isoWhiskerLeft
    (sourceMap (polynomialProjection P a)).functor
    (rightFirst (laurentMinus P a) ≪≫ rightSecond (laurentMinus P a))).hom =
      (bottomPairReference P a 4 2).hom
  rw [bottom_terminal_reference, ← minus_anchor]
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, right_route_identity,
    whiskerLeft_id']
  exact Category.comp_id _

/-- All five terminal projection vertices share their complete original references. -/
theorem terminal_nodes (j : Fin 5) :
    bottomNodes P a (Quillen.SimplexGrid.index 4 2 (j, 2)) =
      middleNodes P a (Quillen.SimplexGrid.index 2 4 (2, j)) := by
  rw [bottom_pair, middle_pair]
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  rw [bottom_terminal_reference]
  rfl

/-- The whole positive side is the original unit square with its actual polynomial premap. -/
theorem plus_side_family :
    ModelSimplex.ofIsos (source P a) (fun i ↦ (plusSideNodes P a i).1)
      (fun i ↦ (plusSideNodes P a i).2) =
      (OriginalUnitSquareSimplex.simplex (laurentPlus P a)).precomp
        (sourceMap (polynomialProjection P a)) := by
  change ModelSimplex.ofIsos (source P a)
    (fun i ↦ sourceMap (polynomialProjection P a) ≫ vertices (laurentPlus P a) i)
    (fun i ↦ plusSourceIso P a ≪≫
      isoWhiskerLeft (sourceMap (polynomialProjection P a)).functor
        (references (laurentPlus P a) i)) = _
  rw [ModelSimplex.ofIsos_change_reference]
  exact (ModelSimplex.ofIsos_precomp _ _ _ _).symm

/-- The entire inverse side keeps its separate original chart and unchanged polynomial premap. -/
theorem minus_side_family :
    ModelSimplex.ofIsos (source P a) (fun i ↦ (minusSideNodes P a i).1)
      (fun i ↦ (minusSideNodes P a i).2) =
      (OriginalUnitSquareSimplex.simplex (laurentMinus P a)).precomp
        (sourceMap (polynomialProjection P a)) := by
  change ModelSimplex.ofIsos (source P a)
    (fun i ↦ sourceMap (polynomialProjection P a) ≫ vertices (laurentMinus P a) i)
    (fun i ↦ minusSourceIso P a ≪≫
      isoWhiskerLeft (sourceMap (polynomialProjection P a)).functor
        (references (laurentMinus P a) i)) = _
  rw [ModelSimplex.ofIsos_change_reference]
  exact (ModelSimplex.ofIsos_precomp _ _ _ _).symm

/-- All positive top joins are full node equalities, including the normalization intermediate. -/
theorem plus_top_nodes (i : Fin 3) : plusSideNodes P a (![5, 6, 7] i) =
    plusNodes P a (![2, 3, 7] i) := by
  fin_cases i
  · exact plus_top_first P a
  · exact plus_top_intermediate P a
  · exact plus_top_target P a

/-- All inverse-chart top joins retain their actual full dependent references. -/
theorem minus_top_nodes (i : Fin 3) : minusSideNodes P a (![5, 6, 7] i) =
    minusNodes P a (![2, 3, 7] i) := by
  fin_cases i
  · exact minus_top_first P a
  · exact minus_top_intermediate P a
  · exact minus_top_target P a

/-- The positive Laurent identity edge agrees with its original bottom product column. -/
theorem plus_bottom_nodes (i : Fin 3) : plusSideNodes P a (![2, 3, 7] i) =
    bottomNodes P a (![6, 7, 8] i) := by
  fin_cases i
  · exact plus_bottom_first P a
  · exact plus_bottom_intermediate P a
  · exact plus_bottom_target P a

/-- The inverse Laurent identity edge agrees with its separate original bottom column. -/
theorem minus_bottom_nodes (i : Fin 3) : minusSideNodes P a (![2, 3, 7] i) =
    bottomNodes P a (![12, 13, 14] i) := by
  fin_cases i
  · exact minus_bottom_first P a
  · exact minus_bottom_intermediate P a
  · exact minus_bottom_target P a

end Quillen.PerfectComplexes.CoefficientBassUnitBoundaryNodes
