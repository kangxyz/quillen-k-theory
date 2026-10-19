/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityTopSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNodeTransport

/-!
# The actual shared nodes of the original global span identity

The original global scheme arrows and full reference data are used directly. Only the pure
scalar parameters are shared with the coefficient development; no coefficient model is identified.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentityTopNodes
open OriginalUnitSquareSimplex CoefficientPolynomialSpanUnitSimplex InputIdentityTopSimplex
variable (X : Scheme.{u})

/-- The unchanged reference of the literal product grid. -/
abbrev source := unitSourceMap X ≫ InputIdentityProjection.source X

/-- A model-map node with an isomorphism from the fixed product-grid reference. -/
abbrev Node := Σ F : modelOf (boundedFlatPerfectWaldhausen X) ⟶
    modelOf (boundedFlatPerfectWaldhausen
      (laurent.obj X)), (source X).functor ≅ F.functor

/-- All fifteen original product nodes, with their original product references. -/
def middleNodes (i : Fin 15) : Node X :=
  ⟨CommonReferenceProduct.vertices (identityVertices X)
      (fun j ↦ (InputIdentityProjection.nodes X j).1) i,
    CommonReferenceProduct.references (unitSourceMap X)
      (identityVertices X) (identityReferences X)
      (InputIdentityProjection.source X) (fun j ↦ (InputIdentityProjection.nodes X j).1)
      (fun j ↦ (InputIdentityProjection.nodes X j).2) i⟩

/-- The positive square changes reference through its actual shared initial identity node. -/
def plusSourceIso : (source X).functor ≅
    (sourceMap (projection.app X) ≫ sourceMap (plus.app X)).functor :=
  (middleNodes X 2).2 ≪≫
    (isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (plus.app X)).functor).symm

/-- The negative square uses the actual inverse-chart node, including its source transport. -/
def minusSourceIso : (source X).functor ≅
    (sourceMap (projection.app X) ≫ sourceMap (minus.app X)).functor :=
  (middleNodes X 4).2 ≪≫
    (isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (minus.app X)).functor).symm

/-- Every positive vertex and its original reference, whiskered by the positive chart. -/
def plusNodes (i : Fin 8) : Node X :=
  ⟨vertices (projection.app X) i ≫ sourceMap (plus.app X),
    plusSourceIso X ≪≫ isoWhiskerRight (references (projection.app X) i)
      (sourceMap (plus.app X)).functor⟩

/-- Every negative vertex and its original reference, whiskered by the negative chart. -/
def minusNodes (i : Fin 8) : Node X :=
  ⟨vertices (projection.app X) i ≫ sourceMap (minus.app X),
    minusSourceIso X ≪≫ isoWhiskerRight (references (projection.app X) i)
      (sourceMap (minus.app X)).functor⟩

theorem plus_five : plusNodes X 5 = middleNodes X 2 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (((middleNodes X 2).2 ≪≫
    (isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (plus.app X)).functor).symm) ≪≫
    isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (plus.app X)).functor).hom = (middleNodes X 2).2.hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem minus_five : minusNodes X 5 = middleNodes X 4 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (((middleNodes X 4).2 ≪≫
    (isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (minus.app X)).functor).symm) ≪≫
    isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (minus.app X)).functor).hom = (middleNodes X 4).2.hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The literal pair of references before enumerating the product grid. -/
def productReference (i : Fin 3) (j : Fin 5) : (source X).functor ≅
    (identityVertices X i ≫ (InputIdentityProjection.nodes X j).1).functor :=
  (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
    ((identityReferences X i).prod (InputIdentityProjection.nodes X j).2)

private theorem reference_naturality {V W : Model.{u}} {F G : V ⥤ W}
    (ρ : F ≅ G) {X Y : V} (η : X ⟶ Y) :
    F.map η ≫ ρ.hom.app Y = (F.map (𝟙 X) ≫ ρ.hom.app X) ≫ G.map η := by
  exact (ρ.hom.naturality η).trans
    ((congrArg (fun α ↦ (α ≫ ρ.hom.app X) ≫ G.map η) (F.map_id X)).trans
      (congrArg (fun α ↦ α ≫ G.map η) (Category.id_comp (ρ.hom.app X)))).symm

/-- Naturality of the actual Bass reference moves the identity reference to the right. -/
theorem product_reference (i : Fin 3) (j : Fin 5) :
    productReference X i j = productReference X 0 j ≪≫
      isoWhiskerRight (identityReferences X i)
        (InputIdentityProjection.nodes X j).1.functor := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  change (InputIdentityProjection.source X).functor.map
      ((identityReferences X i).hom.app A) ≫
      (InputIdentityProjection.nodes X j).2.hom.app
        ((identityVertices X i).functor.obj A) =
    ((InputIdentityProjection.source X).functor.map (𝟙 _) ≫
      (InputIdentityProjection.nodes X j).2.hom.app ((unitSourceMap _).functor.obj A)) ≫
      (InputIdentityProjection.nodes X j).1.functor.map
        ((identityReferences X i).hom.app A)
  exact reference_naturality (InputIdentityProjection.nodes X j).2
    ((identityReferences X i).hom.app A)

/-- Decoding a product index preserves the entire dependent node. -/
theorem middle_pair (i : Fin 3) (j : Fin 5) :
    middleNodes X (Quillen.SimplexGrid.index 2 4 (i, j)) =
      ⟨identityVertices X i ≫ (InputIdentityProjection.nodes X j).1,
        productReference X i j⟩ := by
  exact congrArg (fun z : Fin 3 × Fin 5 ↦
    (⟨identityVertices X z.1 ≫ (InputIdentityProjection.nodes X z.2).1,
      productReference X z.1 z.2⟩ : Node X))
    (Quillen.SimplexGrid.decode_index 2 4 (i, j))

theorem plus_six : plusNodes X 6 = middleNodes X 7 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso X ≪≫ isoWhiskerRight
    (leftFirst (projection.app X) ≪≫ leftSecondGeometric (projection.app X))
    (sourceMap (plus.app X)).functor).hom = (productReference X 1 2).hom
  rw [product_reference]
  simp only [plusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv, whiskerRight_comp, Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rfl

theorem minus_six : minusNodes X 6 = middleNodes X 9 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso X ≪≫ isoWhiskerRight
    (leftFirst (projection.app X) ≪≫ leftSecondGeometric (projection.app X))
    (sourceMap (minus.app X)).functor).hom = (productReference X 1 4).hom
  rw [product_reference]
  simp only [minusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv, whiskerRight_comp, Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rfl

private theorem left_second_whisker {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    whiskerRight (leftSecond p).hom (sourceMap q).functor =
      whiskerRight ((unitFirst A).hom ≫ (unitSecond A).hom)
        (sourceMap p ≫ sourceMap q).functor := by
  rw [← left_second_composite]
  simp only [whiskerRight_comp]
  rfl

theorem plus_seven : plusNodes X 7 = middleNodes X 12 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso X ≪≫ isoWhiskerRight
    (rightFirst (projection.app X) ≪≫ rightSecond (projection.app X))
    (sourceMap (plus.app X)).functor).hom = (productReference X 2 2).hom
  rw [product_reference]
  simp only [plusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv]
  rw [two_routes, whiskerRight_comp]
  simp only [Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rw [left_second_whisker]
  rfl

theorem minus_seven : minusNodes X 7 = middleNodes X 14 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso X ≪≫ isoWhiskerRight
    (rightFirst (projection.app X) ≪≫ rightSecond (projection.app X))
    (sourceMap (minus.app X)).functor).hom = (productReference X 2 4).hom
  rw [product_reference]
  simp only [minusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv]
  rw [two_routes, whiskerRight_comp]
  simp only [Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rw [left_second_whisker]
  rfl

/-- All three positive shared vertices agree as dependent nodes, including reference transport. -/
theorem plus_shared (i : Fin 3) :
    plusNodes X ⟨5 + i.val, by omega⟩ =
      middleNodes X ⟨5 * i.val + 2, by omega⟩ := by
  fin_cases i
  · exact plus_five X
  · exact plus_six X
  · exact plus_seven X

/-- All three negative shared vertices retain the actual inverse-chart reference. -/
theorem minus_shared (i : Fin 3) :
    minusNodes X ⟨5 + i.val, by omega⟩ =
      middleNodes X ⟨5 * i.val + 4, by omega⟩ := by
  fin_cases i
  · exact minus_five X
  · exact minus_six X
  · exact minus_seven X

private theorem postcomp_ofIsos {V W T : Model.{u}} {k : ℕ}
    (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (F i).functor) (J : W ⟶ T) :
    (ModelSimplex.ofIsos F₀ F ρ).postcomp J =
      ModelSimplex.ofIsos (F₀ ≫ J) (fun i ↦ F i ≫ J)
        (fun i ↦ isoWhiskerRight (ρ i) J.functor) := by
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro i j f
  apply heq_of_eq
  exact whiskerRight_comp _ _ _

/-- Reanchoring preserves the entire original positive square simplex. -/
theorem plus_family :
    ModelSimplex.ofIsos (source X) (fun i ↦ (plusNodes X i).1)
      (fun i ↦ (plusNodes X i).2) = plusSimplex X := by
  change ModelSimplex.ofIsos (source X)
    (fun i ↦ vertices (projection.app X) i ≫ sourceMap (plus.app X))
    (fun i ↦ plusSourceIso X ≪≫ isoWhiskerRight (references (projection.app X) i)
      (sourceMap (plus.app X)).functor) = _
  rw [ModelSimplex.ofIsos_change_reference]
  exact (postcomp_ofIsos _ _ _ _).symm

/-- Reanchoring preserves the entire original inverse-chart square simplex. -/
theorem minus_family :
    ModelSimplex.ofIsos (source X) (fun i ↦ (minusNodes X i).1)
      (fun i ↦ (minusNodes X i).2) = minusSimplex X := by
  change ModelSimplex.ofIsos (source X)
    (fun i ↦ vertices (projection.app X) i ≫ sourceMap (minus.app X))
    (fun i ↦ minusSourceIso X ≪≫ isoWhiskerRight (references (projection.app X) i)
      (sourceMap (minus.app X)).functor) = _
  rw [ModelSimplex.ofIsos_change_reference]
  exact (postcomp_ofIsos _ _ _ _).symm

/-- The middle family retains its original reference unchanged. -/
theorem middle_family :
    ModelSimplex.ofIsos (source X) (fun i ↦ (middleNodes X i).1)
      (fun i ↦ (middleNodes X i).2) = middleSimplex X := rfl


end Quillen.PerfectComplexes.GlobalRawBass.InputIdentityTopNodes
