/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialSpanUnitSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNodeTransport

/-! The shared dependent nodes of the two original polynomial unit squares and the
independently parametrized identity/Bass grid. References retain the actual transformations. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientPolynomialSpanUnitNodes
open OriginalUnitSquareSimplex CoefficientPolynomialSpanUnitSimplex
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The unchanged reference of the literal product grid. -/
abbrev source := unitSourceMap (space (op P, a)) ≫ BassProjectionPath.source P a

abbrev Node := Σ F : modelOf (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
    modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a))), (source P a).functor ≅ F.functor

/-- All fifteen original product nodes, with their original product references. -/
def middleNodes (i : Fin 15) : Node P a :=
  ⟨CommonReferenceProduct.vertices (identityVertices (space (op P, a)))
      (fun j ↦ (BassProjectionPath.nodes P a j).1) i,
    CommonReferenceProduct.references (unitSourceMap (space (op P, a)))
      (identityVertices (space (op P, a))) (identityReferences (space (op P, a)))
      (BassProjectionPath.source P a) (fun j ↦ (BassProjectionPath.nodes P a j).1)
      (fun j ↦ (BassProjectionPath.nodes P a j).2) i⟩

/-- The positive square changes reference through its actual shared initial identity node. -/
def plusSourceIso : (source P a).functor ≅
    (sourceMap (polynomialProjection P a) ≫ sourceMap (laurentPlus P a)).functor :=
  (middleNodes P a 2).2 ≪≫
    (isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentPlus P a)).functor).symm

/-- The negative square uses the actual inverse-chart node, including its source transport. -/
def minusSourceIso : (source P a).functor ≅
    (sourceMap (polynomialProjection P a) ≫ sourceMap (laurentMinus P a)).functor :=
  (middleNodes P a 4).2 ≪≫
    (isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentMinus P a)).functor).symm

/-- Every positive vertex and its original reference, whiskered by the positive chart. -/
def plusNodes (i : Fin 8) : Node P a :=
  ⟨vertices (polynomialProjection P a) i ≫ sourceMap (laurentPlus P a),
    plusSourceIso P a ≪≫ isoWhiskerRight (references (polynomialProjection P a) i)
      (sourceMap (laurentPlus P a)).functor⟩

/-- Every negative vertex and its original reference, whiskered by the negative chart. -/
def minusNodes (i : Fin 8) : Node P a :=
  ⟨vertices (polynomialProjection P a) i ≫ sourceMap (laurentMinus P a),
    minusSourceIso P a ≪≫ isoWhiskerRight (references (polynomialProjection P a) i)
      (sourceMap (laurentMinus P a)).functor⟩

theorem plus_five : plusNodes P a 5 = middleNodes P a 2 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (((middleNodes P a 2).2 ≪≫
    (isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentPlus P a)).functor).symm) ≪≫
    isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentPlus P a)).functor).hom = (middleNodes P a 2).2.hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem minus_five : minusNodes P a 5 = middleNodes P a 4 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (((middleNodes P a 4).2 ≪≫
    (isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentMinus P a)).functor).symm) ≪≫
    isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentMinus P a)).functor).hom = (middleNodes P a 4).2.hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The literal pair of references before enumerating the product grid. -/
def productReference (i : Fin 3) (j : Fin 5) : (source P a).functor ≅
    (identityVertices (space (op P, a)) i ≫ (BassProjectionPath.nodes P a j).1).functor :=
  (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
    ((identityReferences (space (op P, a)) i).prod (BassProjectionPath.nodes P a j).2)

private theorem reference_naturality {V W : Model.{u}} {F G : V ⥤ W}
    (ρ : F ≅ G) {X Y : V} (η : X ⟶ Y) :
    F.map η ≫ ρ.hom.app Y = (F.map (𝟙 X) ≫ ρ.hom.app X) ≫ G.map η := by
  exact (ρ.hom.naturality η).trans
    ((congrArg (fun α ↦ (α ≫ ρ.hom.app X) ≫ G.map η) (F.map_id X)).trans
      (congrArg (fun α ↦ α ≫ G.map η) (Category.id_comp (ρ.hom.app X)))).symm

/-- Naturality of the actual Bass reference moves the identity reference to the right. -/
theorem product_reference (i : Fin 3) (j : Fin 5) :
    productReference P a i j = productReference P a 0 j ≪≫
      isoWhiskerRight (identityReferences (space (op P, a)) i)
        (BassProjectionPath.nodes P a j).1.functor := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (BassProjectionPath.source P a).functor.map
      ((identityReferences (space (op P, a)) i).hom.app X) ≫
      (BassProjectionPath.nodes P a j).2.hom.app
        ((identityVertices (space (op P, a)) i).functor.obj X) =
    ((BassProjectionPath.source P a).functor.map (𝟙 _) ≫
      (BassProjectionPath.nodes P a j).2.hom.app ((unitSourceMap _).functor.obj X)) ≫
      (BassProjectionPath.nodes P a j).1.functor.map
        ((identityReferences (space (op P, a)) i).hom.app X)
  exact reference_naturality (BassProjectionPath.nodes P a j).2
    ((identityReferences (space (op P, a)) i).hom.app X)

/-- Decoding a product index preserves the entire dependent node. -/
theorem middle_pair (i : Fin 3) (j : Fin 5) :
    middleNodes P a (Quillen.SimplexGrid.index 2 4 (i, j)) =
      ⟨identityVertices (space (op P, a)) i ≫ (BassProjectionPath.nodes P a j).1,
        productReference P a i j⟩ := by
  exact congrArg (fun z : Fin 3 × Fin 5 ↦
    (⟨identityVertices (space (op P, a)) z.1 ≫ (BassProjectionPath.nodes P a z.2).1,
      productReference P a z.1 z.2⟩ : Node P a))
    (Quillen.SimplexGrid.decode_index 2 4 (i, j))

theorem plus_six : plusNodes P a 6 = middleNodes P a 7 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso P a ≪≫ isoWhiskerRight
    (leftFirst (polynomialProjection P a) ≪≫ leftSecondGeometric (polynomialProjection P a))
    (sourceMap (laurentPlus P a)).functor).hom = (productReference P a 1 2).hom
  rw [product_reference]
  simp only [plusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv, whiskerRight_comp, Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rfl

theorem minus_six : minusNodes P a 6 = middleNodes P a 9 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso P a ≪≫ isoWhiskerRight
    (leftFirst (polynomialProjection P a) ≪≫ leftSecondGeometric (polynomialProjection P a))
    (sourceMap (laurentMinus P a)).functor).hom = (productReference P a 1 4).hom
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

theorem plus_seven : plusNodes P a 7 = middleNodes P a 12 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso P a ≪≫ isoWhiskerRight
    (rightFirst (polynomialProjection P a) ≪≫ rightSecond (polynomialProjection P a))
    (sourceMap (laurentPlus P a)).functor).hom = (productReference P a 2 2).hom
  rw [product_reference]
  simp only [plusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv]
  rw [two_routes, whiskerRight_comp]
  simp only [Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rw [left_second_whisker]
  rfl

theorem minus_seven : minusNodes P a 7 = middleNodes P a 14 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso P a ≪≫ isoWhiskerRight
    (rightFirst (polynomialProjection P a) ≪≫ rightSecond (polynomialProjection P a))
    (sourceMap (laurentMinus P a)).functor).hom = (productReference P a 2 4).hom
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
    plusNodes P a ⟨5 + i.val, by omega⟩ =
      middleNodes P a ⟨5 * i.val + 2, by omega⟩ := by
  fin_cases i
  · exact plus_five P a
  · exact plus_six P a
  · exact plus_seven P a

/-- All three negative shared vertices retain the actual inverse-chart reference. -/
theorem minus_shared (i : Fin 3) :
    minusNodes P a ⟨5 + i.val, by omega⟩ =
      middleNodes P a ⟨5 * i.val + 4, by omega⟩ := by
  fin_cases i
  · exact minus_five P a
  · exact minus_six P a
  · exact minus_seven P a

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
    ModelSimplex.ofIsos (source P a) (fun i ↦ (plusNodes P a i).1)
      (fun i ↦ (plusNodes P a i).2) = plusSimplex P a := by
  change ModelSimplex.ofIsos (source P a)
    (fun i ↦ vertices (polynomialProjection P a) i ≫ sourceMap (laurentPlus P a))
    (fun i ↦ plusSourceIso P a ≪≫ isoWhiskerRight (references (polynomialProjection P a) i)
      (sourceMap (laurentPlus P a)).functor) = _
  rw [ModelSimplex.ofIsos_change_reference]
  exact (postcomp_ofIsos _ _ _ _).symm

/-- Reanchoring preserves the entire original inverse-chart square simplex. -/
theorem minus_family :
    ModelSimplex.ofIsos (source P a) (fun i ↦ (minusNodes P a i).1)
      (fun i ↦ (minusNodes P a i).2) = minusSimplex P a := by
  change ModelSimplex.ofIsos (source P a)
    (fun i ↦ vertices (polynomialProjection P a) i ≫ sourceMap (laurentMinus P a))
    (fun i ↦ minusSourceIso P a ≪≫ isoWhiskerRight (references (polynomialProjection P a) i)
      (sourceMap (laurentMinus P a)).functor) = _
  rw [ModelSimplex.ofIsos_change_reference]
  exact (postcomp_ofIsos _ _ _ _).symm

/-- The middle family retains its original reference unchanged. -/
theorem middle_family :
    ModelSimplex.ofIsos (source P a) (fun i ↦ (middleNodes P a i).1)
      (fun i ↦ (middleNodes P a i).2) = middleSimplex P a := rfl

end Quillen.PerfectComplexes.CoefficientPolynomialSpanUnitNodes
