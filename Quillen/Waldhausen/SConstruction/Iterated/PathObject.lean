/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.Prespectrum
public import Quillen.Waldhausen.SConstruction.Iterated.RelativeCylinder
public import Quillen.Topology.Realization.BisimplicialContractibility
public import Quillen.Waldhausen.Fibration.AllWeak.Basic

/-!
# Actual path objects at every finite iterated S-stage

All stages are connected, and all stages of an all-weak category are contractible. The
added-initial-row construction has an explicit ordinal-clamping simplicial homotopy from
its augmentation-section composite to identity. Its target is the genuine zero-row stage,
whose contractibility is proved. Consequently every displayed higher path object is genuinely
contractible, without assuming any higher Omega-equivalence.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS

/-- Every actual higher S-realization is connected, with no Omega-equivalence premise. -/
theorem stageSpace_pathConnected (r : ℕ) (W : Model.{u}) : PathConnectedSpace (stageSpace r W) := by
  induction r generalizing W with
  | zero => exact inferInstanceAs (PathConnectedSpace W.waldhausen.Delooping)
  | succ r ih =>
    let : PathConnectedSpace |(rowDiagram W ⋙ stages r).obj (op ⦋0⦌)| :=
      ih ((rows ⦋0⦌).obj W)
    exact diagonal_pathConnected_of_zero_row (rowDiagram W ⋙ stages r)


/-- An all-weak original structure has a genuine S-contraction. -/
theorem initialS_contractible_of_all_weak (W : Model.{u})
    (h : ∀ ⦃A B : W⦄ (f : A ⟶ B), W.waldhausen.weq f) :
    ContractibleSpace (stageSpace 0 W) := by
  let η : zeroFunctor W.waldhausen ⟶ 𝟭 W := {
    app A := W.waldhausen.isZero.to_ A
    naturality _ _ _ := W.waldhausen.isZero.eq_of_src _ _ }
  let H := weakNaturalTransformationRealizationHomotopy W.waldhausen W.waldhausen
    (zeroFunctor_isExact _ _) (IsExact.id _ _) η (fun A ↦ h (η.app A))
  apply (contractible_iff_id_nullhomotopic _).2
  refine ⟨W.waldhausen.kBasepoint, ?_⟩
  have hc : (deloopingMap (zeroFunctor_isExact W.waldhausen W.waldhausen)).hom =
      ContinuousMap.const W.waldhausen.Delooping W.waldhausen.kBasepoint :=
    deloopingMap_zeroFunctor _ _
  have hi : (deloopingMap (IsExact.id W.waldhausen.cof W.waldhausen.weq)).hom =
      ContinuousMap.id W.waldhausen.Delooping := ExtensionCategory.deloopingMap_identity _
  rw [hc, hi] at H
  exact ⟨H.symm⟩

/-- All finite stages of an all-weak original category are actually contractible. -/
theorem stageSpace_contractible_of_all_weak (r : ℕ) (W : Model.{u})
    (h : ∀ ⦃A B : W⦄ (f : A ⟶ B), W.waldhausen.weq f) :
    ContractibleSpace (stageSpace r W) := by
  induction r generalizing W with
  | zero => exact initialS_contractible_of_all_weak W h
  | succ r ih =>
    apply diagonal_contractible_of_rows (rowDiagram W ⋙ stages r)
    intro n
    exact ih ((rows n).obj W) (fun {A B} f p ↦ h (f.hom.app p))

open Fibration.RelativeRows

/-- Contract the added initial segment, retaining the actual remaining ordinal vertices. -/
def pathClamp {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) : addInitial.obj n ⟶ addInitial.obj n :=
  SimplexCategory.Hom.mk {
    toFun := Fin.cases 0 (fun i ↦ if τ.toOrderHom i = 0 then 0 else i.succ)
    monotone' := by
      intro i j hij
      cases i using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ i =>
        cases j using Fin.cases with
        | zero => have h : i.val + 1 ≤ 0 := hij; omega
        | succ j =>
          have h : i ≤ j := Nat.le_of_succ_le_succ hij
          by_cases hi : τ.toOrderHom i = 0
          · simp only [Fin.cases_succ, hi, ite_true]; exact Fin.zero_le _
          · have hj : τ.toOrderHom j ≠ 0 := by
              intro hj
              have hm := τ.toOrderHom.monotone h
              rw [hj] at hm
              exact hi (Fin.le_zero_iff.mp hm)
            simp only [Fin.cases_succ, hi, hj, ite_false, Fin.succ_le_succ_iff]
            exact h }

lemma pathClamp_naturality {m n : SimplexCategory} (α : m ⟶ n) (τ : n ⟶ ⦋1⦌) :
    pathClamp (α ≫ τ) ≫ addInitial.map α = addInitial.map α ≫ pathClamp τ := by
  ext i : 3
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    change (Fin.cases (motive := fun _ : Fin (m.len + 2) ↦ Fin (n.len + 2)) (0 : Fin (n.len +
      2)) (fun j ↦ (α.toOrderHom j).succ))
      (if τ.toOrderHom (α.toOrderHom i) = 0 then 0 else i.succ) =
      if τ.toOrderHom (α.toOrderHom i) = 0 then 0 else (α.toOrderHom i).succ
    split <;> rfl

lemma pathClamp_zero (n : SimplexCategory) :
    pathClamp (n.const ⦋1⦌ 0) = (addInitial.obj n).const (addInitial.obj n) 0 := by
  ext i : 3
  cases i using Fin.cases <;> rfl

lemma pathClamp_one (n : SimplexCategory) : pathClamp (n.const ⦋1⦌ 1) = 𝟙 (addInitial.obj n) := by
  ext i : 3
  cases i using Fin.cases <;> rfl

open Fibration.RelativeRows

/-- The row diagram augmented by an initial simplicial vertex. -/
def pathDiagram (W : Model.{u}) : SimplexCategoryᵒᵖ ⥤ Model.{u} :=
  addInitial.op ⋙ rowDiagram W

/-- The natural projection from the path diagram to the constant zero-ordinal row. -/
def pathAugmentation (W : Model.{u}) : pathDiagram W ⟶
    (Functor.const _).obj ((rows ⦋0⦌).obj W) where
  app n := (rowsReindex (⦋0⦌.const (addInitial.obj n.unop) 0)).app W
  naturality n m α := by
    apply Model.Hom.ext
    change QuotientRows.reindex W.waldhausen (addInitial.map α.unop) ⋙
      QuotientRows.reindex W.waldhausen (⦋0⦌.const (addInitial.obj m.unop) 0) =
      QuotientRows.reindex W.waldhausen (⦋0⦌.const (addInitial.obj n.unop) 0) ⋙ 𝟭 _
    rw [CategoryTheory.Functor.comp_id, ← QuotientRows.reindex_comp]
    congr 1

/-- The natural constant-row section of the path augmentation. -/
def pathSection (W : Model.{u}) : (Functor.const _).obj ((rows ⦋0⦌).obj W) ⟶ pathDiagram W where
  app n := (rowsReindex ((addInitial.obj n.unop).const ⦋0⦌ 0)).app W
  naturality n m α := by
    apply Model.Hom.ext
    change 𝟭 _ ⋙ QuotientRows.reindex W.waldhausen ((addInitial.obj m.unop).const ⦋0⦌ 0) =
      QuotientRows.reindex W.waldhausen ((addInitial.obj n.unop).const ⦋0⦌ 0) ⋙
        QuotientRows.reindex W.waldhausen (addInitial.map α.unop)
    rw [CategoryTheory.Functor.id_comp, ← QuotientRows.reindex_comp]
    congr 1

lemma pathSection_augmentation (W : Model.{u}) : pathSection W ≫ pathAugmentation W = 𝟙 _ := by
  ext n : 1
  apply Model.Hom.ext
  change QuotientRows.reindex W.waldhausen ((addInitial.obj n.unop).const ⦋0⦌ 0) ⋙
    QuotientRows.reindex W.waldhausen (⦋0⦌.const (addInitial.obj n.unop) 0) = 𝟭 _
  rw [← QuotientRows.reindex_comp]
  have h : ⦋0⦌.const (addInitial.obj n.unop) 0 ≫ (addInitial.obj n.unop).const ⦋0⦌ 0 = 𝟙 _ :=
    SimplexCategory.isTerminalZero.hom_ext _ _
  rw [h, QuotientRows.reindex_id]

lemma pathClamp_reindex (W : Model.{u}) {m n : SimplexCategory}
    (α : m ⟶ n) (τ : n ⟶ ⦋1⦌) :
    (rowsReindex (addInitial.map α)).app W ≫ (rowsReindex (pathClamp (α ≫ τ))).app W =
      (rowsReindex (pathClamp τ)).app W ≫ (rowsReindex (addInitial.map α)).app W := by
  apply Model.Hom.ext
  change QuotientRows.reindex W.waldhausen (addInitial.map α) ⋙
    QuotientRows.reindex W.waldhausen (pathClamp (α ≫ τ)) =
      QuotientRows.reindex W.waldhausen (pathClamp τ) ⋙
        QuotientRows.reindex W.waldhausen (addInitial.map α)
  rw [← QuotientRows.reindex_comp, ← QuotientRows.reindex_comp, pathClamp_naturality]

/-- The actual added-initial-row contraction cylinder, before any weak-equivalence argument. -/
def pathCylinder (H : Model.{u} ⥤ SSet.{u}) (W : Model.{u}) :
    TheoremA.diagonalSSet (pathDiagram W ⋙ H) ⊗ Δ[1] ⟶
      TheoremA.diagonalSSet (pathDiagram W ⋙ H) where
  app n := ↾fun z ↦ (H.map ((rowsReindex (pathClamp z.2.down)).app W)).app n z.1
  naturality n m α := by
    ext z : 3
    change (H.map ((rowsReindex (pathClamp (α.unop ≫ z.2.down))).app W)).app m
      ((H.obj ((rows (addInitial.obj m.unop)).obj W)).map α
        ((H.map ((rowsReindex (addInitial.map α.unop)).app W)).app n z.1)) =
      (H.obj ((rows (addInitial.obj m.unop)).obj W)).map α
        ((H.map ((rowsReindex (addInitial.map α.unop)).app W)).app n
          ((H.map ((rowsReindex (pathClamp z.2.down)).app W)).app n z.1))
    have hn := ConcreteCategory.congr_hom
      ((H.map ((rowsReindex (pathClamp (α.unop ≫ z.2.down))).app W)).naturality α)
        ((H.map ((rowsReindex (addInitial.map α.unop)).app W)).app n z.1)
    refine hn.trans ?_
    apply congrArg ((H.obj ((rows (addInitial.obj m.unop)).obj W)).map α)
    have hm := congrArg (fun η : H.obj ((rows (addInitial.obj n.unop)).obj W) ⟶
        H.obj ((rows (addInitial.obj m.unop)).obj W) ↦ η.app n)
      (congrArg H.map (pathClamp_reindex W α.unop z.2.down))
    simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app] at hm
    exact ConcreteCategory.congr_hom hm z.1

/-- The diagonal simplicial map induced by the path augmentation. -/
def pathAugmentationMap (H : Model.{u} ⥤ SSet.{u}) (W : Model.{u}) :=
  TheoremA.diagonalMap (Functor.whiskerRight (pathAugmentation W) H)

/-- The diagonal simplicial map induced by the constant-row section. -/
def pathSectionMap (H : Model.{u} ⥤ SSet.{u}) (W : Model.{u}) :=
  TheoremA.diagonalMap (Functor.whiskerRight (pathSection W) H)

lemma pathSectionMap_augmentation (H : Model.{u} ⥤ SSet.{u}) (W : Model.{u}) :
    pathSectionMap H W ≫ pathAugmentationMap H W = 𝟙 _ := by
  let G := (Functor.whiskeringRight SimplexCategoryᵒᵖ Model SSet).obj H ⋙ TheoremA.diagonalFunctor
  change G.map (pathSection W) ≫ G.map (pathAugmentation W) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp, pathSection_augmentation, CategoryTheory.Functor.map_id]

lemma pathCylinder_zero (H : Model.{u} ⥤ SSet.{u}) (W : Model.{u}) :
    SSet.ι₀ ≫ pathCylinder H W = pathAugmentationMap H W ≫ pathSectionMap H W := by
  ext n A : 4
  change (H.map ((rowsReindex (pathClamp (n.unop.const ⦋1⦌ 0))).app W)).app n A =
    (H.map ((pathSection W).app n)).app n ((H.map ((pathAugmentation W).app n)).app n A)
  rw [pathClamp_zero]
  have h : (rowsReindex ((addInitial.obj n.unop).const (addInitial.obj n.unop) 0)).app W =
      (pathAugmentation W).app n ≫ (pathSection W).app n := by
    apply Model.Hom.ext
    exact QuotientRows.reindex_comp W.waldhausen
      ((addInitial.obj n.unop).const ⦋0⦌ 0) (⦋0⦌.const (addInitial.obj n.unop) 0)
  rw [h, CategoryTheory.Functor.map_comp]
  rfl

lemma pathCylinder_one (H : Model.{u} ⥤ SSet.{u}) (W : Model.{u}) :
    SSet.ι₁ ≫ pathCylinder H W = 𝟙 _ := by
  ext n A : 4
  change (H.map ((rowsReindex (pathClamp (n.unop.const ⦋1⦌ 1))).app W)).app n A = A
  rw [pathClamp_one]
  have h : (rowsReindex (𝟙 (addInitial.obj n.unop))).app W = 𝟙 _ := by
    apply Model.Hom.ext
    exact QuotientRows.reindex_id _ _
  rw [h, CategoryTheory.Functor.map_id]
  rfl

/-- The complete added-initial-row path object has the displayed original contraction. -/
def pathHomotopy (H : Model.{u} ⥤ SSet.{u}) (W : Model.{u}) :
    SSet.Homotopy (pathAugmentationMap H W ≫ pathSectionMap H W) (𝟙 _) where
  h := pathCylinder H W
  h₀ := pathCylinder_zero H W
  h₁ := pathCylinder_one H W
  rel := by ext n z; exact z.1.property.elim

/-- The actual augmentation and degeneracy section give the whole path-object equivalence. -/
def pathRealizationEquiv (H : Model.{u} ⥤ SSet.{u}) (W : Model.{u}) :
    ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (pathDiagram W ⋙ H)|
      |TheoremA.diagonalSSet ((Functor.const _).obj ((rows ⦋0⦌).obj W) ⋙ H)| where
  toFun := (SSet.toTop.map (pathAugmentationMap H W)).hom
  invFun := (SSet.toTop.map (pathSectionMap H W)).hom
  left_inv := by
    have h := realizationSimplicialHomotopy (pathHomotopy H W)
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      TopCat.hom_comp, TopCat.hom_id] at h
    exact ⟨h⟩
  right_inv := by
    have h := congrArg (fun f ↦ (SSet.toTop.map f).hom) (pathSectionMap_augmentation H W)
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      TopCat.hom_comp, TopCat.hom_id] at h
    rw [h]

lemma zeroRows_all_weak (W : Model.{u}) {A B : (rows ⦋0⦌).obj W} (f : A ⟶ B) :
    ((rows ⦋0⦌).obj W).waldhausen.weq f := by
  rintro ⟨⟨i,j⟩,hij⟩
  fin_cases i
  fin_cases j
  exact W.waldhausen.weq_iso _ ((A.property.zero 0).isIso (B.property.zero 0) _)

/-- At every finite S-level the genuine added-initial-row path object is contractible. -/
theorem pathStage_contractible (r : ℕ) (W : Model.{u}) :
    ContractibleSpace |TheoremA.diagonalSSet (pathDiagram W ⋙ stages r)| := by
  let e : TheoremA.diagonalSSet ((Functor.const _).obj ((rows ⦋0⦌).obj W) ⋙ stages r) ≅
      (stages r).obj ((rows ⦋0⦌).obj W) :=
    TheoremA.diagonalFunctor.mapIso (Functor.constComp SimplexCategoryᵒᵖ ((rows ⦋0⦌).obj W)
      (stages r)) ≪≫
      TheoremA.diagonalConstantIso _
  let : ContractibleSpace |(stages r).obj ((rows ⦋0⦌).obj W)| :=
    stageSpace_contractible_of_all_weak r ((rows ⦋0⦌).obj W) (fun {A B} f ↦ zeroRows_all_weak W f)
  let : ContractibleSpace |TheoremA.diagonalSSet ((Functor.const _).obj ((rows ⦋0⦌).obj W) ⋙
    stages r)| :=
    (TopCat.homeoOfIso (SSet.toTop.mapIso e)).contractibleSpace
  exact (pathRealizationEquiv (stages r) W).contractibleSpace


end Quillen.Waldhausen.IteratedS
