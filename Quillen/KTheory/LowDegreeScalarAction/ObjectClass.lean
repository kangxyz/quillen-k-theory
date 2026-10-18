/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.IdentityAutomorphism
public import Quillen.KTheory.GrothendieckComparison.Basic
public import Quillen.KTheory.Automorphism.PositiveNormalization
public import Quillen.Topology.Realization.DoubleHomotopy
public import Quillen.KTheory.LowDegreeScalarAction.ScalarUnit
public import Quillen.KTheory.Field.MatrixCubeComparison

/-!
# Object-class calibration of the original scalar operations

The original full-apex-minus-zero-apex object loop is the reverse of the
original core loop. The two actual nerve cylinders interchange, including
both original time parameters. Conjugation through the actual Q rebase
identifies the normalized identity track with that categorical identity
track. The existing degree-zero normalization and reversal formulas then
show that the operation on the original object class is the original capped
automorphism class, hence inverse to the literal automorphism-first cube.
The chosen zero object has neutral class and neutral output.

The cube comparison uses the existing SmallCategory automorphism cube.
For a chosen SmallModel of an independently sized linear category, the
original scalar natural automorphism is lifted through its realization;
no linear structure on the model is assumed. On the actual upper model of
finite modules over a field, the original module determinant of the action
on the rank-n object class is the inverse nth power of the same scalar unit.
Every finite rank, including zero, is covered. No ordered symbol or K2
product identification is asserted.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open MonoidalCategory CartesianMonoidalCategory
open scoped ZeroObject Simplicial Topology unitInterval
universe u v
namespace Quillen.LowDegreeScalarAction.ObjectClass

private theorem ordinalInterchange
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {F G : C ⥤ D} (η : F ⟶ G) (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X))
    {X Y : C} (f : X ⟶ Y) (a b c d : Fin 2) (hab : a ≤ b) (hcd : c ≤ d) :
    HEq
      (((ComposableArrows.mk₁ η).map (homOfLE hcd)).app
          (((ComposableArrows.mk₁ α).obj a).obj X) ≫
        ((ComposableArrows.mk₁ η).obj d).map
          (((ComposableArrows.mk₁ α).map (homOfLE hab)).app X ≫
            ((ComposableArrows.mk₁ α).obj b).map f))
      (((ComposableArrows.mk₁ β).map (homOfLE hab)).app
          (((ComposableArrows.mk₁ η).obj c).obj X) ≫
        ((ComposableArrows.mk₁ β).obj b).map
          (((ComposableArrows.mk₁ η).map (homOfLE hcd)).app X ≫
            ((ComposableArrows.mk₁ η).obj d).map f)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals try exact ((by decide : ¬ (1 : Fin 2) ≤ 0) hab).elim
  all_goals try exact ((by decide : ¬ (1 : Fin 2) ≤ 0) hcd).elim
  all_goals
    simp_all only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ComposableArrows.mk₁_obj,
      ComposableArrows.Mk₁.obj, Functor.id_obj, Fin.mk_one, homOfLE_leOfHom,
      ComposableArrows.mk₁_map, ComposableArrows.Mk₁.map, Functor.id_map, Functor.map_comp,
      heq_eq_eq, NatTrans.id_app, Category.id_comp]
  exact β.naturality_assoc (η.app X) (G.map f)

private theorem nerveInterchange
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {F G : C ⥤ D} (η : F ⟶ G) (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X)) :
    naturalTransformationNerveCylinder α ▷ Δ[1] ≫
        naturalTransformationNerveCylinder η =
      simplicialCylinderSwap (nerve C) ≫ naturalTransformationNerveCylinder η ▷ Δ[1] ≫
        naturalTransformationNerveCylinder β := by
  ext n z
  change
    (z.2.down.toOrderHom.monotone.functor.prod'
      ((z.1.2.down.toOrderHom.monotone.functor.prod' z.1.1) ⋙
        naturalTransformationCylinderFunctor α)) ⋙
      naturalTransformationCylinderFunctor η =
    (z.1.2.down.toOrderHom.monotone.functor.prod'
      ((z.2.down.toOrderHom.monotone.functor.prod' z.1.1) ⋙
        naturalTransformationCylinderFunctor η)) ⋙
      naturalTransformationCylinderFunctor β
  refine CategoryTheory.Functor.hext (fun p => ?_) ?_
  · dsimp [naturalTransformationNerveCylinder, naturalTransformationCylinderFunctor,
      Functor.uncurry, Functor.prod', simplicialCylinderSwap]
    generalize hτ : z.1.2.down.toOrderHom p = t
    generalize hθ : z.2.down.toOrderHom p = s
    fin_cases t <;> fin_cases s <;> rfl
  · intro p q f
    exact ordinalInterchange η α β hF hG (z.1.1.map f)
      (z.1.2.down.toOrderHom p) (z.1.2.down.toOrderHom q)
      (z.2.down.toOrderHom p) (z.2.down.toOrderHom q)
      (z.1.2.down.toOrderHom.monotone (leOfHom f))
      (z.2.down.toOrderHom.monotone (leOfHom f))

private theorem homotopyInterchange
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {F G : C ⥤ D} (η : F ⟶ G) (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X))
    (s t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy η
        (s, classifyingSpaceNaturalTransformationHomotopy α (t, x)) =
      classifyingSpaceNaturalTransformationHomotopy β
        (t, classifyingSpaceNaturalTransformationHomotopy η (s, x)) :=
  realizationSimplicialHomotopy_interchange
    (naturalTransformationNerveHomotopy η) (naturalTransformationNerveHomotopy α)
    (naturalTransformationNerveHomotopy η) (naturalTransformationNerveHomotopy β)
    (nerveInterchange η α β hF hG) s t x

private def castSelfIso {A : Type u} [SmallCategory A]
    {F : A ⥤ A} (h : F = 𝟭 A) (α : F ≅ F) : 𝟭 A ≅ 𝟭 A :=
  (eqToIso h.symm) ≪≫ α ≪≫ eqToIso h

private theorem castSelfIso_homotopy {A : Type u} [SmallCategory A]
    {F : A ⥤ A} (h : F = 𝟭 A) (α : F ≅ F)
    (t : unitInterval) (z : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy (castSelfIso h α).hom (t, z) =
      classifyingSpaceNaturalTransformationHomotopy α.hom (t, z) := by
  subst F
  simp [castSelfIso]

private theorem castSelfIso_conjugate {A : Type u} [SmallCategory A]
    {F G : A ⥤ A} (hF : F = 𝟭 A) (hG : G = 𝟭 A)
    (e : F ≅ G) (α : F ≅ F) :
    castSelfIso hG (e.symm ≪≫ α ≪≫ e) = castSelfIso hF α := by
  subst F
  subst G
  simp only [castSelfIso, eqToIso_refl, Iso.refl_trans, Iso.trans_refl]
  apply Iso.ext
  apply NatTrans.ext
  funext A
  change e.inv.app A ≫ α.hom.app A ≫ e.hom.app A = α.hom.app A
  have hn := α.hom.naturality (e.hom.app A)
  change e.hom.app A ≫ α.hom.app A = α.hom.app A ≫ e.hom.app A at hn
  rw [← hn, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem rightClass_eq_component {T : Type u} [TopologicalSpace T] {x : T}
    {Z : Type v} [TopologicalSpace Z] (f : C(Z, Path x x)) (z : Z)
    (a : HomotopyGroup.Pi 1 Z z) :
    IdentityTrack.rightClass f z a = Automorphism.loopComponentToPiTwo (f z)
      (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a)) := by
  have h := piOne_homotopy_corrected
    (ContinuousMap.Homotopy.refl (IdentityTrack.rightMap f z))
    (IdentityTrack.rightCap f z) (Automorphism.rightNormalizationPath f z)
    (Automorphism.loopComponent_piOne_mul_comm (Path.refl x))
  exact (congrArg (loopShiftMulEquiv 0).symm (DFunLike.congr_fun h a)).trans
    (Automorphism.rightNormalization_formula f z a)

variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

private def identityQAut (u : 𝟭 C ≅ 𝟭 C) : 𝟭 E.QCategory ≅ 𝟭 E.QCategory :=
  NatIso.ofComponents (fun A => E.qIsoOfIso (u.app A.obj.of)) (by
    rintro ⟨⟨A⟩⟩ ⟨⟨B⟩⟩ f
    have h := (ExactFunctor.mapQIso (F := ExactFunctor.id E)
      (G := ExactFunctor.id E) u).hom.naturality f
    change (ExactFunctor.id E).mapQ.map f ≫ (E.qIsoOfIso (u.app B)).hom =
      (E.qIsoOfIso (u.app A)).hom ≫ (ExactFunctor.id E).mapQ.map f at h
    have hf : (ExactFunctor.id E).mapQ.map f = f := by
      cases f using Quotient.inductionOn
      rfl
    rw [hf] at h
    exact h)

private theorem cast_mapQIso (u : 𝟭 C ≅ 𝟭 C) :
    castSelfIso (ExactFunctor.mapQ_id E)
      (ExactFunctor.mapQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u) =
        identityQAut E u := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  simp [castSelfIso, identityQAut, ExactFunctor.mapQIso]

private theorem cast_normalizedQIso (u : 𝟭 C ≅ 𝟭 C) :
    castSelfIso (IdentityAutomorphism.normalizedIdentityQ E)
      (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u) =
        identityQAut E u := by
  unfold ExactFunctor.normalizedQIso rebaseFunctorNatIso
  exact (castSelfIso_conjugate (ExactFunctor.mapQ_id E)
    (IdentityAutomorphism.normalizedIdentityQ E) _ _).trans (cast_mapQIso E u)

private theorem identityQAut_homotopy (u : 𝟭 C ≅ 𝟭 C)
    (t : unitInterval) (z : E.KSpace) :
    classifyingSpaceNaturalTransformationHomotopy (identityQAut E u).hom (t, z) =
      IdentityAutomorphism.homotopy E u (t, z) := by
  rw [← cast_normalizedQIso E u, castSelfIso_homotopy]
  rfl

private def identityCoreAction (u : 𝟭 C ≅ 𝟭 C) : 𝟭 (Core C) ⟶ 𝟭 (Core C) where
  app A := CoreHom.mk (u.app A.of)
  naturality {A B} f := by
    apply Core.hom_ext
    exact u.hom.naturality f.iso.hom

private theorem coneInterchange (u : 𝟭 C ≅ 𝟭 C)
    (η : (Functor.const (Core C)).obj E.qZero ⟶ Automorphism.coreQ E)
    (X : C) (s t : unitInterval) :
    IdentityAutomorphism.homotopy E u
        (t, classifyingSpacePath (η.app (Core.mk X)) s) =
      Automorphism.conePath E η
        (classifyingSpacePath (CoreHom.mk (u.app X) : Core.mk X ⟶ Core.mk X) t) s := by
  let α := identityCoreAction u
  let β := (identityQAut E u).hom
  have hF (A : Core C) :
      ((Functor.const (Core C)).obj E.qZero).map (α.app A) = β.app E.qZero := by
    apply @Subsingleton.elim _
      (E.qHom_subsingleton_of_isZero E.qZero E.qZero (isZero_zero C))
  have hG (A : Core C) : (Automorphism.coreQ E).map (α.app A) =
      β.app ((Automorphism.coreQ E).obj A) := rfl
  have h := homotopyInterchange η α β hF hG s t (classifyingSpacePoint (Core.mk X))
  rw [classifyingSpaceNaturalTransformationHomotopy_vertex_track,
    classifyingSpaceNaturalTransformationHomotopy_vertex_track] at h
  exact (identityQAut_homotopy E u t _).symm.trans h.symm

private theorem objectLoop_eq_reverse_coreLoop (X : C) :
    E.kZeroObjectLoop X =
      (Automorphism.coreLoopMap E (classifyingSpacePoint (Core.mk X))).symm := by
  rw [Automorphism.coreLoopMap_vertex]
  simp only [Path.trans_symm, Path.symm_symm]
  rfl

private theorem objectLoopTrack_apply (u : 𝟭 C ≅ 𝟭 C) (X : C)
    (t s : unitInterval) :
    IdentityAutomorphism.homotopy E u (t, E.kZeroObjectLoop X s) =
      (Automorphism.automorphismCylinder E (u.app X) t).symm s := by
  change IdentityAutomorphism.homotopy E u
    (t, ((classifyingSpacePath (Automorphism.fullFromZero E X)).trans
      (classifyingSpacePath (E.fromZero (Q.of _ _ X))).symm) s) =
    (((Automorphism.conePath E (Automorphism.zeroCone E) _).trans
      (Automorphism.conePath E (Automorphism.fullCone E) _).symm).symm) s
  rw [Path.trans_symm, Path.symm_symm]
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact coneInterchange E u (Automorphism.fullCone E) X _ t
  · exact coneInterchange E u (Automorphism.zeroCone E) X _ t

private theorem objectClass_mk (X : C) :
    E.kZeroObjectClass X =
      (⟦(genLoopHomeomorphOfUnique (Fin 1)).symm (E.kZeroObjectLoop X)⟧ : E.K 0) := rfl

private theorem track_normalization (u : 𝟭 C ≅ 𝟭 C) (X : C) :
    let f := Automorphism.coreLoopMap E
    let z := classifyingSpacePoint (Core.mk X)
    let p := (genLoopHomeomorphOfUnique (Fin 1)).symm (loopReversal (f z))
    loopKOneNormalization (genLoopHomeomorphOfUnique (Fin 1) p)
      ⟦(IdentityTrack.track (IdentityAutomorphism.homotopy E u).toHomotopy
        (IdentityAutomorphism.homotopy_fixed E u) 0 p).map
          (genLoopHomeomorphOfUnique (Fin 1)).continuous⟧ =
      (Automorphism.automorphismClass E X (u.app X))⁻¹ := by
  let f := Automorphism.coreLoopMap E
  let z := classifyingSpacePoint (Core.mk X)
  let e := genLoopHomeomorphOfUnique (Fin 1) (X := E.KSpace) (x := E.kBasepoint)
  let p := e.symm (loopReversal (f z))
  let edge := classifyingSpacePath (C := Core C) (CoreHom.mk (u.app X) : Core.mk X ⟶ Core.mk X)
  let a := HomotopyGroup.pi1MulEquivFundamentalGroup.symm
    (Path.Homotopic.Quotient.mk edge)
  have htrack :
      (IdentityTrack.track (IdentityAutomorphism.homotopy E u).toHomotopy
        (IdentityAutomorphism.homotopy_fixed E u) 0 p).map e.continuous =
      edge.map (loopReversal.comp f).continuous := by
    ext t s
    change IdentityAutomorphism.homotopy E u (t, (loopReversal (f z)) s) =
      (Automorphism.automorphismCylinder E (u.app X) t).symm s
    change IdentityAutomorphism.homotopy E u
      (t, (Automorphism.coreLoopMap E (classifyingSpacePoint (Core.mk X))).symm s) = _
    exact (congrArg (fun q : Path E.kBasepoint E.kBasepoint =>
      IdentityAutomorphism.homotopy E u (t, q s))
      (objectLoop_eq_reverse_coreLoop E X)).symm.trans
        (objectLoopTrack_apply E u X t s)
  have h := IdentityTrack.leftClass_reverse f z a
  rw [IdentityTrack.leftClass_eq_normalization, rightClass_eq_component] at h
  change loopKOneNormalization (e p) _ = _
  rw [htrack]
  change loopKOneNormalization ((loopReversal.comp f) z)
    (FundamentalGroup.map (loopReversal.comp f) z
      (HomotopyGroup.pi1MulEquivFundamentalGroup a)) = _
  exact h

/-- On the original full-apex-minus-zero-apex object class, the identity action
  gives the original capped automorphism class, with its proved orientation. -/
theorem kZeroAction_objectClass (u : 𝟭 C ≅ 𝟭 C) (X : C) :
    IdentityAutomorphism.kZeroAction E u (E.kZeroObjectClass X) =
      Automorphism.automorphismClass E X (u.app X) := by
  let p := (genLoopHomeomorphOfUnique (Fin 1)).symm
    (Automorphism.coreLoopMap E (classifyingSpacePoint (Core.mk X))).symm
  have hc : E.kZeroObjectClass X = (⟦p⟧ : E.K 0) := by
    rw [objectClass_mk, objectLoop_eq_reverse_coreLoop]
    rfl
  rw [hc, IdentityAutomorphism.kZeroAction_normalization]
  exact (congrArg (fun a => a⁻¹) (track_normalization E u X)).trans (inv_inv _)

/-- The original object-loop action is inverse to the class of the literal
  automorphism-first cube, with its existing cap and coordinate order. -/
theorem kZeroAction_objectClass_cube (u : 𝟭 C ≅ 𝟭 C) (X : C) :
    IdentityAutomorphism.kZeroAction E u (E.kZeroObjectClass X) =
      ((Quotient.mk' (Automorphism.Cube.automorphismFirstCube E X (u.app X)))⁻¹ : E.K 1) := by
  rw [kZeroAction_objectClass, Automorphism.Cube.automorphismFirstCube_class, inv_inv]

/-- The actual chosen-zero object class has neutral output. -/
theorem kZeroAction_zero_object (u : 𝟭 C ≅ 𝟭 C) :
    IdentityAutomorphism.kZeroAction E u (E.kZeroObjectClass (0 : C)) = 1 := by
  rw [E.kZeroObjectClass_zero, IdentityAutomorphism.kZeroAction_one]

/-- The same zero-object calibration retains the original automorphism class. -/
theorem automorphismClass_zero_object (u : 𝟭 C ≅ 𝟭 C) :
    Automorphism.automorphismClass E (0 : C) (u.app (0 : C)) = 1 :=
  (kZeroAction_objectClass E u (0 : C)).symm.trans (kZeroAction_zero_object E u)

/-- The literal capped automorphism-first cube at the chosen zero is neutral. -/
theorem automorphismFirstCube_zero_object (u : 𝟭 C ≅ 𝟭 C) :
    (Quotient.mk' (Automorphism.Cube.automorphismFirstCube E (0 : C)
      (u.app (0 : C))) : E.K 1) = (1 : E.K 1) := by
  rw [Automorphism.Cube.automorphismFirstCube_class, automorphismClass_zero_object, inv_one]

end Quillen.LowDegreeScalarAction.ObjectClass

namespace Quillen.LowDegreeScalarAction.ObjectClass
universe w s
open CategoryTheory.Linear
variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C]
  [Preadditive C] [HasFiniteBiproducts C] [Linear R C] [EssentiallySmall.{s} C]
  (E : ExactStructure C)

/-- The lifted scalar automorphism calibrates the actual object class in the
  chosen model, without a linear structure on that model. -/
theorem smallModelKZeroAction_objectClass (r : Rˣ) (X : SmallModel.{s} C) :
    ScalarUnit.smallModelKZeroAction R E r (E.smallModel.{s}.kZeroObjectClass X) =
      Automorphism.automorphismClass E.smallModel.{s} X
        ((smallModelScalarNatAut R C r).app X) :=
  kZeroAction_objectClass E.smallModel.{s} (smallModelScalarNatAut R C r) X

/-- On the image of an original object, the same scalar action is inverse to
  the literal cube of its original scalar automorphism under the chosen functor. -/
theorem smallModelKZeroAction_mapped_objectClass_cube (r : Rˣ) (X : C) :
    ScalarUnit.smallModelKZeroAction R E r
        (E.smallModel.{s}.kZeroObjectClass ((equivSmallModel.{s} C).functor.obj X)) =
      ((Quotient.mk' (Automorphism.Cube.automorphismFirstCube E.smallModel.{s}
        ((equivSmallModel.{s} C).functor.obj X)
        ((equivSmallModel.{s} C).functor.mapIso ((scalarNatAut R C r).app X))))⁻¹ :
          E.SmallK.{s} 1) := by
  have h : (smallModelScalarNatAut R C r).app ((equivSmallModel.{s} C).functor.obj X) =
      (equivSmallModel.{s} C).functor.mapIso ((scalarNatAut R C r).app X) := by
    apply Iso.ext
    exact (smallModelScalarNatAut_functor_map_hom R C r X).symm
  change IdentityAutomorphism.kZeroAction E.smallModel.{s} (smallModelScalarNatAut R C r)
    (E.smallModel.{s}.kZeroObjectClass ((equivSmallModel.{s} C).functor.obj X)) = _
  rw [kZeroAction_objectClass_cube, h]

end Quillen.LowDegreeScalarAction.ObjectClass

namespace Quillen.LowDegreeScalarAction.ObjectClass
open CategoryTheory.Linear
variable (F : Type u) [Field F]

private theorem scalarMatrixAut (n : ℕ) (r : Fˣ) :
    (scalarNatAut F (FGModuleCat.{u} F) r).app (FGModuleCat.of F (Fin n → F)) =
      FGModuleCat.matrixToAut F n (Matrix.GeneralLinearGroup.scalar (Fin n) r) := by
  apply Iso.ext
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((scalarNatAut F (FGModuleCat.{u} F) r).hom.app
    (FGModuleCat.of F (Fin n → F))) x =
    (FGModuleCat.matrixToAut F n (Matrix.GeneralLinearGroup.scalar (Fin n) r)).hom x
  rw [FGModuleCat.matrixToAut_apply]
  change (fun i : Fin n => (r : F) * x i) = (Matrix.scalar (Fin n) (r : F)).mulVec x
  funext i
  simp only [Matrix.scalar_apply, Matrix.mulVec_diagonal]

/-- On the actual upper finite free-module object class, the scalar-unit action
  is inverse to the literal old cube of the scalar matrix with the same unit. -/
theorem upperFiniteModuleKZeroAction_objectClass_cube (n : ℕ) (r : Fˣ) :
    ScalarUnit.upperFiniteModuleKZeroAction F r
        ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}.kZeroObjectClass
          ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
            (FGModuleCat.of F (Fin n → F)))) =
      ((Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
          (FGModuleCat.of F (Fin n → F)))
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
          (FGModuleCat.matrixToAut F n (Matrix.GeneralLinearGroup.scalar (Fin n) r)))))⁻¹ :
            (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 1) := by
  change ScalarUnit.smallModelKZeroAction.{u, u + 1, u, u + 1} F
    (ModuleCat.finiteModuleExactStructure.{u, u} F) r
    _ = _
  rw [smallModelKZeroAction_mapped_objectClass_cube, scalarMatrixAut]

/-- The unchanged upper-module determinant of the scalar operation on the
  original rank-n object class is the inverse nth power of the same scalar unit. -/
theorem moduleDetEquiv_scalar_objectClass (n : ℕ) (r : Fˣ) :
    Field.moduleDetEquiv F
      (ScalarUnit.upperFiniteModuleKZeroAction F r
        ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}.kZeroObjectClass
          ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
            (FGModuleCat.of F (Fin n → F))))) = (r ^ n)⁻¹ := by
  rw [upperFiniteModuleKZeroAction_objectClass_cube, map_inv,
    Field.moduleDetEquiv_matrix_cube, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

/-- In rank one, the original scalar operation has determinant the inverse
  of the unchanged scalar unit. -/
theorem moduleDetEquiv_scalar_rankOne_objectClass (r : Fˣ) :
    Field.moduleDetEquiv F
      (ScalarUnit.upperFiniteModuleKZeroAction F r
        ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}.kZeroObjectClass
          ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
            (FGModuleCat.of F (Fin 1 → F))))) = r⁻¹ := by
  simpa only [pow_one] using moduleDetEquiv_scalar_objectClass F 1 r

end Quillen.LowDegreeScalarAction.ObjectClass
