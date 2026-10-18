/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.ScalarUnit
public import Quillen.KTheory.Field.MatrixCubeComparison

/-!
# Original projective-to-upper scalar-operation naturality

An ordinary category with objects in `u + 1` and morphisms in `u` has its
Q-category in the same object and morphism universe as an upper small model.
The actual raw Q-functor can therefore be normalized directly at these matching
Q endpoints, even though the ordinary categories have different morphism
universes. Its canonical zero-isomorphism edge identifies this based map with
the original `universalKMap`.

Whole original identity-automorphism homotopies give operation naturality for
this particular mixed-universe pattern. The actual projective inclusion,
forward opposite scalar, original opposite-ring restriction and upper-model
descent supply the concrete scalar square. No linear structure is put on the
chosen model, and no arbitrary replacement map or positive symbol marking is
asserted.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u c h
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Linear
open scoped ZeroObject Topology

namespace Quillen.LowDegreeScalarAction.MixedProjectiveNaturality

private def castSelfIso {A : Type c} [Category.{h} A]
    {F : A ⥤ A} (hF : F = 𝟭 A) (a : F ≅ F) : Aut (𝟭 A) :=
  eqToIso hF.symm ≪≫ a ≪≫ eqToIso hF

private theorem castSelfIso_homotopy {A : Type c} [Category.{h} A]
    {F : A ⥤ A} (hF : F = 𝟭 A) (a : F ≅ F)
    (t : unitInterval) (z : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy (castSelfIso hF a).hom (t, z) =
      classifyingSpaceNaturalTransformationHomotopy a.hom (t, z) := by
  subst F
  simp [castSelfIso]

private theorem castSelfIso_conjugate {A : Type c} [Category.{h} A]
    {F G : A ⥤ A} (hF : F = 𝟭 A) (hG : G = 𝟭 A)
    (e : F ≅ G) (a : F ≅ F) :
    castSelfIso hG (e.symm ≪≫ a ≪≫ e) = castSelfIso hF a := by
  subst F
  subst G
  simp only [castSelfIso, eqToIso_refl, Iso.refl_trans, Iso.trans_refl]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change e.inv.app X ≫ a.hom.app X ≫ e.hom.app X = a.hom.app X
  have hn := a.hom.naturality (e.hom.app X)
  change e.hom.app X ≫ a.hom.app X = a.hom.app X ≫ e.hom.app X at hn
  rw [← hn, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

section IdentityHomotopy
variable {C : Type c} [Category.{h} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

private def identityQAut (a : Aut (𝟭 C)) : Aut (𝟭 E.QCategory) :=
  NatIso.ofComponents (fun X => E.qIsoOfIso (a.app X.obj.of)) (by
    rintro ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ f
    have hn := (ExactFunctor.mapQIso (F := ExactFunctor.id E)
      (G := ExactFunctor.id E) a).hom.naturality f
    change (ExactFunctor.id E).mapQ.map f ≫ (E.qIsoOfIso (a.app Y)).hom =
      (E.qIsoOfIso (a.app X)).hom ≫ (ExactFunctor.id E).mapQ.map f at hn
    have hf : (ExactFunctor.id E).mapQ.map f = f := by
      cases f using Quotient.inductionOn
      rfl
    rw [hf] at hn
    exact hn)

private theorem cast_mapQIso (a : Aut (𝟭 C)) :
    castSelfIso (ExactFunctor.mapQ_id E)
      (ExactFunctor.mapQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) a) =
        identityQAut E a := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp [castSelfIso, identityQAut, ExactFunctor.mapQIso]

private theorem cast_normalizedQIso (a : Aut (𝟭 C)) :
    castSelfIso (IdentityAutomorphism.normalizedIdentityQ E)
      (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) a) =
        identityQAut E a := by
  unfold ExactFunctor.normalizedQIso rebaseFunctorNatIso
  exact (castSelfIso_conjugate (ExactFunctor.mapQ_id E)
    (IdentityAutomorphism.normalizedIdentityQ E) _ _).trans (cast_mapQIso E a)

private theorem identityQAut_homotopy (a : Aut (𝟭 C))
    (t : unitInterval) (z : E.KSpace) :
    classifyingSpaceNaturalTransformationHomotopy (identityQAut E a).hom (t, z) =
      IdentityAutomorphism.homotopy E a (t, z) := by
  rw [← cast_normalizedQIso E a, castSelfIso_homotopy]
  rfl

end IdentityHomotopy

section MixedMap
variable {C D : Type (u + 1)} [Category.{u} C] [SmallCategory D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

private abbrev normalizedQ := rebaseFunctor F.mapQ EC.qZero ED.qZero
  (ED.qIsoOfIso F.toFunctor.mapZeroObject)

private theorem normalizedQ_point :
    classifyingSpaceMap (normalizedQ F) EC.kBasepoint = ED.kBasepoint :=
  rebaseFunctor_map_point _ _ _ _

private theorem correctedMap_congr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (hfg : f = g) {x : X} {y : Y}
    (p : Path (f x) y) (q : Path (g x) y) (hpq : ∀ t, p t = q t)
    (n : ℕ) (a : HomotopyGroup.Pi n X x) :
    pathTransport p n (homotopyGroupMap f rfl a) =
      pathTransport q n (homotopyGroupMap g rfl a) := by
  subst g
  have he : p = q := Path.ext (funext hpq)
  subst q
  rfl

private theorem universalKMap_normalizedQ (n : ℕ) :
    F.universalKMap n = piMap n (classifyingSpaceMap (normalizedQ F)).hom
      (normalizedQ_point F) := by
  ext a
  change pathTransport F.universalQZeroBasePath (n + 1)
    (homotopyGroupMap (classifyingSpaceMapUniversal F.mapQ) rfl a) =
    homotopyGroupMap (classifyingSpaceMap (normalizedQ F)).hom (normalizedQ_point F) a
  exact (correctedMap_congr (classifyingSpaceMapUniversal_eq F.mapQ)
    F.universalQZeroBasePath
    (classifyingSpaceIsoBasePath F.mapQ EC.qZero ED.qZero
      (ED.qIsoOfIso F.toFunctor.mapZeroObject)) (fun _ => rfl) (n + 1) a).trans
      (pathTransport_rebaseFunctor_homotopyGroupMap F.mapQ EC.qZero ED.qZero
        (ED.qIsoOfIso F.toFunctor.mapZeroObject) (n + 1) a)

private theorem mapQ_iso {X Y : C} (e : X ≅ Y) :
    F.mapQ.mapIso (EC.qIsoOfIso e) = ED.qIsoOfIso (F.toFunctor.mapIso e) := by
  apply Iso.ext
  apply Quotient.sound
  refine ⟨Span.mkIso (Iso.refl _) ?_ ?_⟩
  · change 𝟙 (F.toFunctor.obj X) ≫ 𝟙 (F.toFunctor.obj X) = F.toFunctor.map (𝟙 X)
    simp
  · change 𝟙 (F.toFunctor.obj X) ≫ F.toFunctor.map e.hom = F.toFunctor.map e.hom
    simp

private theorem mapQ_identityQAut (a : Aut (𝟭 C)) (b : Aut (𝟭 D))
    (hcomp : ∀ X, F.toFunctor.map (a.hom.app X) = b.hom.app (F.toFunctor.obj X))
    (X : EC.QCategory) :
    F.mapQ.map ((identityQAut EC a).hom.app X) =
      (identityQAut ED b).hom.app (F.mapQ.obj X) := by
  have hi : F.toFunctor.mapIso (a.app X.obj.of) = b.app (F.toFunctor.obj X.obj.of) := by
    apply Iso.ext
    exact hcomp X.obj.of
  change F.mapQ.map (EC.qIsoOfIso (a.app X.obj.of)).hom =
    (ED.qIsoOfIso (b.app (F.toFunctor.obj X.obj.of))).hom
  exact (congrArg Iso.hom (mapQ_iso F (a.app X.obj.of))).trans
    (congrArg (fun e => (ED.qIsoOfIso e).hom) hi)

private theorem normalizedQ_identityQAut (a : Aut (𝟭 C)) (b : Aut (𝟭 D))
    (hcomp : ∀ X, F.toFunctor.map (a.hom.app X) = b.hom.app (F.toFunctor.obj X))
    (X : EC.QCategory) :
    (normalizedQ F).map ((identityQAut EC a).hom.app X) =
      (identityQAut ED b).hom.app ((normalizedQ F).obj X) := by
  let e := rebaseFunctorIso F.mapQ EC.qZero ED.qZero
    (ED.qIsoOfIso F.toFunctor.mapZeroObject)
  change e.inv.app X ≫ F.mapQ.map ((identityQAut EC a).hom.app X) ≫ e.hom.app X = _
  rw [mapQ_identityQAut F a b hcomp]
  have hn := (identityQAut ED b).hom.naturality (e.hom.app X)
  change e.hom.app X ≫ (identityQAut ED b).hom.app ((normalizedQ F).obj X) =
    (identityQAut ED b).hom.app (F.mapQ.obj X) ≫ e.hom.app X at hn
  rw [← hn, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem identityHomotopy_natural (a : Aut (𝟭 C)) (b : Aut (𝟭 D))
    (hcomp : ∀ X, F.toFunctor.map (a.hom.app X) = b.hom.app (F.toFunctor.obj X))
    (t : unitInterval) (z : EC.KSpace) :
    classifyingSpaceMap (normalizedQ F) (IdentityAutomorphism.homotopy EC a (t, z)) =
      IdentityAutomorphism.homotopy ED b (t, classifyingSpaceMap (normalizedQ F) z) := by
  have hw : Functor.whiskerRight (identityQAut EC a).hom (normalizedQ F) =
      Functor.whiskerLeft (normalizedQ F) (identityQAut ED b).hom := by
    apply NatTrans.ext
    funext X
    exact normalizedQ_identityQAut F a b hcomp X
  rw [← identityQAut_homotopy EC a, ← identityQAut_homotopy ED b,
    ← classifyingSpaceNaturalTransformationHomotopy_whiskerRight, hw,
    classifyingSpaceNaturalTransformationHomotopy_whiskerLeft]

/-- Original identity-automorphism operations commute with the original
universal K-map for the displayed mixed ordinary morphism universes. -/
theorem universalKMap_operation (a : Aut (𝟭 C)) (b : Aut (𝟭 D))
    (hcomp : ∀ X, F.toFunctor.map (a.hom.app X) = b.hom.app (F.toFunctor.obj X))
    (m : ℕ) (z : EC.K m) :
    F.universalKMap (m + 1)
        (IdentityTrack.operation (IdentityAutomorphism.homotopy EC a).toHomotopy
          (IdentityAutomorphism.homotopy_fixed EC a) m z) =
      IdentityTrack.operation (IdentityAutomorphism.homotopy ED b).toHomotopy
        (IdentityAutomorphism.homotopy_fixed ED b) m (F.universalKMap m z) := by
  rw [universalKMap_normalizedQ, universalKMap_normalizedQ]
  exact IdentityTrack.operation_natural (IdentityAutomorphism.homotopy EC a).toHomotopy
    (IdentityAutomorphism.homotopy_fixed EC a) (IdentityAutomorphism.homotopy ED b).toHomotopy
    (IdentityAutomorphism.homotopy_fixed ED b) (classifyingSpaceMap (normalizedQ F)).hom
    (normalizedQ_point F) (identityHomotopy_natural F a b hcomp) m z

/-- The original K1-to-K2 operation retains its actual universal K-map in
this mixed ordinary morphism-universe pattern. -/
theorem universalKMap_kOneAction (a : Aut (𝟭 C)) (b : Aut (𝟭 D))
    (hcomp : ∀ X, F.toFunctor.map (a.hom.app X) = b.hom.app (F.toFunctor.obj X))
    (z : EC.K 1) :
    F.universalKMap 2 (IdentityAutomorphism.kOneAction EC a z) =
      IdentityAutomorphism.kOneAction ED b (F.universalKMap 1 z) :=
  universalKMap_operation F a b hcomp 1 z

end MixedMap

section ActualRightProjectives
variable (F : Type u) [Field F]

private theorem ordinary_scalar_component (a : Fˣ)
    (P : FiniteProjectiveModule.Category.{u, u} Fᵐᵒᵖ) :
    (Field.rightProjectiveToModuleExact F).toFunctor.map
        ((scalarNatAut Fᵐᵒᵖ (FiniteProjectiveModule.Category.{u, u} Fᵐᵒᵖ)
          (Units.opEquiv.symm (MulOpposite.op a))).hom.app P) =
      (scalarNatAut F (FGModuleCat.{u} F) a).hom.app
        ((Field.rightProjectiveToModuleExact F).toFunctor.obj P) := by
  apply (ModuleCat.finiteModule F).ι.map_injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Actual projective inclusion, opposite restriction and model descent send
the forward opposite unit to the same original scalar, without inversion. -/
theorem rightProjectiveToUpperExact_scalar_component (a : Fˣ)
    (P : FiniteProjectiveModule.Category.{u, u} Fᵐᵒᵖ) :
    (Field.rightProjectiveToUpperExact F).toFunctor.map
        ((scalarNatAut Fᵐᵒᵖ (FiniteProjectiveModule.Category.{u, u} Fᵐᵒᵖ)
          (Units.opEquiv.symm (MulOpposite.op a))).hom.app P) =
      (smallModelScalarNatAut.{u, u + 1, u, u + 1} F (FGModuleCat.{u} F) a).hom.app
        ((Field.rightProjectiveToUpperExact F).toFunctor.obj P) := by
  change (equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.map
    ((Field.rightProjectiveToModuleExact F).toFunctor.map
      ((scalarNatAut Fᵐᵒᵖ (FiniteProjectiveModule.Category.{u, u} Fᵐᵒᵖ)
        (Units.opEquiv.symm (MulOpposite.op a))).hom.app P)) = _
  rw [ordinary_scalar_component]
  exact smallModelScalarNatAut_functor_map_hom.{u, u + 1, u, u + 1} F (FGModuleCat.{u} F) a _

/-- The exact original projective-to-upper universal K-map preserves the
scalar K1-to-K2 operation at the literal forward opposite unit. -/
theorem rightProjectiveToUpperExact_kOneAction (a : Fˣ)
    (z : (FiniteProjectiveModule.exactStructure.{u, u} Fᵐᵒᵖ).K 1) :
    (Field.rightProjectiveToUpperExact F).universalKMap 2
        (IdentityAutomorphism.kOneAction (FiniteProjectiveModule.exactStructure.{u, u} Fᵐᵒᵖ)
          (scalarNatAut Fᵐᵒᵖ (FiniteProjectiveModule.Category.{u, u} Fᵐᵒᵖ)
            (Units.opEquiv.symm (MulOpposite.op a))) z) =
      IdentityAutomorphism.kOneAction
        (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}
        (smallModelScalarNatAut.{u, u + 1, u, u + 1} F (FGModuleCat.{u} F) a)
        ((Field.rightProjectiveToUpperExact F).universalKMap 1 z) :=
  universalKMap_kOneAction (Field.rightProjectiveToUpperExact F) _ _
    (rightProjectiveToUpperExact_scalar_component F a) z

/-- The same actual square in the original bundled scalar-operation notation. -/
theorem rightProjectiveToUpperExact_scalarAction (a : Fˣ)
    (z : (FiniteProjectiveModule.exactStructure.{u, u} Fᵐᵒᵖ).K 1) :
    (Field.rightProjectiveToUpperExact F).universalKMap 2
        (ScalarUnit.finiteProjectiveKOneAction Fᵐᵒᵖ
          (Units.opEquiv.symm (MulOpposite.op a)) z) =
      ScalarUnit.upperFiniteModuleKOneAction F a
        ((Field.rightProjectiveToUpperExact F).universalKMap 1 z) :=
  rightProjectiveToUpperExact_kOneAction F a z

end ActualRightProjectives

end Quillen.LowDegreeScalarAction.MixedProjectiveNaturality
