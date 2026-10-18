/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.ObjectClass
public import Quillen.KTheory.LowDegreeScalarAction.FieldSymbols
public import Quillen.KTheory.Map.SmallModelUniverse
public import Quillen.KTheory.GrothendieckComparison.Naturality
public import Quillen.Topology.HomotopyGroups.PathTransportFundamentalGroup
public import Quillen.Topology.ClassifyingSpace.UniversePromotion
public import Quillen.Topology.HomotopyGroups.PathTransportNaturality
public import Quillen.Topology.HomotopyGroups.WeakEquivalence

/-!
# Scalar operations and the original change of small-model universe

The two Q-categories are lifted to a common universe. Whole original
identity-automorphism homotopies are preserved by the canonical up maps.
Normalization takes place only on the lifted raw Q-functor; the original
zero-isomorphism edge gives its exact comparison with `universalKMap`.

The resulting operation naturality applies to the canonical
`smallKUniverseEquiv`. Its scalar components are compared through the original
realization and model functors, without linear structures on either model.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Linear
open scoped ZeroObject Topology
universe u v w s₁ s₂

namespace Quillen.LowDegreeScalarAction.UniverseNaturality

section OneCategory
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

private def castSelfIso {A : Type u} [SmallCategory A]
    {F : A ⥤ A} (h : F = 𝟭 A) (α : F ≅ F) : 𝟭 A ≅ 𝟭 A :=
  eqToIso h.symm ≪≫ α ≪≫ eqToIso h

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

private def identityQAut (a : Aut (𝟭 C)) : Aut (𝟭 E.QCategory) :=
  NatIso.ofComponents (fun A => E.qIsoOfIso (a.app A.obj.of)) (by
    rintro ⟨⟨A⟩⟩ ⟨⟨B⟩⟩ f
    have h := (ExactFunctor.mapQIso (F := ExactFunctor.id E)
      (G := ExactFunctor.id E) a).hom.naturality f
    change (ExactFunctor.id E).mapQ.map f ≫ (E.qIsoOfIso (a.app B)).hom =
      (E.qIsoOfIso (a.app A)).hom ≫ (ExactFunctor.id E).mapQ.map f at h
    have hf : (ExactFunctor.id E).mapQ.map f = f := by
      cases f using Quotient.inductionOn
      rfl
    rw [hf] at h
    exact h)

private theorem cast_mapQIso (a : Aut (𝟭 C)) :
    castSelfIso (ExactFunctor.mapQ_id E)
      (ExactFunctor.mapQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) a) =
        identityQAut E a := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
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

private abbrev upMap : C(E.KSpace, ClassifyingSpace (AsSmall.{max u v} E.QCategory)) :=
  classifyingSpaceMapUniversal AsSmall.up

private theorem upMap_point :
    upMap.{u, v} E E.kBasepoint = classifyingSpacePoint (AsSmall.up.obj E.qZero) :=
  classifyingSpaceMapUniversal_point _ _

private def upKMap (n : ℕ) : E.K n →*
    HomotopyGroup.Pi (n + 1) (ClassifyingSpace (AsSmall.{max u v} E.QCategory))
      (classifyingSpacePoint (AsSmall.up.obj E.qZero)) :=
  piMap n (upMap.{u, v} E) (upMap_point E)

private theorem upKMap_injective (n : ℕ) : Function.Injective (upKMap.{u, v} E n) :=
  (homotopyEquivPiEquiv (classifyingSpaceUniverseHomeomorph.{u, u, max u v}
    E.QCategory).toHomotopyEquiv (upMap_point E) n).injective

private def liftedHomotopy (a : Aut (𝟭 C)) :
    (ContinuousMap.id (ClassifyingSpace (AsSmall.{max u v} E.QCategory))).Homotopy
      (ContinuousMap.id (ClassifyingSpace (AsSmall.{max u v} E.QCategory))) :=
  (classifyingSpaceNaturalTransformationHomotopy
    (UniversePromotion.liftTransformation.{u, v} (identityQAut E a).hom)).cast
      (by change (classifyingSpaceMap (𝟭 _)).hom = _; rw [classifyingSpaceMap_id]; rfl)
      (by change (classifyingSpaceMap (𝟭 _)).hom = _; rw [classifyingSpaceMap_id]; rfl)

private theorem liftedHomotopy_up (a : Aut (𝟭 C))
    (t : unitInterval) (z : E.KSpace) :
    liftedHomotopy.{u, v} E a (t, upMap E z) =
      upMap E (IdentityAutomorphism.homotopy E a (t, z)) := by
  change classifyingSpaceNaturalTransformationHomotopy
    (UniversePromotion.liftTransformation.{u, v} (identityQAut E a).hom)
      (t, upMap E z) = _
  rw [← identityQAut_homotopy]
  exact UniversePromotion.naturalTransformationHomotopy_up (identityQAut E a).hom t z

private theorem liftedHomotopy_fixed (a : Aut (𝟭 C)) (t : unitInterval) :
    liftedHomotopy.{u, v} E a (t, classifyingSpacePoint (AsSmall.up.obj E.qZero)) =
      classifyingSpacePoint (AsSmall.up.obj E.qZero) := by
  rw [← upMap_point E, liftedHomotopy_up, IdentityAutomorphism.homotopy_fixed]

private theorem upKMap_operation (a : Aut (𝟭 C)) (m : ℕ) (z : E.K m) :
    upKMap.{u, v} E (m + 1)
      (IdentityTrack.operation (IdentityAutomorphism.homotopy E a).toHomotopy
        (IdentityAutomorphism.homotopy_fixed E a) m z) =
      IdentityTrack.operation (liftedHomotopy E a) (liftedHomotopy_fixed E a) m
        (upKMap E m z) :=
  IdentityTrack.operation_natural (IdentityAutomorphism.homotopy E a).toHomotopy
    (IdentityAutomorphism.homotopy_fixed E a) (liftedHomotopy E a)
    (liftedHomotopy_fixed E a) (upMap E) (upMap_point E)
    (fun t x => (liftedHomotopy_up E a t x).symm) m z

end OneCategory

section IndependentCategories
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type v} [SmallCategory D] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

private abbrev liftedQ : AsSmall.{max u v} EC.QCategory ⥤
    AsSmall.{max u v} ED.QCategory :=
  universeLiftFunctor F.mapQ

private def liftedZeroIso : (liftedQ F).obj (AsSmall.up.obj EC.qZero) ≅
    AsSmall.up.obj ED.qZero :=
  (AsSmall.up : ED.QCategory ⥤ AsSmall.{max u v} ED.QCategory).mapIso
    (ED.qIsoOfIso F.toFunctor.mapZeroObject)

private abbrev normalizedLiftedQ :=
  rebaseFunctor (liftedQ F) (AsSmall.up.obj EC.qZero) (AsSmall.up.obj ED.qZero)
    (liftedZeroIso F)

private theorem liftedRowSquare :
    (upMap.{v, u} ED).comp (classifyingSpaceMapUniversal F.mapQ) =
      (classifyingSpaceMap (liftedQ F)).hom.comp (upMap.{u, v} EC) := by
  rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_comp,
    ← classifyingSpaceMapUniversal_comp]
  rfl

private theorem universalKMap_up_square (n : ℕ) (a : EC.K n) :
    upKMap.{v, u} ED n (F.universalKMap n a) =
      piMap n (classifyingSpaceMap (normalizedLiftedQ F)).hom
        (rebaseFunctor_map_point _ _ _ _) (upKMap.{u, v} EC n a) := by
  let δ := classifyingSpaceIsoBasePath (liftedQ F)
    (AsSmall.up.obj EC.qZero) (AsSmall.up.obj ED.qZero) (liftedZeroIso F)
  have h₀ : upMap.{v, u} ED (classifyingSpaceMapUniversal F.mapQ EC.kBasepoint) =
      classifyingSpaceMap (liftedQ F) (classifyingSpacePoint (AsSmall.up.obj EC.qZero)) := by
    change ((upMap.{v, u} ED).comp (classifyingSpaceMapUniversal F.mapQ)) EC.kBasepoint = _
    rw [liftedRowSquare]
    exact congrArg (classifyingSpaceMap (liftedQ F)) (upMap_point EC)
  have hn := pathTransport_naturality_of_track (upMap.{v, u} ED)
    F.universalQZeroBasePath δ h₀ (upMap_point ED)
    (fun t => classifyingSpaceMapUniversal_path
      (AsSmall.up : ED.QCategory ⥤ AsSmall.{max u v} ED.QCategory)
      (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom t) (n + 1)
    (homotopyGroupMap (classifyingSpaceMapUniversal F.mapQ) rfl a)
  change homotopyGroupMap (upMap.{v, u} ED) (upMap_point ED)
    (pathTransport F.universalQZeroBasePath (n + 1)
      (homotopyGroupMap (classifyingSpaceMapUniversal F.mapQ) rfl a)) = _
  rw [← hn]
  have hm : homotopyGroupMap (upMap.{v, u} ED) h₀
      (homotopyGroupMap (classifyingSpaceMapUniversal F.mapQ) rfl a) =
      homotopyGroupMap (classifyingSpaceMap (liftedQ F)).hom rfl
        (upKMap.{u, v} EC n a) := by
    change homotopyGroupMap (upMap.{v, u} ED) h₀
        (homotopyGroupMap (classifyingSpaceMapUniversal F.mapQ) rfl a) =
      homotopyGroupMap (classifyingSpaceMap (liftedQ F)).hom rfl
        (homotopyGroupMap (upMap.{u, v} EC) (upMap_point EC) a)
    rw [← homotopyGroupMap_comp, ← homotopyGroupMap_comp]
    exact congrFun (homotopyGroupMap_congr (liftedRowSquare F) _ _) a
  rw [hm]
  exact pathTransport_rebaseFunctor_homotopyGroupMap (liftedQ F)
    (AsSmall.up.obj EC.qZero) (AsSmall.up.obj ED.qZero) (liftedZeroIso F) (n + 1) _

private theorem mapQ_identityQAut (a : Aut (𝟭 C)) (b : Aut (𝟭 D))
    (h : ∀ X, F.toFunctor.map (a.hom.app X) = b.hom.app (F.toFunctor.obj X))
    (X : EC.QCategory) :
    F.mapQ.map ((identityQAut EC a).hom.app X) =
      (identityQAut ED b).hom.app (F.mapQ.obj X) := by
  have hi : F.toFunctor.mapIso (a.app X.obj.of) = b.app (F.toFunctor.obj X.obj.of) := by
    apply Iso.ext
    exact h X.obj.of
  have hq : F.mapQ.mapIso (EC.qIsoOfIso (a.app X.obj.of)) =
      ED.qIsoOfIso (F.toFunctor.mapIso (a.app X.obj.of)) := by
    apply Iso.ext
    apply Quotient.sound
    refine ⟨Span.mkIso (Iso.refl _) ?_ ?_⟩
    · change 𝟙 (F.toFunctor.obj X.obj.of) ≫ 𝟙 (F.toFunctor.obj X.obj.of) =
        F.toFunctor.map (𝟙 X.obj.of)
      simp
    · change 𝟙 (F.toFunctor.obj X.obj.of) ≫ F.toFunctor.map (a.app X.obj.of).hom =
        F.toFunctor.map (a.app X.obj.of).hom
      simp
  change F.mapQ.map (EC.qIsoOfIso (a.app X.obj.of)).hom =
    (ED.qIsoOfIso (b.app (F.toFunctor.obj X.obj.of))).hom
  exact (congrArg Iso.hom hq).trans
    (congrArg (fun e => (ED.qIsoOfIso e).hom) hi)

private theorem liftedQ_identityQAut (a : Aut (𝟭 C)) (b : Aut (𝟭 D))
    (h : ∀ X, F.toFunctor.map (a.hom.app X) = b.hom.app (F.toFunctor.obj X))
    (X : AsSmall.{max u v} EC.QCategory) :
    (liftedQ F).map
        ((UniversePromotion.liftTransformation.{u, v} (identityQAut EC a).hom).app X) =
      (UniversePromotion.liftTransformation.{v, u} (identityQAut ED b).hom).app
        ((liftedQ F).obj X) := by
  apply ULift.ext
  exact mapQ_identityQAut F a b h
    ((AsSmall.down : AsSmall.{max u v} EC.QCategory ⥤ EC.QCategory).obj X)

private theorem normalizedLiftedQ_identityQAut (a : Aut (𝟭 C)) (b : Aut (𝟭 D))
    (h : ∀ X, F.toFunctor.map (a.hom.app X) = b.hom.app (F.toFunctor.obj X))
    (X : AsSmall.{max u v} EC.QCategory) :
    (normalizedLiftedQ F).map
        ((UniversePromotion.liftTransformation.{u, v} (identityQAut EC a).hom).app X) =
      (UniversePromotion.liftTransformation.{v, u} (identityQAut ED b).hom).app
        ((normalizedLiftedQ F).obj X) := by
  let e := rebaseFunctorIso (liftedQ F) (AsSmall.up.obj EC.qZero)
    (AsSmall.up.obj ED.qZero) (liftedZeroIso F)
  change e.inv.app X ≫ (liftedQ F).map
    ((UniversePromotion.liftTransformation.{u, v} (identityQAut EC a).hom).app X) ≫
      e.hom.app X = _
  rw [liftedQ_identityQAut F a b h]
  have hn := (UniversePromotion.liftTransformation.{v, u} (identityQAut ED b).hom).naturality
    (e.hom.app X)
  change e.hom.app X ≫
      (UniversePromotion.liftTransformation.{v, u} (identityQAut ED b).hom).app
        ((normalizedLiftedQ F).obj X) =
    (UniversePromotion.liftTransformation.{v, u} (identityQAut ED b).hom).app
      ((liftedQ F).obj X) ≫ e.hom.app X at hn
  rw [← hn, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem normalizedLiftedQ_homotopy (a : Aut (𝟭 C)) (b : Aut (𝟭 D))
    (h : ∀ X, F.toFunctor.map (a.hom.app X) = b.hom.app (F.toFunctor.obj X))
    (t : unitInterval) (x : ClassifyingSpace (AsSmall.{max u v} EC.QCategory)) :
    classifyingSpaceMap (normalizedLiftedQ F) (liftedHomotopy.{u, v} EC a (t, x)) =
      liftedHomotopy.{v, u} ED b
        (t, classifyingSpaceMap (normalizedLiftedQ F) x) := by
  have hw : Functor.whiskerRight
      (UniversePromotion.liftTransformation.{u, v} (identityQAut EC a).hom)
        (normalizedLiftedQ F) =
    Functor.whiskerLeft (normalizedLiftedQ F)
      (UniversePromotion.liftTransformation.{v, u} (identityQAut ED b).hom) := by
    apply NatTrans.ext
    funext X
    exact normalizedLiftedQ_identityQAut F a b h X
  change classifyingSpaceMap (normalizedLiftedQ F)
    (classifyingSpaceNaturalTransformationHomotopy _ (t, x)) =
      classifyingSpaceNaturalTransformationHomotopy _
        (t, classifyingSpaceMap (normalizedLiftedQ F) x)
  rw [← classifyingSpaceNaturalTransformationHomotopy_whiskerRight, hw,
    classifyingSpaceNaturalTransformationHomotopy_whiskerLeft]

/-- Compatible actual identity automorphisms commute with the original
zero-corrected universal K-map, even in independent small-category universes. -/
theorem universalKMap_operation (a : Aut (𝟭 C)) (b : Aut (𝟭 D))
    (h : ∀ X, F.toFunctor.map (a.hom.app X) = b.hom.app (F.toFunctor.obj X))
    (m : ℕ) (z : EC.K m) :
    F.universalKMap (m + 1)
      (IdentityTrack.operation (IdentityAutomorphism.homotopy EC a).toHomotopy
        (IdentityAutomorphism.homotopy_fixed EC a) m z) =
      IdentityTrack.operation (IdentityAutomorphism.homotopy ED b).toHomotopy
        (IdentityAutomorphism.homotopy_fixed ED b) m (F.universalKMap m z) := by
  apply upKMap_injective.{v, u} ED (m + 1)
  rw [universalKMap_up_square, upKMap_operation, upKMap_operation]
  rw [IdentityTrack.operation_natural (liftedHomotopy.{u, v} EC a)
    (liftedHomotopy_fixed EC a) (liftedHomotopy.{v, u} ED b)
    (liftedHomotopy_fixed ED b) (classifyingSpaceMap (normalizedLiftedQ F)).hom
    (rebaseFunctor_map_point _ _ _ _) (normalizedLiftedQ_homotopy F a b h)]
  rw [universalKMap_up_square]

/-- Degree-zero scalar-type operations retain the original universal K-map. -/
theorem universalKMap_kZeroAction (a : Aut (𝟭 C)) (b : Aut (𝟭 D))
    (h : ∀ X, F.toFunctor.map (a.hom.app X) = b.hom.app (F.toFunctor.obj X))
    (z : EC.K 0) :
    F.universalKMap 1 (IdentityAutomorphism.kZeroAction EC a z) =
      IdentityAutomorphism.kZeroAction ED b (F.universalKMap 0 z) :=
  universalKMap_operation F a b h 0 z

/-- Degree-one scalar-type operations retain the original universal K-map. -/
theorem universalKMap_kOneAction (a : Aut (𝟭 C)) (b : Aut (𝟭 D))
    (h : ∀ X, F.toFunctor.map (a.hom.app X) = b.hom.app (F.toFunctor.obj X))
    (z : EC.K 1) :
    F.universalKMap 2 (IdentityAutomorphism.kOneAction EC a z) =
      IdentityAutomorphism.kOneAction ED b (F.universalKMap 1 z) :=
  universalKMap_operation F a b h 1 z

private def fundamentalNaturality :
    classifyingFundamentalGroupoidFunctor EC.QCategory ⋙
        FundamentalGroupoid.map (classifyingSpaceMapUniversal F.mapQ) ≅
      F.mapQ ⋙ classifyingFundamentalGroupoidFunctor ED.QCategory :=
  NatIso.ofComponents (fun X => eqToIso (congrArg FundamentalGroupoid.mk
      (classifyingSpaceMapUniversal_point F.mapQ X))) (by
    intro X Y f
    apply (cancel_epi (eqToHom (congrArg FundamentalGroupoid.mk
      (classifyingSpaceMapUniversal_point F.mapQ X).symm))).1
    simp only [eqToIso, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [Category.assoc]
    change eqToHom (congrArg FundamentalGroupoid.mk
        (classifyingSpaceMapUniversal_point F.mapQ X).symm) ≫
      (⟦(classifyingSpacePath f).map (classifyingSpaceMapUniversal F.mapQ).continuous⟧ :
        Path.Homotopic.Quotient _ _) ≫
      eqToHom (congrArg FundamentalGroupoid.mk
        (classifyingSpaceMapUniversal_point F.mapQ Y)) = _
    rw [FundamentalGroupoid.conj_eqToHom
      (classifyingSpaceMapUniversal_point F.mapQ X).symm
      (classifyingSpaceMapUniversal_point F.mapQ Y).symm]
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact classifyingSpaceMapUniversal_path F.mapQ f t)

private theorem mapQ_fromZero (X : C) :
    (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom ≫
        ED.fromZero (Q.of ED.deflation ED.inflation (F.toFunctor.obj X)) =
      F.mapQ.map (EC.fromZero (Q.of EC.deflation EC.inflation X)) := by
  let e := F.toFunctor.mapZeroObject
  change Q.mkHom ED.deflation ED.inflation (Q.isoSpan _ _ e _) ≫
    Q.mkHom ED.deflation ED.inflation _ = Q.mkHom ED.deflation ED.inflation _
  have h : IsPullback (𝟙 (F.toFunctor.obj (0 : C))) e.hom e.hom (𝟙 (0 : D)) :=
    IsPullback.of_horiz_isIso ⟨by exact Subsingleton.elim _ _⟩
  apply ED.q_comp_of_isPullback _ _ _ _ h _ (Iso.refl _)
  · simp [QCompatibleFunctor.mapSpan, Q.isoSpan, Q.of,
      CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]
    simpa using F.toFunctor.mapZeroObject.hom_inv_id
  · simp [QCompatibleFunctor.mapSpan, Q.of,
      CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]

private theorem mapQ_fromZeroTotal (X : C) :
    (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom ≫
        ED.fromZeroTotal (Q.of ED.deflation ED.inflation (F.toFunctor.obj X)) =
      F.mapQ.map (EC.fromZeroTotal (Q.of EC.deflation EC.inflation X)) := by
  let e := F.toFunctor.mapZeroObject
  change Q.mkHom ED.deflation ED.inflation (Q.isoSpan _ _ e _) ≫
    Q.mkHom ED.deflation ED.inflation _ = Q.mkHom ED.deflation ED.inflation _
  have h : IsPullback (0 : F.toFunctor.obj X ⟶ F.toFunctor.obj (0 : C))
      (𝟙 (F.toFunctor.obj X)) e.hom (0 : F.toFunctor.obj X ⟶ 0) :=
    (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  apply ED.q_comp_of_isPullback _ _ _ _ h _ (Iso.refl _)
  · simp [QCompatibleFunctor.mapSpan, Q.isoSpan, Q.of,
      CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]
  · simp [QCompatibleFunctor.mapSpan, Q.of,
      CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]

private theorem qObjectClass_mapQ {T : Type*} [Groupoid T]
    (H : ED.QCategory ⥤ T) (X : C) :
    (H.mapIso (ED.qIsoOfIso F.toFunctor.mapZeroObject)).conj
        (EC.qObjectClass (F.mapQ ⋙ H) X) =
      ED.qObjectClass H (F.toFunctor.obj X) := by
  simp only [Iso.conj_apply, ExactStructure.qObjectClass, Functor.comp_map,
    Functor.mapIso_inv, Functor.mapIso_hom]
  rw [← mapQ_fromZeroTotal F X]
  simp only [← Groupoid.inv_eq_inv]
  rw [← mapQ_fromZero F X]
  simp [Category.assoc, Groupoid.inv_eq_inv]

private theorem pathClass_cast {Y : Type*} [TopologicalSpace Y]
    {x x' y : Y} (p : Path x y) (h : x' = x) :
    (⟦p.cast h rfl⟧ : FundamentalGroupoid.mk x' ⟶ FundamentalGroupoid.mk y) =
      eqToHom (congrArg FundamentalGroupoid.mk h) ≫
        (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) := by
  subst x'
  simp

/-- Every original object class is preserved by the actual zero-corrected
universal K-map, with independent endpoint universes. -/
theorem universalKMap_objectClass (X : C) :
    F.universalKMap 0 (EC.kZeroObjectClass X) =
      ED.kZeroObjectClass (F.toFunctor.obj X) := by
  let H := classifyingFundamentalGroupoidFunctor ED.QCategory
  let η := fundamentalNaturality F
  let e := ED.qIsoOfIso F.toFunctor.mapZeroObject
  have he : (η.app EC.qZero ≪≫ H.mapIso e).hom =
      (⟦F.universalQZeroBasePath⟧ :
        FundamentalGroupoid.mk (classifyingSpaceMapUniversal F.mapQ EC.kBasepoint) ⟶
          FundamentalGroupoid.mk ED.kBasepoint) := by
    change eqToHom (congrArg FundamentalGroupoid.mk
        (classifyingSpaceMapUniversal_point F.mapQ EC.qZero)) ≫
      (⟦classifyingSpacePath e.hom⟧ : Path.Homotopic.Quotient _ _) =
      ⟦(classifyingSpacePath e.hom).cast
        (classifyingSpaceMapUniversal_point F.mapQ EC.qZero) rfl⟧
    exact (pathClass_cast _ _).symm
  have hep : (Groupoid.isoEquivHom
      (FundamentalGroupoid.mk (classifyingSpaceMapUniversal F.mapQ EC.kBasepoint))
      (FundamentalGroupoid.mk ED.kBasepoint)).symm ⟦F.universalQZeroBasePath⟧ =
      η.app EC.qZero ≪≫ H.mapIso e := by
    apply Iso.ext
    exact he.symm
  apply ED.kZeroFundamentalGroupEquiv.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (pathTransport F.universalQZeroBasePath 1
      (homotopyGroupMap (classifyingSpaceMapUniversal F.mapQ) rfl
        (EC.kZeroObjectClass X))) = _
  rw [piOneEquivFundamentalGroup_pathTransport]
  change FundamentalGroup.fundamentalGroupMulEquivOfPath F.universalQZeroBasePath
    (HomotopyGroup.pi1MulEquivFundamentalGroup
      (piMap 0 (classifyingSpaceMapUniversal F.mapQ) rfl (EC.kZeroObjectClass X))) = _
  rw [piOneEquivFundamentalGroup_naturality]
  change FundamentalGroup.fundamentalGroupMulEquivOfPath F.universalQZeroBasePath
    (FundamentalGroup.mapOfEq (classifyingSpaceMapUniversal F.mapQ) rfl
      (EC.kZeroFundamentalGroupEquiv (EC.kZeroObjectClass X))) =
    ED.kZeroFundamentalGroupEquiv (ED.kZeroObjectClass (F.toFunctor.obj X))
  rw [EC.kZeroFundamentalGroupEquiv_objectClass, ED.kZeroFundamentalGroupEquiv_objectClass,
    EC.kZeroObjectLoop_eq_qObjectClass, ED.kZeroObjectLoop_eq_qObjectClass,
    FundamentalGroup.fundamentalGroupMulEquivOfPath, hep, Iso.trans_conj]
  have hn := EC.qObjectClass_natIso η X
  rw [EC.qObjectClass_comp] at hn
  simp only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  change (H.mapIso e).conj ((η.app EC.qZero).conj
    ((FundamentalGroupoid.map (classifyingSpaceMapUniversal F.mapQ)).map
      (EC.qObjectClass (classifyingFundamentalGroupoidFunctor EC.QCategory) X))) = _
  rw [← hn]
  exact qObjectClass_mapQ F H X

end IndependentCategories

section ModelObjects
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [EssentiallySmall.{s₁} C] [EssentiallySmall.{s₂} C] (E : ExactStructure C)

/-- The canonical model comparison preserves the original object class of
every original object, including its original chosen-model unit isomorphism. -/
theorem smallKUniverseEquiv_objectClass (X : C) :
    E.smallKUniverseEquiv.{s₁, s₂} 0
        (E.smallModel.{s₁}.kZeroObjectClass ((equivSmallModel.{s₁} C).functor.obj X)) =
      E.smallModel.{s₂}.kZeroObjectClass ((equivSmallModel.{s₂} C).functor.obj X) := by
  have h := universalKMap_objectClass (E.smallModelUniverseComparison.{s₁, s₂})
    ((equivSmallModel.{s₁} C).functor.obj X)
  exact h.trans (E.smallModel.{s₂}.kZeroObjectClass_iso
    ((equivSmallModel.{s₂} C).functor.mapIso ((equivSmallModel.{s₁} C).unitIso.app X).symm))

end ModelObjects

section ScalarModels
universe r c h
variable (R : Type r) [Ring R] {C : Type c} [Category.{h} C]
  [Preadditive C] [HasFiniteBiproducts C] [Linear R C]
  [EssentiallySmall.{s₁} C] [EssentiallySmall.{s₂} C] (E : ExactStructure C)

/-- The original comparison preserves the descended scalar components without
putting a linear structure on either chosen model. -/
theorem smallModelUniverseComparison_scalar (a : Rˣ) (X : SmallModel.{s₁} C) :
    (E.smallModelUniverseComparison.{s₁, s₂}).toFunctor.map
        ((smallModelScalarNatAut.{r, c, h, s₁} R C a).hom.app X) =
      (smallModelScalarNatAut.{r, c, h, s₂} R C a).hom.app
        ((E.smallModelUniverseComparison.{s₁, s₂}).toFunctor.obj X) := by
  change (equivSmallModel.{s₂} C).functor.map
    ((equivSmallModel.{s₁} C).inverse.map
      ((smallModelScalarNatAut.{r, c, h, s₁} R C a).hom.app X)) = _
  rw [smallModelScalarNatAut_map_hom]
  exact smallModelScalarNatAut_functor_map_hom.{r, c, h, s₂} R C a _

/-- The canonical comparison of model universes preserves the actual scalar
K0-to-K1 action and its original normalization. -/
theorem smallKUniverseEquiv_kZeroAction (a : Rˣ) (z : E.SmallK.{s₁} 0) :
    E.smallKUniverseEquiv.{s₁, s₂} 1
        (ScalarUnit.smallModelKZeroAction.{r, c, h, s₁} R E a z) =
      ScalarUnit.smallModelKZeroAction.{r, c, h, s₂} R E a
        (E.smallKUniverseEquiv.{s₁, s₂} 0 z) :=
  universalKMap_kZeroAction (E.smallModelUniverseComparison.{s₁, s₂})
    (smallModelScalarNatAut.{r, c, h, s₁} R C a)
    (smallModelScalarNatAut.{r, c, h, s₂} R C a)
    (fun X => smallModelUniverseComparison_scalar R E a X) z

/-- The canonical comparison of model universes preserves the actual scalar
K1-to-K2 action and its original normalization. -/
theorem smallKUniverseEquiv_kOneAction (a : Rˣ) (z : E.SmallK.{s₁} 1) :
    E.smallKUniverseEquiv.{s₁, s₂} 2
        (ScalarUnit.smallModelKOneAction.{r, c, h, s₁} R E a z) =
      ScalarUnit.smallModelKOneAction.{r, c, h, s₂} R E a
        (E.smallKUniverseEquiv.{s₁, s₂} 1 z) :=
  universalKMap_kOneAction (E.smallModelUniverseComparison.{s₁, s₂})
    (smallModelScalarNatAut.{r, c, h, s₁} R C a)
    (smallModelScalarNatAut.{r, c, h, s₂} R C a)
    (fun X => smallModelUniverseComparison_scalar R E a X) z

/-- The canonical model comparison carries the literal positive cube of the
original scalar automorphism to the same positive cube in the other model.
Both normalization inverses are retained before cancelling them. -/
theorem smallKUniverseEquiv_positiveScalarCube (a : Rˣ) (X : C) :
    E.smallKUniverseEquiv.{s₁, s₂} 1
        (Quotient.mk' (Automorphism.Cube.automorphismFirstCube E.smallModel.{s₁}
          ((equivSmallModel.{s₁} C).functor.obj X)
          ((equivSmallModel.{s₁} C).functor.mapIso ((scalarNatAut R C a).app X)))) =
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube E.smallModel.{s₂}
        ((equivSmallModel.{s₂} C).functor.obj X)
        ((equivSmallModel.{s₂} C).functor.mapIso ((scalarNatAut R C a).app X))) :
          E.SmallK.{s₂} 1) := by
  have h := smallKUniverseEquiv_kZeroAction.{s₁, s₂, r, c, h} R E a
    (E.smallModel.{s₁}.kZeroObjectClass ((equivSmallModel.{s₁} C).functor.obj X))
  have h₁ := ObjectClass.smallModelKZeroAction_mapped_objectClass_cube.{c, h, r, s₁} R E a X
  have h₂ := ObjectClass.smallModelKZeroAction_mapped_objectClass_cube.{c, h, r, s₂} R E a X
  rw [smallKUniverseEquiv_objectClass, h₁, h₂, map_inv] at h
  exact inv_injective h

end ScalarModels

section FiniteModules
variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/-- The original lower-to-upper finite-module comparison preserves its actual
scalar K0-to-K1 operation. -/
theorem finiteModule_kZeroAction_universe (a : Rˣ)
    (z : (ModuleCat.finiteModuleExactStructure.{u, u} R).SmallK.{u} 0) :
    (ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} 1
        (ScalarUnit.smallModelKZeroAction.{u, u + 1, u, u} R
          (ModuleCat.finiteModuleExactStructure.{u, u} R) a z) =
      ScalarUnit.upperFiniteModuleKZeroAction R a
        ((ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} 0 z) :=
  smallKUniverseEquiv_kZeroAction.{u, u + 1, u, u + 1, u} R
    (ModuleCat.finiteModuleExactStructure.{u, u} R) a z

/-- The original lower-to-upper finite-module comparison preserves its actual
scalar K1-to-K2 operation. -/
theorem finiteModule_kOneAction_universe (a : Rˣ)
    (z : (ModuleCat.finiteModuleExactStructure.{u, u} R).SmallK.{u} 1) :
    (ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} 2
        (ScalarUnit.smallModelKOneAction.{u, u + 1, u, u} R
          (ModuleCat.finiteModuleExactStructure.{u, u} R) a z) =
      ScalarUnit.upperFiniteModuleKOneAction R a
        ((ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} 1 z) :=
  smallKUniverseEquiv_kOneAction.{u, u + 1, u, u + 1, u} R
    (ModuleCat.finiteModuleExactStructure.{u, u} R) a z

omit [IsNoetherianRing R] in
private theorem scalarMatrixAut (n : ℕ) (a : Rˣ) :
    (scalarNatAut R (FGModuleCat.{u} R) a).app (FGModuleCat.of R (Fin n → R)) =
      FGModuleCat.matrixToAut R n (Matrix.GeneralLinearGroup.scalar (Fin n) a) := by
  apply Iso.ext
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((scalarNatAut R (FGModuleCat.{u} R) a).hom.app
    (FGModuleCat.of R (Fin n → R))) x =
    (FGModuleCat.matrixToAut R n (Matrix.GeneralLinearGroup.scalar (Fin n) a)).hom x
  rw [FGModuleCat.matrixToAut_apply]
  change (fun i : Fin n => (a : R) * x i) = (Matrix.scalar (Fin n) (a : R)).mulVec x
  funext i
  simp only [Matrix.scalar_apply, Matrix.mulVec_diagonal]

/-- The original lower-to-upper comparison preserves the actual finite scalar
matrix's positive cube, in every finite rank. -/
theorem finiteModule_positiveScalarCube_universe (n : ℕ) (a : Rˣ) :
    (ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} 1
        (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
          (ModuleCat.finiteModuleExactStructure.{u, u} R).smallModel.{u}
          ((equivSmallModel.{u} (FGModuleCat.{u} R)).functor.obj
            (FGModuleCat.of R (Fin n → R)))
          ((equivSmallModel.{u} (FGModuleCat.{u} R)).functor.mapIso
            (FGModuleCat.matrixToAut R n (Matrix.GeneralLinearGroup.scalar (Fin n) a))))) =
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} R).smallModel.{u + 1}
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} R)).functor.obj
          (FGModuleCat.of R (Fin n → R)))
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} R)).functor.mapIso
          (FGModuleCat.matrixToAut R n (Matrix.GeneralLinearGroup.scalar (Fin n) a)))) :
            (ModuleCat.finiteModuleExactStructure.{u, u} R).SmallK.{u + 1} 1) := by
  simpa only [scalarMatrixAut] using
    (smallKUniverseEquiv_positiveScalarCube.{u, u + 1, u, u + 1, u} R
      (ModuleCat.finiteModuleExactStructure.{u, u} R) a (FGModuleCat.of R (Fin n → R)))

end FiniteModules

section FieldConsumer
variable (F : Type u) [Field F]

/-- The canonical lower image of the existing upper field unit product is the
original lower scalar operation on the literal positive rank-one matrix cube.
This is a model-universe comparison, with no Milnor-symbol identification. -/
theorem field_unitProduct_eq_lowerScalarCubeAction (a b : Fˣ) :
    ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallKUniverseEquiv.{u, u + 1} 2).symm
        (FieldSymbols.unitProduct F a b) =
      ScalarUnit.smallModelKOneAction.{u, u + 1, u, u} F
        (ModuleCat.finiteModuleExactStructure.{u, u} F) a
        (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
          (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u}
          ((equivSmallModel.{u} (FGModuleCat.{u} F)).functor.obj
            (FGModuleCat.of F (Fin 1 → F)))
          ((equivSmallModel.{u} (FGModuleCat.{u} F)).functor.mapIso
            (FGModuleCat.matrixToAut F 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) b))))) := by
  apply ((ModuleCat.finiteModuleExactStructure.{u, u}
    F).smallKUniverseEquiv.{u, u + 1} 2).injective
  rw [MulEquiv.apply_symm_apply, finiteModule_kOneAction_universe,
    finiteModule_positiveScalarCube_universe]
  unfold FieldSymbols.unitProduct
  rw [FieldSymbols.positiveUnitKOne_cube]

end FieldConsumer

end Quillen.LowDegreeScalarAction.UniverseNaturality
