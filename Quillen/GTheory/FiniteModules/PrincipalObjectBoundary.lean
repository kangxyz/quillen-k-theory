/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.Algebra.Category.FGModuleCat.PrincipalRankOne
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.ClosedDevissage
public import Quillen.KTheory.Automorphism.Isomorphism
public import Quillen.KTheory.Automorphism.PositiveNormalization
public import Quillen.KTheory.GrothendieckComparison.Equivalence
public import Quillen.KTheory.GrothendieckComparison.Naturality
public import Quillen.KTheory.SpaceAction
public import Quillen.Localization.Serre.LocalizationTarget
public import Quillen.Topology.ClassifyingSpace.NaturalTransformationLoopCancellation
public import Quillen.Topology.HomotopyFiber.SourceContractionBoundary
public import Quillen.Topology.HomotopyGroups.LoopNormalizationProduct
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# The original principal boundary on a positive rank-one automorphism cube

The original Serre comparison sends the full/zero Q walking pair of a cokernel
into the actual path-space fiber. The conflation Q identities give an ambient
contraction. Its quotient image factors through the unchanged epsilon cylinder
and the original full and zero cones. Whole-source cylinder cancellation, with
its actual basepoint track, identifies the resulting loop family with the core
loop family. The original left cap and right cap agree at the class level by the
proved trivial action on the actual Q-space. The walking-pair generator traverses
the image automorphism backwards, so it represents the original positive cube.

The resulting boundary is the supported cokernel object class with positive sign.
The actual quotient lift, exact identity comparisons, small-model units and
closed restriction functor then specialize this formula to the original
`closedConnectingHom` and the literal Fin 1 rank-one modules. The zero-cokernel
and unit cases are included. No product or symbol marking is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject Topology unitInterval nonZeroDivisors

namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) {A K : C} (f : A ⟶ A) (q : A ⟶ K) (hfq : f ≫ q = 0)
  (hS : E.conflation (ShortComplex.mk f q hfq))

/-- The full/zero pair representing the original cokernel object loop. -/
def supportPair : WalkingParallelPair ⥤ E.QCategory :=
  parallelPair (E.fromZeroTotal (Q.of _ _ K)) (E.fromZero (Q.of _ _ K))

/-- The actual endomorphism pair, in the orientation id followed by the inflation. -/
def endomorphismPair : WalkingParallelPair ⥤ E.QCategory :=
  parallelPair (𝟙 (Q.of _ _ A)) (E.qInflation f (E.inflation_of_conflation hS))

/-- The original Q conflation identities supply both naturality squares. -/
def cokernelToEndomorphism : supportPair E (K := K) ⟶ endomorphismPair E f q hfq hS :=
  parallelPairHom _ _ _ _ (E.fromZeroTotal (Q.of _ _ A))
    (E.qDeflation q (E.deflation_of_conflation hS))
    (by simpa only [Category.comp_id] using
      E.fromZeroTotal_qDeflation q (E.deflation_of_conflation hS))
    (E.conflation_q_relation hS)

/-- The zero-apex relation supplies the second actual natural transformation. -/
def zeroToEndomorphism :
    (Functor.const WalkingParallelPair).obj E.qZero ⟶ endomorphismPair E f q hfq hS :=
  parallelPairHomMk (E.fromZero (Q.of _ _ A)) (E.fromZero (Q.of _ _ A))
    (by simp [endomorphismPair])
    (by
      change 𝟙 _ ≫ E.fromZero (Q.of _ _ A) =
        E.fromZero (Q.of _ _ A) ≫ E.qInflation f (E.inflation_of_conflation hS)
      simpa only [Category.id_comp] using
        (E.fromZero_qInflation f (E.inflation_of_conflation hS)).symm)

/-- An actual common-universe walking pair, with no new categorical relations. -/
abbrev CircleCategory := AsSmall.{u} WalkingParallelPair

/-- The original cokernel diagram on that actual small walking pair. -/
def supportedDiagram : CircleCategory ⥤ E.QCategory := AsSmall.down ⋙ supportPair E (K := K)

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary

namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- Exact functors preserve the actual forward inflation span. -/
theorem mapQ_qInflation {A B : C} (f : A ⟶ B) (hf : EC.inflation f) :
    F.mapQ.map (EC.qInflation f hf) = ED.qInflation (F.toFunctor.map f) (F.map_inflation f hf) := by
  change Q.mkHom _ _ _ = Q.mkHom _ _ _
  apply Q.mkHom_eq_of_apexIso _ _ _ _ (Iso.refl (F.toFunctor.obj A))
  · change 𝟙 _ ≫ 𝟙 _ = F.toFunctor.map (𝟙 A)
    simp
  · change 𝟙 _ ≫ F.toFunctor.map f = F.toFunctor.map f
    simp

/-- Exact functors preserve the actual reverse quotient span. -/
theorem mapQ_qDeflation {A B : C} (q : A ⟶ B) (hq : EC.deflation q) :
    F.mapQ.map (EC.qDeflation q hq) = ED.qDeflation (F.toFunctor.map q) (F.map_deflation q hq) := by
  change Q.mkHom _ _ _ = Q.mkHom _ _ _
  apply Q.mkHom_eq_of_apexIso _ _ _ _ (Iso.refl (F.toFunctor.obj A))
  · change 𝟙 _ ≫ F.toFunctor.map q = F.toFunctor.map q
    simp
  · change 𝟙 _ ≫ 𝟙 _ = F.toFunctor.map (𝟙 A)
    simp

/-- Once the original target arrow is invertible, its inflation span is its original Q-iso. -/
theorem qInflation_asIso {A B : D} (f : A ⟶ B) [IsIso f] (hf : ED.inflation f) :
    ED.qInflation f hf = (ED.qIsoOfIso (asIso f)).hom := rfl

/-- A quotient onto an original zero object is precisely the full-apex arm
preceded by the specified original zero-object isomorphism. -/
theorem qDeflation_zero_target {A B : D} (q : A ⟶ B) (hq : ED.deflation q) (e : B ≅ 0) :
    ED.qDeflation q hq = (ED.qIsoOfIso e).hom ≫ Automorphism.fullFromZero ED A := by
  have hs : IsPullback q (𝟙 A) e.hom (0 : A ⟶ 0) :=
    IsPullback.of_vert_isIso ⟨(isZero_zero D).eq_of_tgt _ _⟩
  symm
  apply ED.q_comp_of_isPullback _ _ _ _ hs _ (Iso.refl _)
  · change 𝟙 A ≫ q = q ≫ 𝟙 B
    simp
  · simp

open Automorphism.Diagram

/-- The actual zero-normalized map retains the quotient span with exactly its object transports. -/
theorem normalizedQ_qDeflation {A B : C} (q : A ⟶ B) (hq : EC.deflation q)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    eqToHom (normalizedQ_obj F B hB).symm ≫ F.normalizedQ.map (EC.qDeflation q hq) ≫
        eqToHom (normalizedQ_obj F A hA) =
      ED.qDeflation (F.toFunctor.map q) (F.map_deflation q hq) := by
  classical
  simp only [ExactFunctor.normalizedQ, rebaseFunctor, rebaseObjIso,
    dite_eq_right (qObj_ne_zero (EC := EC) A hA),
    dite_eq_right (qObj_ne_zero (EC := EC) B hB), eqToIso.hom, eqToIso.inv, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact mapQ_qDeflation F q hq

/-- The actual normalized inflation becomes the image automorphism with the original transports. -/
theorem normalizedQ_qInflation_iso {A : C} (f : A ⟶ A) (hf : EC.inflation f)
    [IsIso (F.toFunctor.map f)] (hA : A ≠ 0) :
    eqToHom (normalizedQ_obj F A hA).symm ≫ F.normalizedQ.map (EC.qInflation f hf) ≫
        eqToHom (normalizedQ_obj F A hA) =
      (ED.qIsoOfIso (asIso (F.toFunctor.map f))).hom := by
  classical
  simp only [ExactFunctor.normalizedQ, rebaseFunctor, rebaseObjIso,
    dite_eq_right (qObj_ne_zero (EC := EC) A hA), eqToIso.hom, eqToIso.inv, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact (mapQ_qInflation F f hf).trans (qInflation_asIso _ _)

/-- The actual image automorphism row of the walking pair. -/
def imageCorePair {A : C} (f : A ⟶ A) [IsIso (F.toFunctor.map f)] :
    CircleCategory ⥤ Core D :=
  AsSmall.down ⋙ parallelPair (𝟙 (Core.mk (F.toFunctor.obj A)))
    (CoreHom.mk (asIso (F.toFunctor.map f)))

/-- The original normalized Q endomorphism row is the actual image core row. -/
theorem normalizedEndomorphismPair_eq {A K : C} (f : A ⟶ A) (q : A ⟶ K)
    (hfq : f ≫ q = 0) (hS : EC.conflation (ShortComplex.mk f q hfq))
    [IsIso (F.toFunctor.map f)] (hA : A ≠ 0) :
    (AsSmall.down ⋙ endomorphismPair EC f q hfq hS) ⋙ F.normalizedQ =
      imageCorePair F f ⋙ Automorphism.coreQ ED := by
  have h : endomorphismPair EC f q hfq hS ⋙ F.normalizedQ =
      parallelPair (𝟙 (Q.of ED.deflation ED.inflation (F.toFunctor.obj A)))
        (ED.qIsoOfIso (asIso (F.toFunctor.map f))).hom := by
    refine CategoryTheory.Functor.ext (fun j => ?_) ?_
    · cases j <;> exact normalizedQ_obj F A hA
    · intro X Y g
      cases g with
      | id => cases X <;> simp [endomorphismPair]
      | left => simp [endomorphismPair]
      | right =>
        change F.normalizedQ.map (EC.qInflation f (EC.inflation_of_conflation hS)) =
          eqToHom (normalizedQ_obj F A hA) ≫
            (ED.qIsoOfIso (asIso (F.toFunctor.map f))).hom ≫
              eqToHom (normalizedQ_obj F A hA).symm
        apply (cancel_epi (eqToHom (normalizedQ_obj F A hA).symm)).mp
        apply (cancel_mono (eqToHom (normalizedQ_obj F A hA))).mp
        simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
          Category.id_comp, Category.comp_id] using
          normalizedQ_qInflation_iso F f (EC.inflation_of_conflation hS) hA
  have hk : parallelPair (𝟙 (Core.mk (F.toFunctor.obj A)))
      (CoreHom.mk (asIso (F.toFunctor.map f))) ⋙ Automorphism.coreQ ED =
      parallelPair (𝟙 (Q.of ED.deflation ED.inflation (F.toFunctor.obj A)))
        (ED.qIsoOfIso (asIso (F.toFunctor.map f))).hom := by
    refine CategoryTheory.Functor.hext (fun j => ?_) ?_
    · cases j <;> rfl
    · intro X Y g
      cases g with
      | id => cases X <;> rfl
      | left => rfl
      | right => rfl
  exact congrArg (fun T => AsSmall.down ⋙ T) (h.trans hk.symm)

/-- The normalized constant-zero row is exactly the target constant-zero row. -/
theorem normalizedConst_eq {B : Type u} [SmallCategory B] :
    (Functor.const B).obj EC.qZero ⋙ F.normalizedQ = (Functor.const B).obj ED.qZero := by
  refine CategoryTheory.Functor.ext (fun _ => normalizedQ_zero F) ?_
  intro X Y g
  simp

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary

namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
open SerreLocalization Automorphism.Diagram
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] Quillen.SerreLocalization.canonicalQuotientAbelian
variable {C : Type u} [SmallCategory C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]
  (K : P.FullSubcategory) (hK : ¬ IsZero K.obj)

include hK in
/-- A nonzero underlying supported object is not the chosen support zero. -/
theorem supported_ne_zero : K ≠ 0 := by
  intro h
  subst K
  exact hK (P.ι.map_isZero (isZero_zero P.FullSubcategory))

omit [P.IsSerreClass] in
include hK in
/-- A nonzero underlying object is not the chosen ambient zero. -/
theorem underlying_ne_zero : K.obj ≠ 0 := by
  intro h
  apply hK
  rw [h]
  exact isZero_zero C

/-- The exact inclusion's original normalized Q-functor sends the supported
full/zero pair to the ambient pair, with its canonical endpoint equalities. -/
def supportInclusionComparison :
    supportedDiagram (ObjectProperty.subcategoryExactStructure P) (K := K) ⋙
        inclusionNormalizedQ P ≅
      supportedDiagram (abelianExactStructure C) (K := K.obj) := by
  let J := ObjectProperty.exactInclusion P
  let h₀ := normalizedQ_zero J
  let h₁ := normalizedQ_obj J K (supported_ne_zero P K hK)
  let e : supportPair (ObjectProperty.subcategoryExactStructure P) (K := K) ⋙ J.normalizedQ ≅
      supportPair (abelianExactStructure C) (K := K.obj) :=
    parallelPairIsoMk (eqToIso h₀) (eqToIso h₁) (by
      change J.normalizedQ.map (Automorphism.fullFromZero _ K) ≫ eqToHom h₁ =
        eqToHom h₀ ≫ Automorphism.fullFromZero _ K.obj
      apply (cancel_epi (eqToHom h₀.symm)).mp
      simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp] using
        (show eqToHom h₀.symm ≫ J.normalizedQ.map (Automorphism.fullFromZero _ K) ≫
          eqToHom h₁ = Automorphism.fullFromZero _ K.obj from
            normalizedQ_fullArm J K (supported_ne_zero P K hK))) (by
      change J.normalizedQ.map ((ObjectProperty.subcategoryExactStructure P).fromZero
          (Q.of _ _ K)) ≫ eqToHom h₁ =
        eqToHom h₀ ≫ (abelianExactStructure C).fromZero (Q.of _ _ K.obj)
      apply (cancel_epi (eqToHom h₀.symm)).mp
      simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp] using
        (show eqToHom h₀.symm ≫ J.normalizedQ.map
          ((ObjectProperty.subcategoryExactStructure P).fromZero (Q.of _ _ K)) ≫
            eqToHom h₁ = (abelianExactStructure C).fromZero (Q.of _ _ K.obj) from
              normalizedQ_zeroArm J K (supported_ne_zero P K hK)))
  exact Functor.isoWhiskerLeft AsSmall.down e

variable {A : C} (f : A ⟶ A) (q : A ⟶ K.obj) (hfq : f ≫ q = 0)
  (hS : (abelianExactStructure C).conflation (ShortComplex.mk f q hfq))

/-- The original normalized inclusion is followed by the actual cokernel comparison. -/
def actualCokernelToEndomorphism :
    supportedDiagram (ObjectProperty.subcategoryExactStructure P) (K := K) ⋙
        inclusionNormalizedQ P ⟶
      AsSmall.down ⋙ endomorphismPair (abelianExactStructure C) f q hfq hS :=
  (supportInclusionComparison P K hK).hom ≫
    Functor.whiskerLeft AsSmall.down (cokernelToEndomorphism (abelianExactStructure C) f q hfq hS)

/-- The actual supported comparison composed with the displayed full/zero walking pair. -/
def supportedCircleFiberMap :
    C(ClassifyingSpace CircleCategory, NormalizedLocalizationFiber P) :=
  (basedLocalizationFiberComparison P).comp
    (classifyingSpaceMap (supportedDiagram (ObjectProperty.subcategoryExactStructure P)
      (K := K))).hom

/-- The two original transformations contract precisely the source projection
of the maintained Serre fiber comparison, retaining the original epsilon path. -/
def actualAmbientContraction :
    ((HomotopyFiber.projection (classifyingSpaceMap (quotientNormalizedQ P)).hom
      (abelianExactStructure P.isoModSerre.Localization).kBasepoint).comp
        (supportedCircleFiberMap P K)).Homotopy
      (ContinuousMap.const _ (abelianExactStructure C).kBasepoint) :=
  ((classifyingSpaceNaturalTransformationHomotopy
      (actualCokernelToEndomorphism P K hK f q hfq hS)).trans
    (classifyingSpaceNaturalTransformationHomotopy
      (Functor.whiskerLeft AsSmall.down
        (zeroToEndomorphism (abelianExactStructure C) f q hfq hS))).symm).cast
      (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)
      (by
        change (classifyingSpaceMap
          ((Functor.const CircleCategory).obj (abelianExactStructure C).qZero)).hom = _
        rw [classifyingSpaceMap_const_direct]
        rfl)

/-- The walking-pair basepoint is the actual source zero vertex. -/
def circleBasepoint : ClassifyingSpace CircleCategory :=
  classifyingSpacePoint (AsSmall.up.obj WalkingParallelPair.zero)

/-- The actual supported walking pair preserves its original zero vertex. -/
theorem supportedCircle_basepoint :
    supportedCircleFiberMap P K circleBasepoint.{u} = normalizedFiberBasepoint P := by
  have h := classifyingSpaceMap_point
    (supportedDiagram (ObjectProperty.subcategoryExactStructure P) (K := K))
    (AsSmall.up.obj WalkingParallelPair.zero)
  exact (congrArg (basedLocalizationFiberComparison P) h).trans
    (basedLocalizationFiberComparison_basepoint P)

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary

namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
open SerreLocalization Automorphism.Diagram
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] Quillen.SerreLocalization.canonicalQuotientAbelian
variable {C : Type u} [SmallCategory C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]
  (K : P.FullSubcategory) (hK : ¬ IsZero K.obj)
  {A : C} (f : A ⟶ A) (q : A ⟶ K.obj) (hfq : f ≫ q = 0)
  (hS : (abelianExactStructure C).conflation (ShortComplex.mk f q hfq))
  [IsIso ((ExactFunctor.serreLocalization P P.isoModSerre.Q).toFunctor.map f)] (hA : A ≠ 0)

/-- The original formal quotient exact functor. -/
abbrev quotientExact := ExactFunctor.serreLocalization P P.isoModSerre.Q
/-- The original supported full and zero pair. -/
abbrev supportRow := supportedDiagram (ObjectProperty.subcategoryExactStructure P) (K := K)
/-- The ambient endomorphism pair. -/
abbrev ambientRow := AsSmall.down ⋙ endomorphismPair (abelianExactStructure C) f q hfq hS
/-- The actual core image row. -/
abbrev targetCore := imageCorePair (quotientExact P) f

/-- The full original epsilon triangle on the entire walking pair. -/
theorem mappedCokernelTriangle :
    Functor.whiskerRight (actualCokernelToEndomorphism P K hK f q hfq hS)
        (quotientNormalizedQ P) ≫
      eqToHom (normalizedEndomorphismPair_eq (quotientExact P) f q hfq hS hA) =
    Functor.whiskerLeft (supportRow P K) (normalizedQuotientInclusionZeroIso P).hom ≫
      Functor.whiskerLeft (targetCore P f) (Automorphism.fullCone
        (abelianExactStructure P.isoModSerre.Localization)) := by
  apply NatTrans.ext
  funext X
  rcases X with ⟨X⟩
  cases X
  · dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      actualCokernelToEndomorphism]
    simp only [eqToHom_app]
    change (quotientExact P).normalizedQ.map
        (eqToHom (normalizedQ_zero (ObjectProperty.exactInclusion P)) ≫
          Automorphism.fullFromZero (abelianExactStructure C) A) ≫
      eqToHom (normalizedQ_obj (quotientExact P) A hA) =
        (normalizedQuotientInclusionZeroIso P).hom.app
          (ObjectProperty.subcategoryExactStructure P).qZero ≫
          Automorphism.fullFromZero (abelianExactStructure P.isoModSerre.Localization)
            ((quotientExact P).toFunctor.obj A)
    rw [Functor.map_comp, eqToHom_map, normalizedZeroIso_hom_base]
    apply (cancel_epi (eqToHom (normalizedComposite_obj_zero P).symm)).mp
    simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp] using normalizedQ_fullArm (quotientExact P) A hA
  · dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      actualCokernelToEndomorphism]
    simp only [eqToHom_app]
    change (quotientExact P).normalizedQ.map
        (eqToHom (normalizedQ_obj (ObjectProperty.exactInclusion P) K
          (supported_ne_zero P K hK)) ≫
          (abelianExactStructure C).qDeflation q
            ((abelianExactStructure C).deflation_of_conflation hS)) ≫
      eqToHom (normalizedQ_obj (quotientExact P) A hA) =
        (normalizedQuotientInclusionZeroIso P).hom.app (Q.of _ _ K) ≫
          Automorphism.fullFromZero (abelianExactStructure P.isoModSerre.Localization)
            ((quotientExact P).toFunctor.obj A)
    let e : P.isoModSerre.Q.obj K.obj ≅ 0 :=
      ((quotient_isZero_obj_iff P K.obj).2 K.property).iso (isZero_zero _)
    have he : (normalizedQuotientInclusionZeroIso P).hom.app (Q.of _ _ K) =
        (quotientExact P).normalizedQ.map
          (eqToHom (normalizedQ_obj (ObjectProperty.exactInclusion P) K
            (supported_ne_zero P K hK))) ≫
          eqToHom (normalizedQ_obj (quotientExact P) K.obj (underlying_ne_zero P K hK)) ≫
            ((abelianExactStructure P.isoModSerre.Localization).qIsoOfIso e).hom :=
      ((abelianExactStructure P.isoModSerre.Localization).qHom_subsingleton_of_isZero
        _ _ (isZero_zero _)).elim _ _
    rw [he, Functor.map_comp]
    simp only [Category.assoc]
    congr 1
    have h := normalizedQ_qDeflation (quotientExact P) q
      ((abelianExactStructure C).deflation_of_conflation hS) hA (underlying_ne_zero P K hK)
    rw [qDeflation_zero_target _ _ e] at h
    apply (cancel_epi (eqToHom
      (normalizedQ_obj (quotientExact P) K.obj (underlying_ne_zero P K hK)).symm)).mp
    simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp] using h

/-- The original zero contraction arm becomes the target zero cone. -/
theorem mappedZeroTriangle :
    Functor.whiskerRight (Functor.whiskerLeft AsSmall.down
        (zeroToEndomorphism (abelianExactStructure C) f q hfq hS)) (quotientNormalizedQ P) ≫
      eqToHom (normalizedEndomorphismPair_eq (quotientExact P) f q hfq hS hA) =
    eqToHom (normalizedConst_eq (quotientExact P)) ≫
      Functor.whiskerLeft (targetCore P f) (Automorphism.zeroCone
        (abelianExactStructure P.isoModSerre.Localization)) := by
  apply NatTrans.ext
  funext X
  rcases X with ⟨X⟩
  cases X <;>
    apply (cancel_epi (eqToHom (normalizedQ_zero (quotientExact P)).symm)).mp <;>
    simpa only [NatTrans.comp_app, eqToHom_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, zeroToEndomorphism, Automorphism.zeroCone,
      targetCore, imageCorePair, Automorphism.coreQ, Functor.comp_obj, AsSmall.down,
      parallelPair, parallelPairHomMk, parallelPair.parallelPairObj,
      Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using
        normalizedQ_zeroArm (quotientExact P) A hA

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary

namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
open SerreLocalization Automorphism.Diagram Automorphism.Functoriality
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] Quillen.SerreLocalization.canonicalQuotientAbelian
variable {C : Type u} [SmallCategory C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]
  (K : P.FullSubcategory) (hK : ¬ IsZero K.obj)
  {A : C} (f : A ⟶ A) (q : A ⟶ K.obj) (hfq : f ≫ q = 0)
  (hS : (abelianExactStructure C).conflation (ShortComplex.mk f q hfq))
  [IsIso ((ExactFunctor.serreLocalization P P.isoModSerre.Q).toFunctor.map f)] (hA : A ≠ 0)

/-- Restriction of the unchanged Serre epsilon to the actual supported row. -/
abbrev epsilonRow :=
  Functor.whiskerLeft (supportRow P K) (normalizedQuotientInclusionZeroIso P).hom
/-- The target full cone on the actual image core row. -/
abbrev targetFull := Functor.whiskerLeft (targetCore P f)
  (Automorphism.fullCone (abelianExactStructure P.isoModSerre.Localization))
/-- The target zero cone on the actual image core row. -/
abbrev targetZero := Functor.whiskerLeft (targetCore P f)
  (Automorphism.zeroCone (abelianExactStructure P.isoModSerre.Localization))
/-- The original quotient map on Q-spaces. -/
abbrev quotientSpaceMap := (classifyingSpaceMap (quotientNormalizedQ P)).hom
/-- The original quotient basepoint. -/
abbrev quotientBasepoint := (abelianExactStructure P.isoModSerre.Localization).kBasepoint

include hA in
/-- The mapped actual cokernel cylinder is the epsilon/full-cone composite cylinder. -/
theorem mappedCokernelHomotopy (t : unitInterval) (z : ClassifyingSpace CircleCategory) :
    quotientSpaceMap P (classifyingSpaceNaturalTransformationHomotopy
      (actualCokernelToEndomorphism P K hK f q hfq hS) (t, z)) =
    classifyingSpaceNaturalTransformationHomotopy
      (epsilonRow P K ≫ targetFull P f) (t, z) := by
  have h := realizedTransformation_congr rfl
    (normalizedEndomorphismPair_eq (quotientExact P) f q hfq hS hA)
    (Functor.whiskerRight (actualCokernelToEndomorphism P K hK f q hfq hS)
      (quotientNormalizedQ P)) (epsilonRow P K ≫ targetFull P f)
    (by simpa only [eqToHom_refl, Category.id_comp] using
      mappedCokernelTriangle P K hK f q hfq hS hA) t z
  simpa only [classifyingSpaceNaturalTransformationHomotopy_whiskerRight] using h

include hA in
/-- The mapped original zero arm is the target zero-cone cylinder. -/
theorem mappedZeroHomotopy (t : unitInterval) (z : ClassifyingSpace CircleCategory) :
    quotientSpaceMap P (classifyingSpaceNaturalTransformationHomotopy
      (Functor.whiskerLeft AsSmall.down
        (zeroToEndomorphism (abelianExactStructure C) f q hfq hS)) (t, z)) =
    classifyingSpaceNaturalTransformationHomotopy (targetZero P f) (t, z) := by
  have h := realizedTransformation_congr (normalizedConst_eq (quotientExact P))
    (normalizedEndomorphismPair_eq (quotientExact P) f q hfq hS hA)
    (Functor.whiskerRight (Functor.whiskerLeft AsSmall.down
      (zeroToEndomorphism (abelianExactStructure C) f q hfq hS)) (quotientNormalizedQ P))
    (targetZero P f) (mappedZeroTriangle P K f q hfq hS hA) t z
  simpa only [classifyingSpaceNaturalTransformationHomotopy_whiskerRight] using h

include hA in
/-- The entire projected source contraction has exactly the two original target cylinders. -/
theorem mappedAmbientContraction (t : unitInterval) (z : ClassifyingSpace CircleCategory) :
    quotientSpaceMap P (actualAmbientContraction P K hK f q hfq hS (t, z)) =
    ((classifyingSpaceNaturalTransformationHomotopy (epsilonRow P K ≫ targetFull P f)).trans
      (classifyingSpaceNaturalTransformationHomotopy (targetZero P f)).symm) (t, z) := by
  change quotientSpaceMap P (((classifyingSpaceNaturalTransformationHomotopy
    (actualCokernelToEndomorphism P K hK f q hfq hS)).trans
      (classifyingSpaceNaturalTransformationHomotopy
        (Functor.whiskerLeft AsSmall.down
          (zeroToEndomorphism (abelianExactStructure C) f q hfq hS))).symm) (t, z)) = _
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact mappedCokernelHomotopy P K hK f q hfq hS hA _ z
  · exact mappedZeroHomotopy P K f q hfq hS hA _ z

/-- The unchanged stored fiber path, preceded by the actual reversed source contraction,
regarded at the target's original basepoint using the original normalized map equality. -/
def contractedLoopMap : C(ClassifyingSpace CircleCategory,
    Path (quotientBasepoint P) (quotientBasepoint P)) where
  toFun z := (HomotopyFiber.contractedPathMap (quotientSpaceMap P) (quotientBasepoint P)
    (supportedCircleFiberMap P K) (abelianExactStructure C).kBasepoint
    (actualAmbientContraction P K hK f q hfq hS) z).cast
      (quotientExact P).normalizedQ_map_point.symm rfl
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : ClassifyingSpace CircleCategory × unitInterval =>
      HomotopyFiber.contractedPathMap (quotientSpaceMap P) (quotientBasepoint P)
        (supportedCircleFiberMap P K) (abelianExactStructure C).kBasepoint
        (actualAmbientContraction P K hK f q hfq hS) z.1 z.2)
    exact Path.continuous_uncurry_iff.mpr
      (HomotopyFiber.contractedPathMap (quotientSpaceMap P) (quotientBasepoint P)
        (supportedCircleFiberMap P K) (abelianExactStructure C).kBasepoint
        (actualAmbientContraction P K hK f q hfq hS)).continuous

include hA in
/-- The actual loop map has the literal three-cylinder form used by whole cancellation. -/
theorem contractedLoopMap_apply (z : ClassifyingSpace CircleCategory) (t : unitInterval) :
    contractedLoopMap P K hK f q hfq hS z t =
      (((classifyingSpaceNaturalTransformationHomotopy (epsilonRow P K ≫ targetFull P f)).trans
        (classifyingSpaceNaturalTransformationHomotopy (targetZero P f)).symm).symm.trans
          (classifyingSpaceNaturalTransformationHomotopy (epsilonRow P K))) (t, z) := by
  change ((((actualAmbientContraction P K hK f q hfq hS).evalAt z).symm.map
    (quotientSpaceMap P).continuous).trans
      (HomotopyFiber.toPath (quotientSpaceMap P) (quotientBasepoint P)
        (supportedCircleFiberMap P K z))) t = _
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact mappedAmbientContraction P K hK f q hfq hS hA _ z
  · change classifyingSpaceNaturalTransformationHomotopy
      (normalizedQuotientInclusionZeroIso P).hom
        (_, classifyingSpaceMap (supportRow P K) z) = _
    exact (classifyingSpaceNaturalTransformationHomotopy_whiskerLeft
      (supportRow P K) (normalizedQuotientInclusionZeroIso P).hom _ z).symm

/-- The whole core loop family of the actual image automorphism row. -/
def targetCoreLoopMap : C(ClassifyingSpace CircleCategory,
    Path (quotientBasepoint P) (quotientBasepoint P)) :=
  (Automorphism.coreLoopMap (abelianExactStructure P.isoModSerre.Localization)).comp
    (classifyingSpaceMap (targetCore P f)).hom

/-- The two target cylinders are exactly the original core-loop map. -/
theorem targetCoreLoopMap_apply (z : ClassifyingSpace CircleCategory) (t : unitInterval) :
    targetCoreLoopMap P f z t =
      ((classifyingSpaceNaturalTransformationHomotopy (targetZero P f)).trans
        (classifyingSpaceNaturalTransformationHomotopy (targetFull P f)).symm) (t, z) := by
  change ((Automorphism.conePath _ (Automorphism.zeroCone _) _).trans
    (Automorphism.conePath _ (Automorphism.fullCone _) _).symm) t = _
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact (classifyingSpaceNaturalTransformationHomotopy_whiskerLeft
      (targetCore P f) (Automorphism.zeroCone _) _ z).symm
  · exact (classifyingSpaceNaturalTransformationHomotopy_whiskerLeft
      (targetCore P f) (Automorphism.fullCone _) _ z).symm

/-- The original epsilon cancellation supplies a genuine whole-source loop-family homotopy.
Its basepoint track is retained and is not asserted constant. -/
def contractedLoopHomotopy :
    (contractedLoopMap P K hK f q hfq hS).Homotopy (targetCoreLoopMap P f) := by
  let J := TheoremB.naturalTransformationLoopCancellationHomotopy
    (epsilonRow P K) (targetFull P f) (targetZero P f)
  exact {
    toFun w := {
      toFun t := J (w.1, (t, w.2))
      continuous_toFun := by fun_prop
      source' := by
        rw [TheoremB.naturalTransformationLoopCancellationHomotopy_zero]
        simp only [classifyingSpaceMap_comp, TopCat.comp_app,
          classifyingSpaceMap_const_direct]
        rfl
      target' := by
        rw [TheoremB.naturalTransformationLoopCancellationHomotopy_one]
        simp only [classifyingSpaceMap_comp, TopCat.comp_app,
          classifyingSpaceMap_const_direct]
        rfl }
    continuous_toFun := by
      apply Path.continuous_uncurry_iff.mp
      exact J.continuous.comp (by fun_prop)
    map_zero_left z := by
      ext t
      exact (J.apply_zero (t, z)).trans
        (contractedLoopMap_apply P K hK f q hfq hS hA z t).symm
    map_one_left z := by
      ext t
      exact (J.apply_one (t, z)).trans (targetCoreLoopMap_apply P f z t).symm }

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary

namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary

/-- The positive walking-pair circle traverses left and then reverses right. -/
def circleLoop : Path circleBasepoint.{u} circleBasepoint :=
  (classifyingSpacePath (AsSmall.up.map WalkingParallelPairHom.left)).trans
    (classifyingSpacePath (AsSmall.up.map WalkingParallelPairHom.right)).symm

/-- The actual class of the displayed original circle. -/
def circlePiOne : HomotopyGroup.Pi 1 (ClassifyingSpace CircleCategory.{u}) circleBasepoint :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm ⟦circleLoop⟧

/-- Realizing any displayed row sends this circle to its original two edges. -/
theorem circleLoop_map {D : Type u} [SmallCategory D] (F : CircleCategory ⥤ D) :
    ((circleLoop.map (classifyingSpaceMap F).hom.continuous).cast
      (classifyingSpaceMap_point F (AsSmall.up.obj WalkingParallelPair.zero)).symm
      (classifyingSpaceMap_point F (AsSmall.up.obj WalkingParallelPair.zero)).symm) =
    (classifyingSpacePath (F.map (AsSmall.up.map WalkingParallelPairHom.left))).trans
      (classifyingSpacePath (F.map (AsSmall.up.map WalkingParallelPairHom.right))).symm := by
  ext t
  change classifyingSpaceMap F (circleLoop t) = _
  simp only [circleLoop, Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact classifyingSpacePath_naturality F _ _
  · exact classifyingSpacePath_naturality F _ _

variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (K : C)

/-- The supported row sends the literal positive circle to the original object class. -/
theorem circlePiOne_supported :
    homotopyGroupMap (classifyingSpaceMap (supportedDiagram E (K := K))).hom
      (classifyingSpaceMap_point (supportedDiagram E (K := K))
        (AsSmall.up.obj WalkingParallelPair.zero)) circlePiOne = E.kZeroObjectClass K := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [pi1MulEquivFundamentalGroup_naturality]
  simp only [circlePiOne, FundamentalGroup.mapOfEq_apply]
  change ⟦((circleLoop.map (classifyingSpaceMap (supportedDiagram E (K := K))).hom.continuous).cast
    (classifyingSpaceMap_point (supportedDiagram E (K := K)) _).symm
    (classifyingSpaceMap_point (supportedDiagram E (K := K)) _).symm)⟧ =
      ⟦E.kZeroObjectLoop K⟧
  rw [circleLoop_map]
  rfl

/-- On the id/automorphism row, the same positive circle is the inverse automorphism edge. -/
theorem circlePiOne_core {D : Type u} [SmallCategory D] [Preadditive D] [HasFiniteBiproducts D]
    {ED : ExactStructure D} (F : ExactFunctor E ED) {A : C} (f : A ⟶ A)
    [IsIso (F.toFunctor.map f)] :
    FundamentalGroup.mapOfEq (classifyingSpaceMap (imageCorePair F f)).hom
      (classifyingSpaceMap_point (imageCorePair F f) (AsSmall.up.obj WalkingParallelPair.zero))
      (HomotopyGroup.pi1MulEquivFundamentalGroup circlePiOne) =
    (Path.Homotopic.Quotient.mk (classifyingSpacePath (C := Core D)
      (CoreHom.mk (asIso (F.toFunctor.map f)) :
        Core.mk (F.toFunctor.obj A) ⟶ Core.mk (F.toFunctor.obj A))).symm) := by
  simp only [circlePiOne, FundamentalGroup.mapOfEq_apply]
  change ⟦((circleLoop.map (classifyingSpaceMap (imageCorePair F f)).hom.continuous).cast
    (classifyingSpaceMap_point (imageCorePair F f) _).symm
    (classifyingSpaceMap_point (imageCorePair F f) _).symm)⟧ = _
  rw [circleLoop_map]
  change (Path.Homotopic.Quotient.mk
    ((classifyingSpacePath (𝟙 (Core.mk (F.toFunctor.obj A)))).trans
      (classifyingSpacePath (C := Core D) (CoreHom.mk (asIso (F.toFunctor.map f)))).symm)) = _
  rw [classifyingSpacePath_id]
  change (𝟙 (FundamentalGroupoid.mk (classifyingSpacePoint (Core.mk (F.toFunctor.obj A))))) ≫
    (Path.Homotopic.Quotient.mk (classifyingSpacePath (C := Core D)
      (CoreHom.mk (asIso (F.toFunctor.map f)))).symm) = _
  exact Category.id_comp _

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary

namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
section Topology
variable {X : Type u} [TopologicalSpace X] {x : X}
  {Z : Type v} [TopologicalSpace Z] {W : Type w} [TopologicalSpace W]

/-- Normalize both members of a genuine whole loop-family homotopy at the moving base loop. -/
def leftMapHomotopy {f g : C(Z, Path x x)} (H : f.Homotopy g) (z : Z) :
    (IdentityTrack.leftMap f z).Homotopy (IdentityTrack.leftMap g z) where
  toFun a := (H (a.1, z)).symm.trans (H a)
  continuous_toFun := Path.continuous_trans.comp
    ((Path.continuous_symm.comp (H.continuous.comp (continuous_fst.prodMk continuous_const))).prodMk
      H.continuous)
  map_zero_left w := by simp only [H.apply_zero]; rfl
  map_one_left w := by simp only [H.apply_one]; rfl

/-- Original left corrections give identical classes under that whole homotopy. -/
theorem leftClass_homotopy {f g : C(Z, Path x x)} (H : f.Homotopy g) (z : Z)
    (a : HomotopyGroup.Pi 1 Z z) : IdentityTrack.leftClass f z a = IdentityTrack.leftClass g z a :=
  congrArg (loopShiftMulEquiv 0).symm
    (DFunLike.congr_fun (piOne_homotopy_corrected (leftMapHomotopy H z)
      (IdentityTrack.leftCap f z) (IdentityTrack.leftCap g z)
      (Automorphism.loopComponent_piOne_mul_comm (Path.refl x))) a)

/-- The original right-normalized class is functorial under based precomposition. -/
theorem rightClass_precomp (f : C(W, Path x x)) (g : C(Z, W)) (z : Z) (w : W)
    (hg : g z = w) (a : HomotopyGroup.Pi 1 Z z) :
    IdentityTrack.rightClass (f.comp g) z a =
      IdentityTrack.rightClass f w (homotopyGroupMap g hg a) := by
  subst w
  change (loopShiftMulEquiv 0).symm
    (pathTransport (IdentityTrack.rightCap f (g z)) 1
      (homotopyGroupMap ((IdentityTrack.rightMap f (g z)).comp g) rfl a)) = _
  rw [homotopyGroupMap_comp g rfl (IdentityTrack.rightMap f (g z)) rfl]
  rfl

/-- The original right correction cap computes exactly the original component class. -/
theorem rightClass_eq_component (f : C(Z, Path x x)) (z : Z)
    (a : HomotopyGroup.Pi 1 Z z) :
    IdentityTrack.rightClass f z a = Automorphism.loopComponentToPiTwo (f z)
      (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a)) := by
  have h := piOne_homotopy_corrected
    (ContinuousMap.Homotopy.refl (IdentityTrack.rightMap f z))
    (IdentityTrack.rightCap f z) (Automorphism.rightNormalizationPath f z)
    (Automorphism.loopComponent_piOne_mul_comm (Path.refl x))
  exact (congrArg (loopShiftMulEquiv 0).symm (DFunLike.congr_fun h a)).trans
    (Automorphism.rightNormalization_formula f z a)
end Topology

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}
  (F : ExactFunctor EC ED) {A : C} (f : A ⟶ A) [IsIso (F.toFunctor.map f)]

/-- The actual image core row, with its original left cap, represents the positive cube.
The sign comes from the inverse second edge of the displayed walking-pair generator. -/
theorem imageCoreLoop_class :
    IdentityTrack.leftClass
      ((Automorphism.coreLoopMap ED).comp (classifyingSpaceMap (imageCorePair F f)).hom)
      circleBasepoint circlePiOne =
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube ED (F.toFunctor.obj A)
        (asIso (F.toFunctor.map f))) : ED.K 1) := by
  rw [← IdentityTrack.rightClass_eq_leftClass (qSpace_piTwo_pathTransport_loop ED)]
  rw [rightClass_precomp (Automorphism.coreLoopMap ED)
    (classifyingSpaceMap (imageCorePair F f)).hom circleBasepoint
    (classifyingSpacePoint (Core.mk (F.toFunctor.obj A)))
    (classifyingSpaceMap_point (imageCorePair F f) (AsSmall.up.obj WalkingParallelPair.zero))]
  rw [rightClass_eq_component, pi1MulEquivFundamentalGroup_naturality]
  refine (congrArg (fun b : FundamentalGroup (ClassifyingSpace (Core D))
      (classifyingSpacePoint (Core.mk (F.toFunctor.obj A))) =>
    Automorphism.loopComponentToPiTwo
      (Automorphism.coreLoopMap ED (classifyingSpacePoint (Core.mk (F.toFunctor.obj A))))
      (FundamentalGroup.map (Automorphism.coreLoopMap ED)
        (classifyingSpacePoint (Core.mk (F.toFunctor.obj A))) b))
      (circlePiOne_core EC F f)).trans ?_
  let b : FundamentalGroup (ClassifyingSpace (Core D))
      (classifyingSpacePoint (Core.mk (F.toFunctor.obj A))) :=
    ⟦classifyingSpacePath (C := Core D) (CoreHom.mk (asIso (F.toFunctor.map f)))⟧
  change Automorphism.loopComponentToPiTwo
    (Automorphism.coreLoopMap ED (classifyingSpacePoint (Core.mk (F.toFunctor.obj A))))
      (FundamentalGroup.map (Automorphism.coreLoopMap ED)
        (classifyingSpacePoint (Core.mk (F.toFunctor.obj A))) b⁻¹) = _
  rw [map_inv, map_inv, Automorphism.Cube.automorphismFirstCube_class]
  rfl

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary

namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
open SerreLocalization Automorphism.Diagram
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] Quillen.SerreLocalization.canonicalQuotientAbelian
variable {C : Type u} [SmallCategory C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The original Serre comparison proves commutativity of its actual fiber fundamental group. -/
theorem serreFiber_piOne_comm
    (a b : HomotopyGroup.Pi 1 (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P)) :
    a * b = b * a := by
  let E := ObjectProperty.subcategoryExactStructure P
  let k := (localizationFiberComparisonHom P 0).comp E.grothendieckToKZero
  have hk : Function.Surjective k :=
    (localizationFiberComparisonHom_bijective P 0).surjective.comp
      E.grothendieckToKZero_surjective
  obtain ⟨a, rfl⟩ := hk a
  obtain ⟨b, rfl⟩ := hk b
  exact (k.map_mul a b).symm.trans ((congrArg k (mul_comm a b)).trans (k.map_mul b a))

variable (K : P.FullSubcategory) (hK : ¬ IsZero K.obj)
  {A : C} (f : A ⟶ A) (q : A ⟶ K.obj) (hfq : f ≫ q = 0)
  (hS : (abelianExactStructure C).conflation (ShortComplex.mk f q hfq))
  [IsIso ((ExactFunctor.serreLocalization P P.isoModSerre.Q).toFunctor.map f)] (hA : A ≠ 0)

include hK hA q hfq hS in
/-- The exact sign is positive: the original degree-zero boundary of the original
positive cube is the original supported cokernel object class. -/
theorem formalBoundary_positive_of_nonzero :
    SerreLocalization.connectingHom P 0
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (abelianExactStructure P.isoModSerre.Localization) ((quotientExact P).toFunctor.obj A)
        (asIso ((quotientExact P).toFunctor.map f)))) =
      (ObjectProperty.subcategoryExactStructure P).kZeroObjectClass K := by
  let a := contractedLoopMap P K hK f q hfq hS
  let d := HomotopyFiber.contractedDifference (quotientSpaceMap P) (quotientBasepoint P)
    (supportedCircleFiberMap P K) (abelianExactStructure C).kBasepoint
    (actualAmbientContraction P K hK f q hfq hS) circleBasepoint
  let γ : Path (d circleBasepoint) (Path.refl (quotientBasepoint P)) :=
    IdentityTrack.leftCap a circleBasepoint
  have hc : (loopShiftMulEquiv 0).symm
      (pathTransport γ 1 (homotopyGroupMap d rfl circlePiOne)) =
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (abelianExactStructure P.isoModSerre.Localization) ((quotientExact P).toFunctor.obj A)
        (asIso ((quotientExact P).toFunctor.map f))) :
          (abelianExactStructure P.isoModSerre.Localization).K 1) := by
    change IdentityTrack.leftClass a circleBasepoint circlePiOne = _
    exact (leftClass_homotopy (contractedLoopHomotopy P K hK f q hfq hS hA)
      circleBasepoint circlePiOne).trans (imageCoreLoop_class (quotientExact P) f)
  have hb := HomotopyFiber.connecting_contractedDifference (quotientSpaceMap P)
    (quotientBasepoint P) (supportedCircleFiberMap P K) (abelianExactStructure C).kBasepoint
    (actualAmbientContraction P K hK f q hfq hS) circleBasepoint
    (abelianExactStructure C).kBasepoint (quotientExact P).normalizedQ_map_point
    (supportedCircle_basepoint P K) γ (serreFiber_piOne_comm P) circlePiOne
  change fiberConnectingHom P 0
    ((loopShiftMulEquiv 0).symm (pathTransport γ 1 (homotopyGroupMap d rfl circlePiOne))) =
      homotopyGroupMap (supportedCircleFiberMap P K) (supportedCircle_basepoint P K)
        circlePiOne at hb
  have hb' := (congrArg (fiberConnectingHom P 0) hc).symm.trans hb
  apply (localizationFiberComparisonHom_bijective P 0).injective
  change ((localizationFiberComparisonHom P 0).comp (SerreLocalization.connectingHom P 0)) _ = _
  rw [comparison_comp_connectingHom]
  refine hb'.trans ?_
  change homotopyGroupMap ((basedLocalizationFiberComparison P).comp
      (classifyingSpaceMap (supportedDiagram (ObjectProperty.subcategoryExactStructure P)
        (K := K))).hom) _ circlePiOne = _
  rw [homotopyGroupMap_comp _
    (classifyingSpaceMap_point (supportedDiagram (ObjectProperty.subcategoryExactStructure P)
      (K := K)) (AsSmall.up.obj WalkingParallelPair.zero))
      (basedLocalizationFiberComparison P) (basedLocalizationFiberComparison_basepoint P)]
  rw [circlePiOne_supported]
  rfl

include hK q hfq hS in
/-- A nonzero cokernel in this original short exact sequence forces a nonzero source. -/
theorem source_ne_zero : A ≠ 0 := by
  have hs : (ShortComplex.mk f q hfq).ShortExact := hS
  have : Epi q := hs.epi_g
  intro h
  subst A
  apply hK
  apply (IsZero.iff_id_eq_zero _).2
  apply (cancel_epi q).mp
  simp only [Category.comp_id, comp_zero]
  exact (isZero_zero C).eq_of_src _ _

include q hfq hS in
/-- The original formal boundary formula also includes a zero cokernel: there the
original automorphism is already defined before localization and its boundary is trivial. -/
theorem formalBoundary_positive :
    SerreLocalization.connectingHom P 0
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (abelianExactStructure P.isoModSerre.Localization) ((quotientExact P).toFunctor.obj A)
        (asIso ((quotientExact P).toFunctor.map f)))) =
      (ObjectProperty.subcategoryExactStructure P).kZeroObjectClass K := by
  by_cases h₀ : IsZero K.obj
  · have hs : (ShortComplex.mk f q hfq).ShortExact := hS
    have : IsIso f := hs.isIso_f_iff.mpr h₀
    have hz : IsZero K := by
      apply (IsZero.iff_id_eq_zero _).2
      apply P.ι.map_injective
      change (𝟙 K.obj) = 0
      exact h₀.eq_of_src _ _
    have hc := Automorphism.Cube.transposedCube_KMap (quotientExact P) A (asIso f)
    have hi : (quotientExact P).toFunctor.mapIso (asIso f) =
        asIso ((quotientExact P).toFunctor.map f) := by ext; rfl
    rw [hi] at hc
    have hk : Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (abelianExactStructure P.isoModSerre.Localization) ((quotientExact P).toFunctor.obj A)
        (asIso ((quotientExact P).toFunctor.map f))) ∈
        (SerreLocalization.connectingHom P 0).ker := by
      rw [← quotient_range_eq_connecting_ker]
      exact ⟨_, hc⟩
    change SerreLocalization.connectingHom P 0 _ = 1 at hk
    exact hk.trans ((ObjectProperty.subcategoryExactStructure P).kZeroObjectClass_iso
      (hz.iso (isZero_zero _)) |>.trans
        (ObjectProperty.subcategoryExactStructure P).kZeroObjectClass_zero).symm
  · exact formalBoundary_positive_of_nonzero P K h₀ f q hfq hS
      (source_ne_zero P K h₀ f q hfq hS)

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary

namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
open SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] Quillen.SerreLocalization.canonicalQuotientAbelian
variable {C D : Type u} [SmallCategory C] [SmallCategory D] [Abelian C] [Abelian D]
  (P : ObjectProperty C) [P.IsSerreClass]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]
  {A : C} (f : A ⟶ A) [IsIso (L.map f)]

omit [Abelian D] [L.Additive] in
include L in
/-- The constructed faithful quotient lift reflects invertibility of this actual image. -/
theorem quotient_image_isIso : IsIso ((quotientExact P).toFunctor.map f) := by
  have : IsIso ((targetLift P L).map (P.isoModSerre.Q.map f)) := by
    change IsIso ((P.isoModSerre.Q ⋙ targetLift P L).map f)
    exact (congrArg (fun T : C ⥤ D => IsIso (T.map f)) (targetLift_fac P L)).mpr
      (inferInstance : IsIso (L.map f))
  exact isIso_of_reflects_iso (P.isoModSerre.Q.map f) (targetLift P L)

omit [Abelian C] in
/-- Equality of the original underlying functors preserves the literal cube class. -/
theorem positiveCube_of_functor_eq {F G : C ⥤ D} (h : F = G)
    [IsIso (F.map f)] [IsIso (G.map f)] :
    (Quotient.mk' (Automorphism.Cube.automorphismFirstCube (abelianExactStructure D)
      (F.obj A) (asIso (F.map f))) : (abelianExactStructure D).K 1) =
    Quotient.mk' (Automorphism.Cube.automorphismFirstCube (abelianExactStructure D)
      (G.obj A) (asIso (G.map f))) := by
  subst G
  rfl

/-- The exact quotient lift sends the original positive cube to its actual-target cube. -/
theorem targetLift_positiveCube
    [IsIso ((quotientExact P).toFunctor.map f)] :
    (targetLiftExactFunctor P L).KMap 1
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (abelianExactStructure P.isoModSerre.Localization) ((quotientExact P).toFunctor.obj A)
        (asIso ((quotientExact P).toFunctor.map f)))) =
    Quotient.mk' (Automorphism.Cube.automorphismFirstCube (abelianExactStructure D)
      (L.obj A) (asIso (L.map f))) := by
  rw [Automorphism.Cube.transposedCube_KMap]
  have hq : IsIso (P.isoModSerre.Q.map f) := inferInstanceAs
    (IsIso ((quotientExact P).toFunctor.map f))
  let := hq
  have : IsIso ((P.isoModSerre.Q ⋙ targetLift P L).map f) := by
    change IsIso ((targetLift P L).map (P.isoModSerre.Q.map f))
    infer_instance
  have hi : (targetLiftExactFunctor P L).toFunctor.mapIso
      (asIso ((quotientExact P).toFunctor.map f)) =
        asIso ((P.isoModSerre.Q ⋙ targetLift P L).map f) := by ext; rfl
  rw [hi]
  exact positiveCube_of_functor_eq f (targetLift_fac P L)

/-- Actual Serre localization sends the original positive automorphism cube of a
self-conflation to the original supported cokernel object class, with positive sign. -/
theorem actualBoundary_positive (K : P.FullSubcategory) (q : A ⟶ K.obj)
    (hfq : f ≫ q = 0)
    (hS : (abelianExactStructure C).conflation (ShortComplex.mk f q hfq)) :
    actualConnectingHom P L 0
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube (abelianExactStructure D)
        (L.obj A) (asIso (L.map f)))) =
      (ObjectProperty.subcategoryExactStructure P).kZeroObjectClass K := by
  let := quotient_image_isIso P L f
  have h := DFunLike.congr_fun (actualConnectingHom_comp_targetLiftKMap P L 0)
    (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
      (abelianExactStructure P.isoModSerre.Localization) ((quotientExact P).toFunctor.obj A)
      (asIso ((quotientExact P).toFunctor.map f))))
  change actualConnectingHom P L 0 ((targetLiftExactFunctor P L).KMap 1 _) =
    SerreLocalization.connectingHom P 0 _ at h
  have h' := (congrArg (actualConnectingHom P L 0) (targetLift_positiveCube P L f)).symm.trans h
  exact h'.trans (formalBoundary_positive P K f q hfq hS)

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary

namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
open FiniteModuleLocalization FGModuleCat.PrincipalRankOne
attribute [local instance] Abelian.hasFiniteBiproducts
variable (R : Type u) [CommRing R] [IsNoetherianRing R] (r : R)

/-- The literal Fin 1 free module in the original chosen small model. -/
public abbrev smallRankOne : SmallModel.{u} (FGModuleCat.{u} R) :=
  (equivSmallModel (FGModuleCat.{u} R)).functor.obj (rankOne R)

/-- The original scalar multiplication, through that same small-model equivalence. -/
def smallMultiply : smallRankOne R ⟶ smallRankOne R :=
  (equivSmallModel (FGModuleCat.{u} R)).functor.map (multiply R r)

/-- The original closed-to-supported functor applied to the original quotient rank-one module. -/
def smallQuotientTarget : (smallTorsion (Submonoid.powers r)).FullSubcategory :=
  (smallClosedToSupport r).obj (smallRankOne (ClosedRing r))

/-- The canonical unit of the quotient-ring model supplies the exact quotient endpoint. -/
def smallQuotientIso :
    (equivSmallModel (FGModuleCat.{u} R)).functor.obj (quotientObject R r) ≅
      (smallQuotientTarget R r).obj :=
  (equivSmallModel (FGModuleCat.{u} R)).functor.mapIso
    ((closedRestriction r).mapIso
      ((equivSmallModel (FGModuleCat.{u} (ClosedRing r))).unitIso.app (rankOne (ClosedRing r))))

/-- The original quotient arrow followed by its actual model unit comparison. -/
def smallQuotientMap : smallRankOne R ⟶ (smallQuotientTarget R r).obj :=
  (equivSmallModel (FGModuleCat.{u} R)).functor.map (quotientMap R r) ≫
    (smallQuotientIso R r).hom

/-- The literal multiplication-to-quotient composite remains zero. -/
theorem smallMultiply_quotient : smallMultiply R r ≫ smallQuotientMap R r = 0 := by
  dsimp only [smallMultiply, smallQuotientMap]
  rw [← Category.assoc, ← Functor.map_comp, multiply_quotientMap, Functor.map_zero, zero_comp]

/-- The exact self-complex with its original canonical closed-support endpoint. -/
def smallRankOneComplex : ShortComplex (SmallModel.{u} (FGModuleCat.{u} R)) :=
  ShortComplex.mk (smallMultiply R r) (smallQuotientMap R r) (smallMultiply_quotient R r)

/-- The actual small-model equivalence and quotient unit carry the original regular
multiplication conflation to this precise supported endpoint. -/
theorem smallRankOneConflation (hr : r ∈ nonZeroDivisors R) :
    (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} R))).conflation
      (smallRankOneComplex R r) := by
  let M := (shortComplex R r).map (equivSmallModel (FGModuleCat.{u} R)).functor
  let e : M ≅ smallRankOneComplex R r :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (smallQuotientIso R r)
      (by change 𝟙 _ ≫ smallMultiply R r = smallMultiply R r ≫ 𝟙 _; simp)
      (by change 𝟙 _ ≫ smallQuotientMap R r = smallQuotientMap R r; simp)
  exact ShortComplex.shortExact_of_iso e
    ((shortExact R r hr).map_of_exact (equivSmallModel (FGModuleCat.{u} R)).functor)

/-- The actual localized rank-one scalar automorphism in the same target small model. -/
@[expose] public def smallLocalizationAut : Aut (smallRankOne (Localization.Away r)) :=
  (equivSmallModel (FGModuleCat.{u} (Localization.Away r))).functor.mapIso (localizationAut R r)

/-- The original localization comparison and ordinary rank-one coordinate isomorphism. -/
def smallLocalizationIso :
    (smallFunctor (Submonoid.powers r)).obj (smallRankOne R) ≅
      smallRankOne (Localization.Away r) :=
  (smallFunctorComparison (Submonoid.powers r)).app (rankOne R) ≪≫
    (equivSmallModel (FGModuleCat.{u} (Localization.Away r))).functor.mapIso (localizationIso R r)

/-- The full ordinary square intertwines the mapped multiplication and the original
localized scalar automorphism, retaining both canonical small-model comparisons. -/
theorem smallLocalization_multiply :
    (smallFunctor (Submonoid.powers r)).map (smallMultiply R r) ≫
      (smallLocalizationIso R r).hom =
    (smallLocalizationIso R r).hom ≫ (smallLocalizationAut R r).hom := by
  change (smallFunctor (Submonoid.powers r)).map
      ((equivSmallModel (FGModuleCat.{u} R)).functor.map (multiply R r)) ≫
    ((smallFunctorComparison (Submonoid.powers r)).hom.app (rankOne R) ≫
      (equivSmallModel (FGModuleCat.{u} (Localization.Away r))).functor.map
        (localizationIso R r).hom) = _
  rw [← Category.assoc]
  erw [(smallFunctorComparison (Submonoid.powers r)).hom.naturality]
  change ((smallFunctorComparison (Submonoid.powers r)).hom.app (rankOne R) ≫
      (equivSmallModel (FGModuleCat.{u} (Localization.Away r))).functor.map
        ((ModuleCat.FiniteLocalization.functor (Submonoid.powers r)).map (multiply R r))) ≫
    (equivSmallModel (FGModuleCat.{u} (Localization.Away r))).functor.map
      (localizationIso R r).hom = _
  rw [Category.assoc, ← Functor.map_comp, localization_multiply_aut, Functor.map_comp]
  exact (Category.assoc _ _ _).symm

/-- Actual multiplication is invertible after the original small-model localization. -/
instance smallLocalization_multiply_isIso :
    IsIso ((smallFunctor (Submonoid.powers r)).map (smallMultiply R r)) := by
  have h : (smallFunctor (Submonoid.powers r)).map (smallMultiply R r) =
      (smallLocalizationIso R r).hom ≫ (smallLocalizationAut R r).hom ≫
        (smallLocalizationIso R r).inv := by
    apply (cancel_mono (smallLocalizationIso R r).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      smallLocalization_multiply R r
  rw [h]
  infer_instance

/-- The same ordinary square gives the precise conjugation of the actual image automorphism. -/
theorem smallLocalization_conjugate :
    Aut.autMulEquivOfIso (smallLocalizationIso R r)
      (asIso ((smallFunctor (Submonoid.powers r)).map (smallMultiply R r))) =
        smallLocalizationAut R r := by
  apply Iso.ext
  change (smallLocalizationIso R r).inv ≫
    ((smallFunctor (Submonoid.powers r)).map (smallMultiply R r) ≫
      (smallLocalizationIso R r).hom) = (smallLocalizationAut R r).hom
  rw [smallLocalization_multiply, Iso.inv_hom_id_assoc]

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary

namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
open FiniteModuleLocalization FGModuleCat.PrincipalRankOne
attribute [local instance] Abelian.hasFiniteBiproducts
variable (R : Type u) [CommRing R] [IsNoetherianRing R] (r : R)

/-- The original exact identity comparison carries the literal cube to the
same object and automorphism in the standard abelian small exact structure. -/
theorem smallAbelian_positiveCube (M : SmallModel.{u} (FGModuleCat.{u} R)) (g : Aut M) :
    smallAbelianKEquiv R 1
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} R).smallModel M g)) =
    Quotient.mk' (Automorphism.Cube.automorphismFirstCube
      (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} R))) M g) := by
  exact Automorphism.Cube.transposedCube_KMap (smallModelToAbelian R) M g

/-- The actual original localization boundary is the original canonical closed-support
object class. The localized cube uses the literal Fin 1 free module and scalar automorphism. -/
theorem principalSupportedBoundary (hr : r ∈ nonZeroDivisors R) :
    FiniteModuleLocalization.connectingHom (Submonoid.powers r) 0
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} (Localization.Away r)).smallModel
        (smallRankOne (Localization.Away r)) (smallLocalizationAut R r))) =
    (ObjectProperty.subcategoryExactStructure (smallTorsion (Submonoid.powers r))).kZeroObjectClass
      (smallQuotientTarget R r) := by
  change SerreLocalization.actualConnectingHom (smallTorsion (Submonoid.powers r))
    (smallFunctor (Submonoid.powers r)) 0 (smallAbelianKEquiv (Localization.Away r) 1 _) = _
  rw [smallAbelian_positiveCube]
  have h := actualBoundary_positive (smallTorsion (Submonoid.powers r))
    (smallFunctor (Submonoid.powers r)) (smallMultiply R r) (smallQuotientTarget R r)
    (smallQuotientMap R r) (smallMultiply_quotient R r) (smallRankOneConflation R r hr)
  have hc := Automorphism.Isomorphism.automorphismFirstCube_class_conjugate
    (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} (Localization.Away r))))
    (smallLocalizationIso R r)
    (asIso ((smallFunctor (Submonoid.powers r)).map (smallMultiply R r)))
  rw [smallLocalization_conjugate] at hc
  exact (congrArg (SerreLocalization.actualConnectingHom (smallTorsion (Submonoid.powers r))
    (smallFunctor (Submonoid.powers r)) 0) hc).trans h

/-- The original closed comparison sends the quotient rank-one object class to the
literal supported endpoint of the regular multiplication conflation. -/
theorem closedRankOneClass_map :
    closedSupportGEquiv r 0
      ((ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing r)).smallModel.kZeroObjectClass
        (smallRankOne (ClosedRing r))) =
    (ObjectProperty.subcategoryExactStructure (smallTorsion (Submonoid.powers r))).kZeroObjectClass
      (smallQuotientTarget R r) := by
  have h := DFunLike.congr_fun (closedSupportGEquiv_coe r 0)
    ((ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing r)).smallModel.kZeroObjectClass
      (smallRankOne (ClosedRing r)))
  exact h.trans ((smallClosedToSupportExact r).KMap_kZeroObjectClass (smallRankOne (ClosedRing r)))

/-- The original principal closed boundary of the original positive rank-one scalar cube
is the original quotient rank-one object class, with positive sign. Units and zero cokernels
are included; no boundary calibration or product marking is a premise. -/
theorem principalClosedBoundary (hr : r ∈ nonZeroDivisors R) :
    closedConnectingHom r 0
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} (Localization.Away r)).smallModel
        (smallRankOne (Localization.Away r)) (smallLocalizationAut R r))) =
    (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing r)).smallModel.kZeroObjectClass
      (smallRankOne (ClosedRing r)) := by
  apply (closedSupportGEquiv r 0).injective
  change closedSupportGEquiv r 0 ((closedSupportGEquiv r 0).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  exact (principalSupportedBoundary R r hr).trans (closedRankOneClass_map R r).symm

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary

namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
open FiniteModuleLocalization FGModuleCat.PrincipalRankOne
attribute [local instance] Abelian.hasFiniteBiproducts
variable (R : Type u) [CommRing R] [IsNoetherianRing R] (r : R)

omit [IsNoetherianRing R] in
/-- A unit already defines the original rank-one multiplication automorphism before localization. -/
theorem multiply_isIso_of_unit (hr : IsUnit r) : IsIso (multiply R r) := by
  obtain ⟨v, rfl⟩ := hr
  let e : Aut (rankOne R) := {
    hom := multiply R (v : R)
    inv := multiply R (↑v⁻¹ : R)
    hom_inv_id := by
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext i
      change (↑v⁻¹ : R) * ((v : R) * x i) = x i
      simp only [← mul_assoc, Units.inv_mul, one_mul]
    inv_hom_id := by
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext i
      change (v : R) * ((↑v⁻¹ : R) * x i) = x i
      simp only [← mul_assoc, Units.mul_inv, one_mul] }
  exact e.isIso_hom

/-- The original quotient rank-one object class is neutral when the principal element is a unit. -/
theorem closedRankOneClass_unit (hr : IsUnit r) :
    (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing r)).smallModel.kZeroObjectClass
      (smallRankOne (ClosedRing r)) = 1 := by
  have := multiply_isIso_of_unit R r hr
  have : IsIso (smallMultiply R r) := inferInstanceAs
    (IsIso ((equivSmallModel (FGModuleCat.{u} R)).functor.map (multiply R r)))
  have hs : (smallRankOneComplex R r).ShortExact :=
    smallRankOneConflation R r hr.mem_nonZeroDivisors
  have hz : IsZero (smallQuotientTarget R r).obj := hs.isIso_f_iff.mp this
  have hz' : IsZero (smallQuotientTarget R r) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (smallTorsion (Submonoid.powers r)).ι.map_injective
    change (𝟙 (smallQuotientTarget R r).obj) = 0
    exact hz.eq_of_src _ _
  apply (closedSupportGEquiv r 0).injective
  rw [map_one]
  let E := ObjectProperty.subcategoryExactStructure (smallTorsion (Submonoid.powers r))
  exact (closedRankOneClass_map R r).trans
    ((E.kZeroObjectClass_iso (hz'.iso (isZero_zero _))).trans E.kZeroObjectClass_zero)


/-- The original principal boundary is neutral in the unit/empty-closed-support case. -/
theorem principalClosedBoundary_unit (hr : IsUnit r) :
    closedConnectingHom r 0
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} (Localization.Away r)).smallModel
        (smallRankOne (Localization.Away r)) (smallLocalizationAut R r))) = 1 :=
  (principalClosedBoundary R r hr.mem_nonZeroDivisors).trans (closedRankOneClass_unit R r hr)

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary


namespace Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
open SerreLocalization FGModuleCat.PrincipalRankOne
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] Quillen.SerreLocalization.canonicalQuotientAbelian

/-- The original formal Serre boundary of the original positive cube is the original
supported cokernel object class. The only invertibility input concerns the actual quotient arrow. -/
public theorem serreConnectingHom_positiveCube
    {C : Type u} [SmallCategory C] [Abelian C]
    (P : ObjectProperty C) [P.IsSerreClass] {A : C} (f : A ⟶ A)
    [IsIso ((ExactFunctor.serreLocalization P P.isoModSerre.Q).toFunctor.map f)]
    (K : P.FullSubcategory) (q : A ⟶ K.obj) (hfq : f ≫ q = 0)
    (hS : (abelianExactStructure C).conflation (ShortComplex.mk f q hfq)) :
    SerreLocalization.connectingHom P 0
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (abelianExactStructure P.isoModSerre.Localization)
        ((ExactFunctor.serreLocalization P P.isoModSerre.Q).toFunctor.obj A)
        (asIso ((ExactFunctor.serreLocalization P P.isoModSerre.Q).toFunctor.map f)))) =
      (ObjectProperty.subcategoryExactStructure P).kZeroObjectClass K :=
  formalBoundary_positive P K f q hfq hS

/-- The same formula holds for the original actual-target Serre boundary, transported
through its constructed exact quotient lift rather than a new boundary map. -/
public theorem actualSerreConnectingHom_positiveCube
    {C D : Type u} [SmallCategory C] [SmallCategory D] [Abelian C] [Abelian D]
    (P : ObjectProperty C) [P.IsSerreClass]
    (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]
    {A : C} (f : A ⟶ A) [IsIso (L.map f)] (K : P.FullSubcategory)
    (q : A ⟶ K.obj) (hfq : f ≫ q = 0)
    (hS : (abelianExactStructure C).conflation (ShortComplex.mk f q hfq)) :
    SerreLocalization.actualConnectingHom P L 0
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube (abelianExactStructure D)
        (L.obj A) (asIso (L.map f)))) =
      (ObjectProperty.subcategoryExactStructure P).kZeroObjectClass K :=
  actualBoundary_positive P L f K q hfq hS

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (r : R)

/-- The original supported localization boundary of the original positive scalar cube
is the literal closed restriction of the quotient-ring rank-one object. -/
public theorem supportedConnectingHom_positiveRankOne (hr : r ∈ nonZeroDivisors R) :
    FiniteModuleLocalization.connectingHom (Submonoid.powers r) 0
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} (Localization.Away r)).smallModel
        (smallRankOne (Localization.Away r)) (smallLocalizationAut R r))) =
    (ObjectProperty.subcategoryExactStructure (smallTorsion (Submonoid.powers r))).kZeroObjectClass
      ((smallClosedToSupport r).obj (smallRankOne (ClosedRing r))) :=
  principalSupportedBoundary R r hr

/-- A regular principal element has positive original closed boundary: its localized
rank-one positive automorphism cube maps to the original quotient rank-one object class. -/
public theorem closedConnectingHom_positiveRankOne (hr : r ∈ nonZeroDivisors R) :
    closedConnectingHom r 0
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} (Localization.Away r)).smallModel
        (smallRankOne (Localization.Away r)) (smallLocalizationAut R r))) =
    (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing r)).smallModel.kZeroObjectClass
      (smallRankOne (ClosedRing r)) :=
  principalClosedBoundary R r hr

/-- The same original boundary is neutral when the principal element is a unit. -/
public theorem closedConnectingHom_positiveRankOne_of_isUnit (hr : IsUnit r) :
    closedConnectingHom r 0
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} (Localization.Away r)).smallModel
        (smallRankOne (Localization.Away r)) (smallLocalizationAut R r))) = 1 :=
  principalClosedBoundary_unit R r hr

end Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
