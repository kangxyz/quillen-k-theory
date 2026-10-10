/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Approximation.FinitePosetInsertion

/-!
# Genuine relative maximal-vertex Reedy attachments

The given source functorial factorization factors the actual strict-boundary
colimit map to the original new vertex. The resulting diagram retains the
whole old comparison and has a genuine latching cofibration with strict leg
and projection equations. An actual Waldhausen pushout constructs its full
colimit and proves that the original exact functor preserves it.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen
open Quillen.FinitePosetLatching
universe w w' z u v u' v'

namespace Quillen.FinitePosetInsertion
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  {W : Structure C} (T : FunctorialFactorization W)
  (m : J) (hm : IsMax m) (G : J ⥤ C)
  (R : Old m ⥤ C) (p : R ⟶ FinitePosetLatching.restriction G (Old m))
  (c : Cocone (boundaryInclusion m ⋙ R)) (hc : IsColimit c)

/-- The genuine latching-to-original-vertex arrow from the previous comparison. -/
def replacementBoundaryArrow : Arrow C :=
  Arrow.mk (hc.desc (comparisonBoundaryCocone m R G p))

/-- The original factorization attaches the new vertex to the whole boundary. -/
def replacementBoundaryCocone : Cocone (boundaryInclusion m ⋙ R) :=
  c.extend (T.inclusion.app (replacementBoundaryArrow m G R p c hc))

/-- The actual new source diagram; all old data are inherited by insertion. -/
def replacementStep : J ⥤ C :=
  insertedDiagram m hm R (replacementBoundaryCocone T m G R p c hc)

/-- The weak original projection strictly respects every actual boundary leg. -/
theorem replacementBoundary_projection (x : Set.Iio m) :
    (replacementBoundaryCocone T m G R p c hc).ι.app x ≫
      T.projection.app (replacementBoundaryArrow m G R p c hc) =
        p.app ((boundaryInclusion m).obj x) ≫ G.map (homOfLE x.property.le) := by
  change (c.ι.app x ≫ T.inclusion.app (replacementBoundaryArrow m G R p c hc)) ≫
    T.projection.app (replacementBoundaryArrow m G R p c hc) = _
  rw [Category.assoc, T.factorization]
  exact hc.fac (comparisonBoundaryCocone m R G p) x

/-- The coherent weak comparison to the original whole diagram. -/
def replacementStepProjection : replacementStep T m hm G R p c hc ⟶ G :=
  insertedProjection m hm R (replacementBoundaryCocone T m G R p c hc) G p
    (T.projection.app (replacementBoundaryArrow m G R p c hc))
    (replacementBoundary_projection T m G R p c hc)

/-- The whole previously constructed old diagram is retained under canonical
object equalities, not merely its individual isomorphism classes. -/
def replacementStepOldIso :
    FinitePosetLatching.inclusion (Old m) ⋙ replacementStep T m hm G R p c hc ≅ R :=
  insertedOldDiagramIso m hm R (replacementBoundaryCocone T m G R p c hc)

/-- Restriction recovers the original specified old comparison simultaneously
on all of its vertices and arrows. -/
theorem replacementStepProjection_restrict :
    Functor.whiskerLeft (FinitePosetLatching.inclusion (Old m))
      (replacementStepProjection T m hm G R p c hc) =
        (replacementStepOldIso T m hm G R p c hc).hom ≫ p :=
  insertedProjection_restrict m hm R (replacementBoundaryCocone T m G R p c hc) G p
    (T.projection.app (replacementBoundaryArrow m G R p c hc))
    (replacementBoundary_projection T m G R p c hc)

/-- Every projection component is weak by the actual original factorization;
no saturation or higher-filling assertion is needed for this step. -/
theorem replacementStepProjection_weak (hp : ∀ x, W.weq (p.app x)) (x : J) :
    W.weq ((replacementStepProjection T m hm G R p c hc).app x) :=
  insertedProjection_weak m hm R (replacementBoundaryCocone T m G R p c hc) G p
    (T.projection.app (replacementBoundaryArrow m G R p c hc))
    (replacementBoundary_projection T m G R p c hc) W hp (T.weak _) x

/-- The actual map from the previously computed latching colimit into the new
vertex. Its target is the literal newly inserted original-diagram object. -/
def replacementStepLatching : c.pt ⟶ (replacementStep T m hm G R p c hc).obj m :=
  T.inclusion.app (replacementBoundaryArrow m G R p c hc) ≫
    (insertedNewIso m R (replacementBoundaryCocone T m G R p c hc)).inv

/-- The new latching map is a genuine source cofibration. -/
theorem replacementStepLatching_cof :
    W.cof (replacementStepLatching T m hm G R p c hc) :=
  W.cof.comp_mem _ _ (T.cofibration _) (W.cof_iso _ inferInstance)

/-- Every original boundary leg agrees strictly with the map of the inserted
diagram after the canonical unchanged-old-object identification. -/
theorem replacementStepLatching_leg (x : Set.Iio m) :
    c.ι.app x ≫ replacementStepLatching T m hm G R p c hc =
      (replacementStepOldIso T m hm G R p c hc).inv.app ((boundaryInclusion m).obj x) ≫
        (replacementStep T m hm G R p c hc).map (homOfLE x.property.le) := by
  have hx : x.val ≠ m := ne_of_lt x.property
  change c.ι.app x ≫
      (T.inclusion.app (replacementBoundaryArrow m G R p c hc) ≫
        (insertedNewIso m R (replacementBoundaryCocone T m G R p c hc)).inv) =
    (insertedOldIso m R (replacementBoundaryCocone T m G R p c hc)
      ⟨x.val, hx⟩).inv ≫
      insertedMap m hm R (replacementBoundaryCocone T m G R p c hc)
        (homOfLE x.property.le)
  simp only [insertedMap, dite_true, dite_eq_right hx,
    Iso.inv_hom_id_assoc]
  simp only [replacementBoundaryCocone, Cocone.extend, NatTrans.comp_app, Category.assoc]
  rfl

/-- The new latching projection factors exactly the original boundary descent. -/
theorem replacementStepLatching_projection :
    replacementStepLatching T m hm G R p c hc ≫
      (replacementStepProjection T m hm G R p c hc).app m =
        (replacementBoundaryArrow m G R p c hc).hom := by
  change (T.inclusion.app (replacementBoundaryArrow m G R p c hc) ≫
      (insertedNewIso m R (replacementBoundaryCocone T m G R p c hc)).inv) ≫
    insertedProjectionApp m hm R (replacementBoundaryCocone T m G R p c hc) G p
      (T.projection.app (replacementBoundaryArrow m G R p c hc)) m = _
  simp only [insertedProjectionApp, dite_true, Category.assoc, Iso.inv_hom_id_assoc]
  exact T.factorization _

/-- The old vertex objects are literally unchanged by the finite induction step. -/
theorem replacementStep_obj_old (x : Old m) :
    (replacementStep T m hm G R p c hc).obj x.val = R.obj x :=
  insertedDiagram_obj_old m hm R (replacementBoundaryCocone T m G R p c hc) x

end Quillen.FinitePosetInsertion

namespace Quillen.FinitePosetInsertion
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]
  (m : J) (hm : IsMax m) (R : Old m ⥤ C)
  (c : Cocone (boundaryInclusion m ⋙ R)) {M : C} (k : c.pt ⟶ M)

/-- The intersection in the actual maximal-vertex lower cover is precisely
its strict boundary, including its original order arrows. -/
def maximalIntersectionIso : (Old m ∩ Set.Iic m : Set J) ≃o Set.Iio m where
  toFun x := ⟨x.val, lt_of_le_of_ne x.property.2 x.property.1⟩
  invFun x := ⟨x.val, ne_of_lt x.property, x.property.le⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The old canonical identification reindexes the original entire boundary
of the inserted diagram, not just separate vertices. -/
def insertedBoundaryIso :
    restriction (insertedDiagram m hm R (c.extend k)) (Set.Iio m) ≅
      boundaryInclusion m ⋙ R :=
  Functor.isoWhiskerLeft (boundaryInclusion m)
    (insertedOldDiagramIso m hm R (c.extend k))

/-- The old boundary colimit cocone, viewed on the literal inserted diagram. -/
def insertedBoundaryCocone :
    Cocone (restriction (insertedDiagram m hm R (c.extend k)) (Set.Iio m)) :=
  (Cocone.precompose (insertedBoundaryIso m hm R c k).hom).obj c

/-- The overlap cocone in the actual two-lower-ideal cover. -/
def insertedIntersectionCocone :
    Cocone (restriction (insertedDiagram m hm R (c.extend k))
      (Old m ∩ Set.Iic m)) :=
  (insertedBoundaryCocone m hm R c k).whisker (maximalIntersectionIso m).equivalence.functor

/-- The actual latching cofibration lands in the literal new object. -/
def insertedLatching : c.pt ⟶ (insertedDiagram m hm R (c.extend k)).obj m :=
  k ≫ (insertedNewIso m R (c.extend k)).inv

/-- All overlap legs factor strictly through the actual attaching map. -/
theorem insertedIntersection_leg (x : (Old m ∩ Set.Iic m : Set J)) :
    (insertedIntersectionCocone m hm R c k).ι.app x ≫ insertedLatching m hm R c k =
      (principalCocone (insertedDiagram m hm R (c.extend k)) m).ι.app
        ⟨x.val, x.property.2⟩ := by
  have hx : x.val ≠ m := x.property.1
  change ((insertedOldIso m R (c.extend k) ⟨x.val, hx⟩).hom ≫ c.ι.app ⟨x.val, lt_of_le_of_ne x.property.2 hx⟩) ≫
    (k ≫ (insertedNewIso m R (c.extend k)).inv) =
      insertedMap m hm R (c.extend k) (homOfLE x.property.2)
  simp only [insertedMap, dite_true, dite_eq_right hx, Cocone.extend,
    NatTrans.comp_app, Functor.const_map_app, Category.assoc]

variable (F : C ⥤ D)
  (W : Structure C) (V : Structure D) (hF : IsExact W.cof W.weq V.cof V.weq F)

include hF in
/-- An actual cofibrant boundary attachment constructs a preserved colimit for
the whole inserted original diagram. No full-diagram colimit is assumed. -/
theorem insertedDiagram_hasPreservedColimit
    (hc : IsColimit c) (hFc : IsColimit (F.mapCocone c))
    (hR : HasPreservedColimit F R) (hk : W.cof k) :
    HasPreservedColimit F (insertedDiagram m hm R (c.extend k)) := by
  let H := insertedDiagram m hm R (c.extend k)
  obtain ⟨cA, ⟨hcA⟩, ⟨hFA⟩⟩ :=
    hR.ofIso F (insertedOldDiagramIso m hm R (c.extend k))
  let cB := principalCocone H m
  let cI := insertedIntersectionCocone m hm R c k
  let hcBoundary := (IsColimit.precomposeHomEquiv (insertedBoundaryIso m hm R c k) c).symm hc
  let hcI : IsColimit cI := hcBoundary.whiskerEquivalence (maximalIntersectionIso m).equivalence
  let hFBoundary := (IsColimit.precomposeHomEquiv
    (Functor.isoWhiskerRight (insertedBoundaryIso m hm R c k) F) (F.mapCocone c)).symm hFc
  let hFBoundary' : IsColimit (F.mapCocone (insertedBoundaryCocone m hm R c k)) :=
    hFBoundary.ofIsoColimit F.mapCoconePrecompose.symm
  let hFI : IsColimit (F.mapCocone cI) :=
    hFBoundary'.whiskerEquivalence (maximalIntersectionIso m).equivalence
  have hj : intersectionToRight cB cI hcI = insertedLatching m hm R c k := by
    apply hcI.hom_ext
    intro x
    rw [intersectionToRight, hcI.fac]
    exact (insertedIntersection_leg m hm R c k x).symm
  have hcof : W.cof (intersectionToRight cB cI hcI) := by
    rw [hj]
    exact W.cof.comp_mem _ _ hk (W.cof_iso _ inferInstance)
  exact exists_preserved_gluedColimit cA cB cI
    (maximal_lower_cover m) (complement_singleton_isLowerSet m hm) (isLowerSet_Iic m)
    F W V hF hcA (principalCoconeIsColimit H m) hcI (Or.inr hcof)
    hFA (mappedPrincipalCoconeIsColimit H F m) hFI

end Quillen.FinitePosetInsertion
