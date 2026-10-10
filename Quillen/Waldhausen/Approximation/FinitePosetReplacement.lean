/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Approximation.FinitePosetAttachment
import Mathlib.Order.Preorder.Finite

/-!
# Actual finite-poset replacement by maximal-vertex induction

The original source factorization and exactness construct a replacement of
every finite original poset diagram, a pointwise weak natural comparison to
that diagram, and actual preserved colimits on every lower ideal. Cardinal
induction retains the whole old diagram; the genuine zero colimit handles the
empty case. Each successor uses only the actual strict-boundary colimit and
its genuine cofibrant attachment. No higher-filling endpoint is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen
open Quillen.FinitePosetLatching
universe w w' z u v u' v'

namespace Quillen.FinitePosetInsertion
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (W : Structure C) (V : Structure D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

include hF in
/-- A maximal attachment's literal boundary map, with actual colimit universal
properties, constructs the preserved colimit of the original whole diagram. -/
theorem maximalAttachment_hasPreservedColimit (G : J ⥤ C) (m : J) (hm : IsMax m)
    (hOld : HasPreservedColimit F (restriction G (Old m)))
    (c : Cocone (restriction G (Set.Iio m)))
    (hc : IsColimit c) (hFc : IsColimit (F.mapCocone c))
    (k : c.pt ⟶ G.obj m) (hk : W.cof k)
    (hleg : ∀ x : Set.Iio m, c.ι.app x ≫ k = G.map (homOfLE x.property.le)) :
    HasPreservedColimit F G := by
  obtain ⟨cA, ⟨hcA⟩, ⟨hFA⟩⟩ := hOld
  let cB := principalCocone G m
  let cI := c.whisker (maximalIntersectionIso m).equivalence.functor
  let hcI := hc.whiskerEquivalence (maximalIntersectionIso m).equivalence
  let hFI := hFc.whiskerEquivalence (maximalIntersectionIso m).equivalence
  have hj : intersectionToRight cB cI hcI = k := by
    apply hcI.hom_ext
    intro x
    rw [intersectionToRight, hcI.fac]
    exact (hleg ⟨x.val, lt_of_le_of_ne x.property.2 x.property.1⟩).symm
  have hcof : W.cof (intersectionToRight cB cI hcI) := hj ▸ hk
  exact exists_preserved_gluedColimit cA cB cI
    (maximal_lower_cover m) (complement_singleton_isLowerSet m hm) (isLowerSet_Iic m)
    F W V hF hcA (principalCoconeIsColimit G m) hcI (Or.inr hcof)
    hFA (mappedPrincipalCoconeIsColimit G F m) hFI

/-- The finite induction invariant: actual preserved colimits on all lower
ideals. No weak-equivalence or contraction endpoint is part of this invariant. -/
def HasLowerPreservedColimits (G : J ⥤ C) : Prop :=
  ∀ A : Set J, IsLowerSet A → HasPreservedColimit F (restriction G A)

variable (m : J) (A : Set J)

/-- The old portion of a lower ideal, indexed in the unchanged old poset. -/
def oldPart : Set (Old m) := {x | x.val ∈ A}

/-- Lower ideals stay lower on the old subposet. -/
theorem oldPart_isLowerSet (hA : IsLowerSet A) : IsLowerSet (oldPart m A) :=
  fun _ _ h hx ↦ hA h hx

/-- A lower ideal which omits the new vertex is entirely old. -/
def omittingOldIso (hmA : m ∉ A) : A ≃o oldPart m A where
  toFun x := ⟨⟨x.val, fun h ↦ hmA (h ▸ x.property)⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Removing the distinguished vertex inside an ideal gives its actual old
portion in the original ambient poset. -/
def containingOldIso (hmA : m ∈ A) : Old (⟨m, hmA⟩ : A) ≃o oldPart m A where
  toFun x := ⟨⟨x.val.val, fun h ↦ x.property (Subtype.ext h)⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, fun h ↦ x.val.property (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- An ideal containing the new vertex contains its entire strict boundary. -/
def containingBoundaryIso (hA : IsLowerSet A) (hmA : m ∈ A) :
    Set.Iio (⟨m, hmA⟩ : A) ≃o Set.Iio m where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hA x.property.le hmA⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Ambient maximality also holds inside any containing ideal. -/
theorem maximal_in_ideal (hm : IsMax m) (hmA : m ∈ A) : IsMax (⟨m, hmA⟩ : A) := by
  intro x hx
  exact hm hx

variable (hm : IsMax m) (R : Old m ⥤ C)
  (c : Cocone (boundaryInclusion m ⋙ R)) {M : C} (k : c.pt ⟶ M)

include hF in
/-- A single genuine cofibrant attachment simultaneously preserves the actual
colimit invariant on every lower ideal, including ideals which contain only
part of the unchanged diagram. -/
theorem insertedDiagram_hasLowerPreservedColimits
    (hc : IsColimit c) (hFc : IsColimit (F.mapCocone c))
    (hR : HasLowerPreservedColimits F R) (hk : W.cof k) :
    HasLowerPreservedColimits F (insertedDiagram m hm R (c.extend k)) := by
  intro A hA
  classical
  let H := insertedDiagram m hm R (c.extend k)
  have hOldPart := hR (oldPart m A) (oldPart_isLowerSet m A hA)
  by_cases hmA : m ∈ A
  · let mA : A := ⟨m, hmA⟩
    let eOld := (containingOldIso m A hmA).equivalence
    let oldEmb := eOld.functor ⋙ inclusion (oldPart m A)
    have hOld : HasPreservedColimit F (restriction (restriction H A) (Old mA)) :=
      (hOldPart.whisker F eOld).ofIso F
        (Functor.isoWhiskerLeft oldEmb (insertedOldDiagramIso m hm R (c.extend k)))
    let eBoundary := (containingBoundaryIso m A hA hmA).equivalence
    let cb := insertedBoundaryCocone m hm R c k
    let cbA : Cocone (restriction (restriction H A) (Set.Iio mA)) :=
      cb.whisker eBoundary.functor
    let hcb := (IsColimit.precomposeHomEquiv (insertedBoundaryIso m hm R c k) c).symm hc
    let hFcb : IsColimit (F.mapCocone cb) :=
      ((IsColimit.precomposeHomEquiv
        (Functor.isoWhiskerRight (insertedBoundaryIso m hm R c k) F)
        (F.mapCocone c)).symm hFc).ofIsoColimit F.mapCoconePrecompose.symm
    apply maximalAttachment_hasPreservedColimit F W V hF (restriction H A) mA
      (maximal_in_ideal m A hm hmA) hOld cbA
      (hcb.whiskerEquivalence eBoundary) (hFcb.whiskerEquivalence eBoundary)
      (insertedLatching m hm R c k)
      (W.cof.comp_mem _ _ hk (W.cof_iso _ inferInstance))
    intro x
    exact insertedIntersection_leg m hm R c k
      ⟨x.val.val, ne_of_lt x.property, x.property.le⟩
  · let eOld := (omittingOldIso m A hmA).equivalence
    let oldEmb := eOld.functor ⋙ inclusion (oldPart m A)
    exact (hOldPart.whisker F eOld).ofIso F
      (Functor.isoWhiskerLeft oldEmb (insertedOldDiagramIso m hm R (c.extend k)))

end Quillen.FinitePosetInsertion

namespace Quillen.FinitePosetInsertion
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (W : Structure C) (V : Structure D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- Reindex the whole poset as its literal full lower ideal. -/
def fullIdealIso : J ≃o (Set.univ : Set J) where
  toFun x := ⟨x, Set.mem_univ x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The all-lower-ideals invariant includes the actual original whole diagram. -/
theorem HasLowerPreservedColimits.whole {G : J ⥤ C}
    (h : HasLowerPreservedColimits F G) : HasPreservedColimit F G :=
  (h Set.univ isLowerSet_univ).whisker F (fullIdealIso (J := J)).equivalence

/-- The strict boundary is an actual lower ideal of the unchanged old poset. -/
theorem HasLowerPreservedColimits.boundary (m : J) {R : Old m ⥤ C}
    (h : HasLowerPreservedColimits F R) :
    HasPreservedColimit F (boundaryInclusion m ⋙ R) :=
  (h (oldPart m (Set.Iio m)) (oldPart_isLowerSet m (Set.Iio m) (isLowerSet_Iio m))).whisker
    F (omittingOldIso m (Set.Iio m) (lt_irrefl m)).equivalence

/-- The literal zero cocone on an empty diagram. -/
def emptyZeroCocone [IsEmpty J] (G : J ⥤ C) : Cocone G where
  pt := W.zero
  ι := { app x := isEmptyElim x, naturality x := isEmptyElim x }

include hF in
/-- Exactness preserves the actual empty colimit, including the empty-poset
base case of the finite induction. -/
theorem empty_hasPreservedColimit [IsEmpty J] (G : J ⥤ C) :
    HasPreservedColimit F G := by
  let c := emptyZeroCocone W G
  refine ⟨c, ⟨?_⟩, ⟨?_⟩⟩
  · exact {
      desc s := W.isZero.to_ s.pt
      fac s x := isEmptyElim x
      uniq s f hf := W.isZero.eq_of_src _ _ }
  · exact {
      desc s := (hF.zero W.isZero).to_ s.pt
      fac s x := isEmptyElim x
      uniq s f hf := (hF.zero W.isZero).eq_of_src _ _ }

include hF in
/-- Actual finite induction constructs a coherent weak replacement with
preserved colimits on every lower ideal. The original functor and original
source diagram appear literally in the comparison and universal properties. -/
theorem exists_lowerPreservedReplacement (T : FunctorialFactorization W)
    [Finite J] (G : J ⥤ C) :
    ∃ (R : J ⥤ C) (p : R ⟶ G),
      (∀ x, W.weq (p.app x)) ∧ HasLowerPreservedColimits F R := by
  classical
  suffices ∀ n : ℕ, ∀ (K : Type w) [PartialOrder K] [Finite K], Nat.card K = n →
      ∀ G : K ⥤ C, ∃ (R : K ⥤ C) (p : R ⟶ G),
        (∀ x, W.weq (p.app x)) ∧ HasLowerPreservedColimits F R by
    exact this (Nat.card J) J rfl G
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K _ _ hcard G
    cases isEmpty_or_nonempty K with
    | inl hEmpty =>
      let _ := hEmpty
      refine ⟨G, 𝟙 G, fun x ↦ isEmptyElim x, ?_⟩
      intro A hA
      exact empty_hasPreservedColimit F W V hF (restriction G A)
    | inr hNonempty =>
      let _ := hNonempty
      obtain ⟨m, hm⟩ := (Set.finite_univ : (Set.univ : Set K).Finite).exists_maximal
        (Set.univ_nonempty)
      have hm' : IsMax m := fun x hmx ↦ hm.2 (Set.mem_univ x) hmx
      have hlt : Nat.card (Old m) < n := by
        let _ := Fintype.ofFinite K
        let _ := Fintype.ofFinite (Old m)
        rw [← hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_lt (x := m) (by simp [Old])
      obtain ⟨R, p, hp, hR⟩ := ih (Nat.card (Old m)) hlt (Old m) rfl
        (restriction G (Old m))
      obtain ⟨c, ⟨hc⟩, ⟨hFc⟩⟩ := hR.boundary F m
      refine ⟨replacementStep T m hm' G R p c hc,
        replacementStepProjection T m hm' G R p c hc,
        replacementStepProjection_weak T m hm' G R p c hc hp, ?_⟩
      exact insertedDiagram_hasLowerPreservedColimits F W V hF m hm' R c
        (T.inclusion.app (replacementBoundaryArrow m G R p c hc)) hc hFc hR (T.cofibration _)

end Quillen.FinitePosetInsertion
