/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Approximation.FinitePoset.WeakCommaCone

/-! # Semantic consumers of genuine finite-poset approximation

These exercise full lower-ideal preservation, the relative old comparison,
strict latching equations, punctured-cube domains, the actual original comma
and its original classifying map, including the empty-poset base case.
-/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen.FinitePosetLatching Quillen.FinitePosetInsertion
open Quillen.Waldhausen.HasApproximationProperty
universe w u v u' v'
namespace QuillenTest.ApproximationFinitePoset

open Quillen
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] {W : Structure C} {V : Structure D}
  {F : C ⥤ D} (T : FunctorialFactorization W)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

include hF T in
/-- A single replacement has actual preserved colimits on all lower ideals
simultaneously, with a weak comparison to the original full diagram. -/
theorem finite_all_lower_ideals [Finite J] (G : J ⥤ C) :
    ∃ (R : J ⥤ C) (p : R ⟶ G), (∀ x, W.weq (p.app x)) ∧
      ∀ A : Set J, IsLowerSet A → ∃ c : Cocone (restriction R A),
        Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c)) :=
  exists_lowerPreservedReplacement F W V hF T G

/-- The entire unchanged old comparison is retained at once. -/
theorem relative_old_comparison (m : J) (hm : IsMax m) (G : J ⥤ C)
    (R : Old m ⥤ C) (p : R ⟶ restriction G (Old m))
    (c : Cocone (boundaryInclusion m ⋙ R)) (hc : IsColimit c) :
    Functor.whiskerLeft (inclusion (Old m)) (replacementStepProjection T m hm G R p c hc) =
      (replacementStepOldIso T m hm G R p c hc).hom ≫ p :=
  replacementStepProjection_restrict T m hm G R p c hc

/-- Latching cofibrancy, the actual boundary leg, and original factorization
hold together, rather than as unrelated existential choices. -/
theorem strict_latching_attachment (m : J) (hm : IsMax m) (G : J ⥤ C)
    (R : Old m ⥤ C) (p : R ⟶ restriction G (Old m))
    (c : Cocone (boundaryInclusion m ⋙ R)) (hc : IsColimit c) (x : Set.Iio m) :
    W.cof (replacementStepLatching T m hm G R p c hc) ∧
    c.ι.app x ≫ replacementStepLatching T m hm G R p c hc =
      (replacementStepOldIso T m hm G R p c hc).inv.app ((boundaryInclusion m).obj x) ≫
        (replacementStep T m hm G R p c hc).map (homOfLE x.property.le) ∧
    replacementStepLatching T m hm G R p c hc ≫
      (replacementStepProjection T m hm G R p c hc).app m =
        (replacementBoundaryArrow m G R p c hc).hom :=
  ⟨replacementStepLatching_cof T m hm G R p c hc,
    replacementStepLatching_leg T m hm G R p c hc x,
    replacementStepLatching_projection T m hm G R p c hc⟩

/-- Previously specified source objects are literally retained and every new
projection component is weak. -/
theorem old_vertices_and_weak_projection (m : J) (hm : IsMax m) (G : J ⥤ C)
    (R : Old m ⥤ C) (p : R ⟶ restriction G (Old m))
    (c : Cocone (boundaryInclusion m ⋙ R)) (hc : IsColimit c)
    (hp : ∀ x, W.weq (p.app x)) (x : Old m) (y : J) :
    (replacementStep T m hm G R p c hc).obj x.val = R.obj x ∧
      W.weq ((replacementStepProjection T m hm G R p c hc).app y) :=
  ⟨replacementStep_obj_old T m hm G R p c hc x,
    replacementStepProjection_weak T m hm G R p c hc hp y⟩

include hF in
/-- The empty domain supplies the genuine zero colimit and its actual exact
image, so the finite induction does not silently exclude its base case. -/
theorem empty_original_colimit (G : PEmpty.{w + 1} ⥤ C) :
    ∃ c : Cocone G, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c)) :=
  empty_hasPreservedColimit F W V hF G

variable (h : HasApproximationProperty W V F) [V.weq.HasTwoOutOfThreeProperty]
  (Y : WideSubcategory V.weq)

include h T in
/-- This is the original comma category, not a replacement surrogate. -/
theorem actual_finite_comma_cone [Finite J] (K : J ⥤ WeakComma hF Y) :
    ∃ L : J ⥤ WeakComma hF Y, Nonempty (L ⟶ K) ∧ Nonempty (Cocone L) :=
  exists_finitePoset_weakComma_cone h hF Y T K

include h T in
/-- Proper faces of an n-cube form a genuinely punctured domain; no missing
top vertex is supplied as an input to the coning construction. -/
theorem punctured_cube_cone (n : ℕ)
    (K : Set.Iio (Finset.univ : Finset (Fin n)) ⥤ WeakComma hF Y) :
    ∃ L : Set.Iio (Finset.univ : Finset (Fin n)) ⥤ WeakComma hF Y,
      Nonempty (L ⟶ K) ∧ Nonempty (Cocone L) :=
  exists_finitePoset_weakComma_cone h hF Y T K

section Realization
variable {C₀ D₀ J₀ : Type u} [SmallCategory C₀] [SmallCategory D₀]
  [PartialOrder J₀] [Finite J₀]
  {W₀ : Structure C₀} {V₀ : Structure D₀} {F₀ : C₀ ⥤ D₀}
  (h₀ : HasApproximationProperty W₀ V₀ F₀)
  (hF₀ : IsExact W₀.cof W₀.weq V₀.cof V₀.weq F₀)
  [V₀.weq.HasTwoOutOfThreeProperty] (T₀ : FunctorialFactorization W₀)
  (Y₀ : WideSubcategory V₀.weq) (K₀ : J₀ ⥤ WeakComma hF₀ Y₀)

include h₀ T₀ in
/-- The original diagram's original realization map is nullhomotopic. -/
theorem original_map_nullhomotopic : (classifyingSpaceMap K₀).hom.Nullhomotopic :=
  finitePoset_weakComma_classifyingMap_nullhomotopic h₀ hF₀ T₀ Y₀ K₀
end Realization
end QuillenTest.ApproximationFinitePoset
