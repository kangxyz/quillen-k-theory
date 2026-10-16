/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSections
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PairPullback
public import Quillen.Aglib.CategoryTheory.ObjectProperty.NestedEquivalence
public import Quillen.Aglib.CategoryTheory.ObjectProperty.LiftComposition

/-!
# Actual supported sections on the joint geometric family

The original restricted acyclicity defines supported sections. Actual evaluation is an equivalence, and every original commuting support square gives the literal reindexing functor, its geometric comparison and its identity/composition laws.
-/
@[expose] public section



open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {i k t : Index R} {U V W : Scheme.{u}}
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation

/-- Actual support tests the original evaluated complex on the specified open. -/
def boundedFlatCoefficientSectionSupported (j : U ⟶ space i) [IsOpenImmersion j] :
    ObjectProperty (BoundedFlatCoefficientSections i) := fun S ↦
  ((restrict j).obj ((boundedFlatCoefficientOriginalEvaluation i).obj S).obj).Acyclic

/-- Supported objects retain the original native cocartesian sections. -/
abbrev BoundedFlatCoefficientSupportedSections (j : U ⟶ space i) [IsOpenImmersion j] :=
  (boundedFlatCoefficientSectionSupported j).FullSubcategory

/-- Original identity evaluation retains the actual supported chain complex. -/
def boundedFlatCoefficientSupportedEvaluation (j : U ⟶ space i) [IsOpenImmersion j] :
    BoundedFlatCoefficientSupportedSections j ⥤ (boundedFlatPerfectSupported j).FullSubcategory :=
  (boundedFlatPerfectSupported j).lift
    ((boundedFlatCoefficientSectionSupported j).ι ⋙ boundedFlatCoefficientOriginalEvaluation i ⋙
      (boundedFlatPerfect (space i)).ι)
    (fun S ↦ ⟨((boundedFlatCoefficientOriginalEvaluation i).obj S.obj).property, S.property⟩)

/-- Forgetting support after evaluation keeps the original chain complex literally. -/
theorem boundedFlatCoefficientSupportedEvaluation_obj
    (j : U ⟶ space i) [IsOpenImmersion j] (S : BoundedFlatCoefficientSupportedSections j) :
    ((boundedFlatCoefficientSupportedEvaluation j).obj S).obj =
      ((boundedFlatCoefficientOriginalEvaluation i).obj S.obj).obj := rfl

/-- Support is exactly the inverse image of original geometric support under evaluation. -/
theorem boundedFlatCoefficientSupportedEvaluation_property
    (j : U ⟶ space i) [IsOpenImmersion j] :
    ((boundedFlatPerfectSupported j).inverseImage (boundedFlatPerfect (space i)).ι).inverseImage
        (boundedFlatCoefficientSectionEquivalence i).functor =
      boundedFlatCoefficientSectionSupported j := by
  funext S
  apply propext
  exact and_iff_right ((boundedFlatCoefficientOriginalEvaluation i).obj S).property

instance boundedFlatCoefficientSupportedEvaluation_isEquivalence
    (j : U ⟶ space i) [IsOpenImmersion j] :
    (boundedFlatCoefficientSupportedEvaluation j).IsEquivalence := by
  let e := Quillen.ObjectProperty.evaluationRestrictionEquivalence
    (boundedFlatPerfect (space i)) (boundedFlatPerfectSupported j) (fun _ h ↦ h.1)
    (boundedFlatCoefficientSectionEquivalence i) (boundedFlatCoefficientSectionSupported j)
    (boundedFlatCoefficientSupportedEvaluation_property j)
  have he : e.functor = boundedFlatCoefficientSupportedEvaluation j :=
    Quillen.ObjectProperty.evaluationRestrictionEquivalence_functor
      (boundedFlatPerfect (space i)) (boundedFlatPerfectSupported j) (fun _ h ↦ h.1)
      (boundedFlatCoefficientSectionEquivalence i) (boundedFlatCoefficientSectionSupported j)
      (boundedFlatCoefficientSupportedEvaluation_property j) _
  rw [← he]
  exact e.isEquivalence_functor

/-- The original supported evaluation is the literal forward functor of its genuine equivalence. -/
def boundedFlatCoefficientSupportedSectionEquivalence
    (j : U ⟶ space i) [IsOpenImmersion j] :
    BoundedFlatCoefficientSupportedSections j ≌ (boundedFlatPerfectSupported j).FullSubcategory :=
  (boundedFlatCoefficientSupportedEvaluation j).asEquivalence

/-- The forward equivalence keeps the specified original supported evaluation literally. -/
theorem boundedFlatCoefficientSupportedSectionEquivalence_functor
    (j : U ⟶ space i) [IsOpenImmersion j] :
    (boundedFlatCoefficientSupportedSectionEquivalence j).functor =
      boundedFlatCoefficientSupportedEvaluation j := rfl

section Reindex
variable (j : U ⟶ space i) (j' : V ⟶ space k) [IsOpenImmersion j] [IsOpenImmersion j']
  (f : i ⟶ k) (l : V ⟶ U) (h : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
include l h

/-- The specified original support square over the native joint map. -/
def boundedFlatCoefficientSupportSquare :
    (⟨Arrow.mk j', (show IsOpenImmersion j' from inferInstance)⟩ :
      AlgebraicGeometry.Scheme.OpenPairs) ⟶
      ⟨Arrow.mk j, (show IsOpenImmersion j from inferInstance)⟩ :=
  ObjectProperty.homMk (Arrow.homMk l (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) h)

/-- Original joint reindexing preserves actual support on the specified support square. -/
theorem boundedFlatCoefficientSectionsMap_supported
    (S : BoundedFlatCoefficientSections i) (hS : boundedFlatCoefficientSectionSupported j S) :
    boundedFlatCoefficientSectionSupported j' ((boundedFlatCoefficientSectionsMap f).obj S) := by
  have hp := boundedFlatPerfectSupported_pairPullback
    (boundedFlatCoefficientSupportSquare j j' f l h)
    (K := ((boundedFlatCoefficientOriginalEvaluation i).obj S).obj)
    ⟨((boundedFlatCoefficientOriginalEvaluation i).obj S).property, hS⟩
  intro n
  exact (hp.2 n).of_iso ((restrict j').mapIso ((boundedFlatPerfect (space k)).ι.mapIso
    ((boundedFlatCoefficientSectionReindexIso f).app S))).symm

/-- The original reindexing restricted to its actual supported objects. -/
def boundedFlatCoefficientSupportedSectionsMap :
    BoundedFlatCoefficientSupportedSections j ⥤ BoundedFlatCoefficientSupportedSections j' :=
  (boundedFlatCoefficientSectionSupported j').lift
    ((boundedFlatCoefficientSectionSupported j).ι ⋙ boundedFlatCoefficientSectionsMap f)
    (fun S ↦ boundedFlatCoefficientSectionsMap_supported j j' f l h S.obj S.property)

/-- Forgetting support keeps the original section reindexing on objects and morphisms. -/
theorem boundedFlatCoefficientSupportedSectionsMap_forget :
    boundedFlatCoefficientSupportedSectionsMap j j' f l h ⋙
        (boundedFlatCoefficientSectionSupported j').ι =
      (boundedFlatCoefficientSectionSupported j).ι ⋙ boundedFlatCoefficientSectionsMap f := rfl

omit l h in
/-- Forgetting the actual supported evaluation retains the original complex-valued functor. -/
theorem boundedFlatCoefficientSupportedEvaluation_forget :
    boundedFlatCoefficientSupportedEvaluation j ⋙ (boundedFlatPerfectSupported j).ι =
      (boundedFlatCoefficientSectionSupported j).ι ⋙ boundedFlatCoefficientOriginalEvaluation i ⋙
        (boundedFlatPerfect (space i)).ι :=
  Quillen.ObjectProperty.lift_comp_ι (boundedFlatPerfectSupported j)
    ((boundedFlatCoefficientSectionSupported j).ι ⋙ boundedFlatCoefficientOriginalEvaluation i ⋙
      (boundedFlatPerfect (space i)).ι)
    (fun S ↦ ⟨((boundedFlatCoefficientOriginalEvaluation i).obj S.obj).property, S.property⟩)

section
attribute [local irreducible] boundedFlatCoefficientSupportedSectionsMap
  boundedFlatCoefficientSupportedEvaluation

/-- The original reindexed supported evaluation keeps its specified underlying functor. -/
theorem boundedFlatCoefficientSupportedReindexEvaluation_forget :
    (boundedFlatCoefficientSupportedSectionsMap j j' f l h ⋙
        boundedFlatCoefficientSupportedEvaluation j') ⋙ (boundedFlatPerfectSupported j').ι =
      (boundedFlatCoefficientSectionSupported j).ι ⋙
        (boundedFlatCoefficientSectionsMap f ⋙ boundedFlatCoefficientOriginalEvaluation k) ⋙
          (boundedFlatPerfect (space k)).ι :=
  Quillen.ObjectProperty.comp_forget_eq
    (boundedFlatCoefficientSectionSupported j) (boundedFlatCoefficientSectionSupported j')
    (boundedFlatPerfectSupported j') (boundedFlatCoefficientSupportedSectionsMap j j' f l h)
    (boundedFlatCoefficientSupportedEvaluation j') (boundedFlatCoefficientSectionsMap f)
    (boundedFlatCoefficientOriginalEvaluation k) (boundedFlatPerfect (space k)).ι
    (boundedFlatCoefficientSupportedSectionsMap_forget j j' f l h)
    (boundedFlatCoefficientSupportedEvaluation_forget j')
end

/-- Actual geometric supported pullback keeps the original complex pullback literally. -/
theorem boundedFlatCoefficientSupportedPairPullback_forget :
    boundedFlatPerfectSupportedPullback (boundedFlatCoefficientSupportSquare j j' f l h) ⋙
        (boundedFlatPerfectSupported j').ι =
      (boundedFlatPerfectSupported j).ι ⋙
        AlgebraicGeometry.Scheme.Modules.Complex.pullback
          (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) :=
  Quillen.ObjectProperty.lift_comp_ι (boundedFlatPerfectSupported j')
    ((boundedFlatPerfectSupported j).ι ⋙
      AlgebraicGeometry.Scheme.Modules.Complex.pullback
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f))
    (fun K ↦ boundedFlatPerfectSupported_pairPullback
      (boundedFlatCoefficientSupportSquare j j' f l h) K.property)

omit l h in
/-- The actual bounded-flat pullback keeps the original complex pullback literally. -/
theorem boundedFlatCoefficientOriginalPullback_forget :
    boundedFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) ⋙
        (boundedFlatPerfect (space k)).ι =
      (boundedFlatPerfect (space i)).ι ⋙
        AlgebraicGeometry.Scheme.Modules.Complex.pullback
          (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) :=
  Quillen.ObjectProperty.lift_comp_ι (boundedFlatPerfect (space k))
    ((boundedFlatPerfect (space i)).ι ⋙
      AlgebraicGeometry.Scheme.Modules.Complex.pullback
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f))
    (fun K ↦ boundedFlatPerfect_pullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
      K.property)

section
attribute [local irreducible] boundedFlatCoefficientSupportedEvaluation
  boundedFlatPerfectSupportedPullback boundedFlatPerfectPullback

/-- The original evaluation and supported pullback retain their actual underlying composite. -/
theorem boundedFlatCoefficientSupportedEvaluationPullback_forget :
    (boundedFlatCoefficientSupportedEvaluation j ⋙
        boundedFlatPerfectSupportedPullback (boundedFlatCoefficientSupportSquare j j' f l h)) ⋙
        (boundedFlatPerfectSupported j').ι =
      (boundedFlatCoefficientSectionSupported j).ι ⋙
        (boundedFlatCoefficientOriginalEvaluation i ⋙
          boundedFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)) ⋙
          (boundedFlatPerfect (space k)).ι :=
  Quillen.ObjectProperty.comp_forget_eq_of_comparison
    (boundedFlatCoefficientSectionSupported j) (boundedFlatPerfectSupported j)
    (boundedFlatPerfectSupported j') (boundedFlatCoefficientSupportedEvaluation j)
    (boundedFlatPerfectSupportedPullback (boundedFlatCoefficientSupportSquare j j' f l h))
    (boundedFlatCoefficientOriginalEvaluation i) (boundedFlatPerfect (space i)).ι
    (AlgebraicGeometry.Scheme.Modules.Complex.pullback
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f))
    (boundedFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f))
    (boundedFlatPerfect (space k)).ι (boundedFlatCoefficientSupportedEvaluation_forget j)
    (boundedFlatCoefficientSupportedPairPullback_forget j j' f l h)
    (boundedFlatCoefficientOriginalPullback_forget f)

/-- The original transition is a supported natural isomorphism on the same complexes. -/
def boundedFlatCoefficientSupportedSectionReindexIso :
    boundedFlatCoefficientSupportedSectionsMap j j' f l h ⋙
        boundedFlatCoefficientSupportedEvaluation j' ≅
      boundedFlatCoefficientSupportedEvaluation j ⋙
        boundedFlatPerfectSupportedPullback (boundedFlatCoefficientSupportSquare j j' f l h) :=
  Quillen.ObjectProperty.isoOfForgetIso (boundedFlatPerfectSupported j')
    (boundedFlatCoefficientSupportedSectionsMap j j' f l h ⋙
      boundedFlatCoefficientSupportedEvaluation j')
    (boundedFlatCoefficientSupportedEvaluation j ⋙
      boundedFlatPerfectSupportedPullback (boundedFlatCoefficientSupportSquare j j' f l h))
    _ _ (boundedFlatCoefficientSupportedReindexEvaluation_forget j j' f l h)
    (boundedFlatCoefficientSupportedEvaluationPullback_forget j j' f l h)
    (Functor.isoWhiskerLeft (boundedFlatCoefficientSectionSupported j).ι
      (Functor.isoWhiskerRight (boundedFlatCoefficientSectionReindexIso f)
        (boundedFlatPerfect (space k)).ι))
end

end Reindex

theorem supported_lift_congr {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ D} (h : F = G)
    (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X)) : P.lift F hF = P.lift G hG := by
  subst h
  rfl

/-- Identity on the joint index is literal identity for every actual support square over it. -/
theorem boundedFlatCoefficientSupportedSectionsMap_id
    (j : U ⟶ space i) [IsOpenImmersion j] (l : U ⟶ U)
    (h : l ≫ j = j ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (𝟙 i)) :
    boundedFlatCoefficientSupportedSectionsMap j j (𝟙 i) l h =
      𝟭 (BoundedFlatCoefficientSupportedSections j) := by
  change (boundedFlatCoefficientSectionSupported j).lift
    ((boundedFlatCoefficientSectionSupported j).ι ⋙ boundedFlatCoefficientSectionsMap (𝟙 i)) _ =
      (boundedFlatCoefficientSectionSupported j).lift (boundedFlatCoefficientSectionSupported j).ι _
  apply supported_lift_congr
  exact congrArg (fun F ↦ (boundedFlatCoefficientSectionSupported j).ι ⋙ F)
    (underCocartesianReindex_id (boundedFlatCoefficientProjection R) i)

/-- Composition keeps the original reindexing; proof witnesses do not alter section maps. -/
theorem boundedFlatCoefficientSupportedSectionsMap_comp
    (j : U ⟶ space i) (j' : V ⟶ space k) (j'' : W ⟶ space t)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (f : i ⟶ k) (g : k ⟶ t) (l : V ⟶ U) (m : W ⟶ V) (n : W ⟶ U)
    (hf : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
    (hg : m ≫ j' = j'' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map g)
    (hfg : n ≫ j = j'' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (f ≫ g)) :
    boundedFlatCoefficientSupportedSectionsMap j j'' (f ≫ g) n hfg =
      boundedFlatCoefficientSupportedSectionsMap j j' f l hf ⋙
        boundedFlatCoefficientSupportedSectionsMap j' j'' g m hg := by
  change (boundedFlatCoefficientSectionSupported j'').lift
    ((boundedFlatCoefficientSectionSupported j).ι ⋙ boundedFlatCoefficientSectionsMap (f ≫ g)) _ =
      (boundedFlatCoefficientSectionSupported j'').lift
        ((boundedFlatCoefficientSectionSupported j).ι ⋙ boundedFlatCoefficientSectionsMap f ⋙
          boundedFlatCoefficientSectionsMap g) _
  apply supported_lift_congr
  exact congrArg (fun F ↦ (boundedFlatCoefficientSectionSupported j).ι ⋙ F)
    (underCocartesianReindex_comp (boundedFlatCoefficientProjection R) f g)

/-- A strict square in the original joint index remains strict after imposing actual support. -/
theorem boundedFlatCoefficientSupportedSectionsMap_square
    {k' : Index R} {V' : Scheme.{u}}
    (j : U ⟶ space i) (j' : V ⟶ space k) (j₂ : V' ⟶ space k') (j₃ : W ⟶ space t)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
    (f : i ⟶ k) (g : k ⟶ t) (f' : i ⟶ k') (g' : k' ⟶ t)
    (l : V ⟶ U) (m : W ⟶ V) (l' : V' ⟶ U) (m' : W ⟶ V')
    (hf : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
    (hg : m ≫ j' = j₃ ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map g)
    (hf' : l' ≫ j = j₂ ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f')
    (hg' : m' ≫ j₂ = j₃ ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map g')
    (h : f ≫ g = f' ≫ g') :
    boundedFlatCoefficientSupportedSectionsMap j j' f l hf ⋙
        boundedFlatCoefficientSupportedSectionsMap j' j₃ g m hg =
      boundedFlatCoefficientSupportedSectionsMap j j₂ f' l' hf' ⋙
        boundedFlatCoefficientSupportedSectionsMap j₂ j₃ g' m' hg' := by
  change (boundedFlatCoefficientSectionSupported j₃).lift
    ((boundedFlatCoefficientSectionSupported j).ι ⋙ boundedFlatCoefficientSectionsMap f ⋙
      boundedFlatCoefficientSectionsMap g) _ =
    (boundedFlatCoefficientSectionSupported j₃).lift
      ((boundedFlatCoefficientSectionSupported j).ι ⋙ boundedFlatCoefficientSectionsMap f' ⋙
        boundedFlatCoefficientSectionsMap g') _
  apply supported_lift_congr
  apply congrArg (fun F ↦ (boundedFlatCoefficientSectionSupported j).ι ⋙ F)
  exact (underCocartesianReindex_comp (boundedFlatCoefficientProjection R) f g).symm.trans
    ((congrArg (underCocartesianReindex (boundedFlatCoefficientProjection R)) h).trans
      (underCocartesianReindex_comp (boundedFlatCoefficientProjection R) f' g'))

end Quillen.PerfectComplexes

end

end
