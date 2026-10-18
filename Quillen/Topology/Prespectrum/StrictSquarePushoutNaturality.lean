/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.StrictSquarePushout

/-!
# Naturality and original clocks of square-cone pushout interchange

Three actual square maps and their two strict span equations induce the original
pointwise pushout square map. The original total-cone interchange commutes with
this map on every quotient generator. Its inverse and all cone/overlap times
remain those of the same point-set isomorphism.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.StrictSquare.Pushout
open HomotopyPushout

/-- A strict morphism between two spans of actual strict squares. -/
structure SpanMorphism
    {S₀ S₁ S₂ T₀ T₁ T₂ : Arrow (Arrow LoopPrespectrum.{u})}
    (f : S₀ ⟶ S₁) (g : S₀ ⟶ S₂) (f' : T₀ ⟶ T₁) (g' : T₀ ⟶ T₂) where
  /-- The original common-source square map. -/
  source : S₀ ⟶ T₀
  /-- The original left-target square map. -/
  left : S₁ ⟶ T₁
  /-- The original right-target square map. -/
  right : S₂ ⟶ T₂
  left_comm : f ≫ left = source ≫ f'
  right_comm : g ≫ right = source ≫ g'

namespace SpanMorphism
variable {S₀ S₁ S₂ T₀ T₁ T₂ : Arrow (Arrow LoopPrespectrum.{u})}
    {f : S₀ ⟶ S₁} {g : S₀ ⟶ S₂} {f' : T₀ ⟶ T₁} {g' : T₀ ⟶ T₂}
    (h : SpanMorphism f g f' g')

/-- Apply any actual functor to the three span maps, then use the original quotient map. -/
def componentMap (K : Arrow (Arrow LoopPrespectrum.{u}) ⥤ LoopPrespectrum.{u}) :
    prespectrum (K.map f) (K.map g) ⟶ prespectrum (K.map f') (K.map g') :=
  map _ _ _ _ (K.map h.source) (K.map h.left) (K.map h.right)
    (by rw [← K.map_comp, ← K.map_comp, h.left_comm])
    (by rw [← K.map_comp, ← K.map_comp, h.right_comm])

/-- An actual natural transformation commutes with the original span quotient maps. -/
theorem componentMap_naturality
    {K L : Arrow (Arrow LoopPrespectrum.{u}) ⥤ LoopPrespectrum.{u}} (e : K ⟶ L) :
    map (K.map f) (K.map g) (L.map f) (L.map g)
        (e.app S₀) (e.app S₁) (e.app S₂) (e.naturality f) (e.naturality g) ≫
        h.componentMap L =
      h.componentMap K ≫ map (K.map f') (K.map g') (L.map f') (L.map g')
        (e.app T₀) (e.app T₁) (e.app T₂) (e.naturality f') (e.naturality g') := by
  apply hom_ext
  · apply Hom.ext
    funext n
    ext x
    exact congrArg (HomotopyPushout.left (L.map f') (L.map g') n)
      (congrArg (fun a => a.map n x) (e.naturality h.left).symm)
  · apply Hom.ext
    funext n
    ext x
    exact congrArg (HomotopyPushout.right (L.map f') (L.map g') n)
      (congrArg (fun a => a.map n x) (e.naturality h.right).symm)
  · intro n r x
    exact congrArg (fun y => cylinder (L.map f') (L.map g') n (r,y))
      (congrArg (fun a => a.map n x) (e.naturality h.source).symm)

/-- The actual four original component maps form a strict map of pushout squares. -/
def squareMap : square f g ⟶ square f' g' :=
  Arrow.homMk
    (Arrow.homMk (h.componentMap (Arrow.leftFunc ⋙ Arrow.leftFunc))
      (h.componentMap (Arrow.leftFunc ⋙ Arrow.rightFunc))
      (h.componentMap_naturality (Functor.whiskerLeft Arrow.leftFunc Arrow.leftToRight)).symm)
    (Arrow.homMk (h.componentMap (Arrow.rightFunc ⋙ Arrow.leftFunc))
      (h.componentMap (Arrow.rightFunc ⋙ Arrow.rightFunc))
      (h.componentMap_naturality (Functor.whiskerLeft Arrow.rightFunc Arrow.leftToRight)).symm)
    (by
      apply Arrow.hom_ext
      · exact (h.componentMap_naturality
          (Functor.whiskerRight Arrow.leftToRight Arrow.leftFunc)).symm
      · exact (h.componentMap_naturality
          (Functor.whiskerRight Arrow.leftToRight Arrow.rightFunc)).symm)

/-- Naturality of the unchanged total-cone interchange on all original quotient strata. -/
theorem totalIso_naturality :
    h.componentMap (strictSquareComparisonFunctor ⋙ mappingConeFunctor) ≫
        (totalIso f' g').hom =
      (totalIso f g).hom ≫ mappingConeMap (strictSquareComparisonFunctor.map h.squareMap) := by
  apply hom_ext
  · apply mappingCone_hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · intro n r q
      induction q using Quot.inductionOn with
      | h z => cases z with
        | inl z => cases z <;> rfl
        | inr z => rfl
  · apply mappingCone_hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · intro n r q
      induction q using Quot.inductionOn with
      | h z => cases z with
        | inl z => cases z <;> rfl
        | inr z => rfl
  · intro n s q
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => rfl
      | inr z =>
        rcases z with ⟨r,q⟩
        induction q using Quot.inductionOn with
        | h z => cases z with
          | inl z => cases z <;> rfl
          | inr z => rfl

/-- The same isomorphism gives the natural inverse square, without selecting another inverse. -/
theorem totalIso_inv_naturality :
    mappingConeMap (strictSquareComparisonFunctor.map h.squareMap) ≫ (totalIso f' g').inv =
      (totalIso f g).inv ≫ h.componentMap (strictSquareComparisonFunctor ⋙ mappingConeFunctor) := by
  apply (cancel_mono (totalIso f' g').hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    h.totalIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SpanMorphism
end Quillen.LoopPrespectrum.StrictSquare.Pushout
