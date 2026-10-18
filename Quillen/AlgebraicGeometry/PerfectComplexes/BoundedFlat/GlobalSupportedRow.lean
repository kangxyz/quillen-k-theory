/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionLaurentAction

/-! # The actual supported global coefficient row and its strict restriction square -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
private theorem exactIntoEquivalence
    {A B C : Type*} [Category A] [Category B] [Category C]
    (WA : Structure A) (WC : Structure C) (e : B ≌ C) (z : B)
    (hz : IsZero (e.functor.obj z)) (F : A ⥤ B)
    (h : IsExact WA.cof WA.weq WC.cof WC.weq (F ⋙ e.functor)) :
    IsExact WA.cof WA.weq (WC.ofEquivalence e z hz).cof
      (WC.ofEquivalence e z hz).weq F where
  zero hx := IsZero.of_full_of_faithful_of_isZero e.functor _ (h.zero hx)
  cofibration f hf := h.cofibration f hf
  weak f hf := h.weak f hf
  pushout hi hp := IsPushout.of_map_of_faithful e.functor (h.pushout hi hp)

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The original support predicate on the actual global coefficient row. -/
abbrev rowSupported (a : Under R) : ObjectProperty ((globalRow Q).obj a) :=
  supported (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
    (schemeMap f a)

/-- Global reindexing preserves actual support through its strict evaluation square. -/
theorem rowMap_supported {a b : Under R} (g : a ⟶ b) (S : (globalRow Q).obj a)
    (hS : rowSupported f a S) : rowSupported f b (((globalRow Q).map g).functor.obj S) := by
  have hp := boundedFlatCoefficientSectionsMap_supported
    (schemeMap f a) (schemeMap f b) (𝟙 (op Q), g)
    (boundedFlatCoefficientOpenPairMap f g).hom.left
    (Arrow.w (boundedFlatCoefficientOpenPairMap f g).hom)
    (((rowRestriction Q).app a).functor.obj S)
    ((restriction_supported R (op Q, a) (schemeMap f a) S).mpr hS)
  have h := congrArg Model.Hom.functor ((rowRestriction Q).naturality g)
  have ho := congrArg (fun F => F.obj S) h
  apply (restriction_supported R (op Q, b) (schemeMap f b) _).mp
  exact Eq.mpr (congrArg (boundedFlatCoefficientSectionSupported (schemeMap f b)) ho) hp

/-- Supported reindexing keeps the actual original global section functor. -/
def supportedRowMapFunctor {a b : Under R} (g : a ⟶ b) :
    (rowSupported f a).FullSubcategory ⥤ (rowSupported f b).FullSubcategory :=
  (rowSupported f b).lift ((rowSupported f a).ι ⋙ ((globalRow Q).map g).functor)
    (fun S => rowMap_supported f g S.obj S.property)

/-- The full coefficient-restriction square commutes before evaluation. -/
theorem supportedRowMap_restriction {a b : Under R} (g : a ⟶ b) :
    supportedRowMapFunctor f g ⋙ supportedRestriction R (op Q, b) (schemeMap f b) =
      supportedRestriction R (op Q, a) (schemeMap f a) ⋙
        (boundedFlatCoefficientSupportedModelMap f g).functor := by
  change (boundedFlatCoefficientSectionSupported (schemeMap f b)).lift
    ((rowSupported f a).ι ⋙ ((globalRow Q).map g).functor ⋙
      ((rowRestriction Q).app b).functor) _ =
    (boundedFlatCoefficientSectionSupported (schemeMap f b)).lift
      ((rowSupported f a).ι ⋙ ((rowRestriction Q).app a).functor ⋙
        ((boundedFlatCoefficientSectionModelRow Q).map g).functor) _
  apply supported_lift_congr
  have h := congrArg Model.Hom.functor ((rowRestriction Q).naturality g)
  exact congrArg (fun F => (rowSupported f a).ι ⋙ F) h

/-- Supported reindexing is exact for the original evaluation-transported classes. -/
theorem supportedRowMap_exact {a b : Under R} (g : a ⟶ b) :
    IsExact (supportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a)).cof
      (supportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a)).weq
      (supportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, b))
      (schemeMap f b)).cof
      (supportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, b))
      (schemeMap f b)).weq (supportedRowMapFunctor f g) := by
  have he := (supportedRestriction_exact R (op Q, a) (schemeMap f a)).comp
    (boundedFlatCoefficientSupportedModelMap f g).exact
  rw [← supportedRowMap_restriction f g] at he
  have heval : IsExact (supportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a)).cof
      (supportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a)).weq
      (boundedFlatPerfectSupportedWaldhausen (schemeMap f b)).cof
      (boundedFlatPerfectSupportedWaldhausen (schemeMap f b)).weq
      (supportedRowMapFunctor f g ⋙ supportedEvaluation (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, b))
      (schemeMap f b)) := by
    have h := he.comp (boundedFlatCoefficientSupportedEvaluation_exact (schemeMap f b))
    rw [Functor.assoc, supportedRestriction_evaluation] at h
    exact h
  exact exactIntoEquivalence _ _
    (supportedEvaluation (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, b))
      (schemeMap f b)).asEquivalence _ _ _ heval

/-- The supported Model arrow keeps the original global chosen zero. -/
def supportedRowMap {a b : Under R} (g : a ⟶ b) :
    supportedModel (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a) ⟶ supportedModel (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, b))
      (schemeMap f b) where
  functor := supportedRowMapFunctor f g
  exact := supportedRowMap_exact f g
  zero := by
    apply ObjectProperty.FullSubcategory.ext
    exact ((globalRow Q).map g).zero

/-- Supported global sections form a strict coefficient Model diagram. -/
def supportedRow : Under R ⥤ Model.{u+1} where
  obj a := supportedModel (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a)
  map := supportedRowMap f
  map_id a := by
    apply Model.Hom.ext
    change (rowSupported f a).lift
      ((rowSupported f a).ι ⋙ ((globalRow Q).map (𝟙 a)).functor) _ =
        (rowSupported f a).lift (rowSupported f a).ι _
    apply supported_lift_congr
    have h := congrArg Model.Hom.functor ((globalRow Q).map_id a)
    exact congrArg (fun F => (rowSupported f a).ι ⋙ F) h
  map_comp g h := by
    apply Model.Hom.ext
    change (rowSupported f _).lift
      ((rowSupported f _).ι ⋙ ((globalRow Q).map (g ≫ h)).functor) _ =
        (rowSupported f _).lift
          ((rowSupported f _).ι ⋙ ((globalRow Q).map g).functor ⋙
            ((globalRow Q).map h).functor) _
    apply supported_lift_congr
    have hh := congrArg Model.Hom.functor ((globalRow Q).map_comp g h)
    exact congrArg (fun F => (rowSupported f _).ι ⋙ F) hh

/-- Forget support without changing the original global section. -/
def supportedRowForget : supportedRow f ⟶ globalRow Q where
  app a := supportedForget (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a)
  naturality a b g := by
    apply Model.Hom.ext
    rfl

/-- Restrict the actual supported global row to the original supported coefficient row. -/
def supportedRowRestriction : supportedRow f ⟶ boundedFlatCoefficientSupportedModelFunctor f where
  app a := supportedRestrictionModel R (op Q, a) (schemeMap f a)
  naturality a b g := by
    apply Model.Hom.ext
    exact supportedRowMap_restriction f g

/-- The actual supported forgetful comparison square is strict as a transformation. -/
theorem supportedRowRestriction_forget :
    supportedRowRestriction f ≫ boundedFlatCoefficientSupportedForgetModelTransformation f =
      supportedRowForget f ≫ rowRestriction Q := by
  ext a
  exact supportedRestrictionModel_forget R f a

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
