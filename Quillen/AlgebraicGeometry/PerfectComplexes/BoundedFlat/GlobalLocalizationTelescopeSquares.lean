/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalLocalizationTelescopeMaps

/-! # Exact original localization comparison squares at every stage and on telescopes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.LocalizationTelescope

private theorem mapSquare {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' D' : C} (a : A ⟶ B) (b : B ⟶ D') (c : A ⟶ C') (d : C' ⟶ D')
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d :=
  (F.map_comp a b).symm.trans ((congrArg F.map h).trans (F.map_comp c d))

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The actual supported comparison square commutes at every finite Bass stage. -/
theorem finiteForget_square (i : ℕ) :
    SupportedTelescope.finiteRestriction f i ≫ boundedFlatCoefficientSupportedBassForget f i =
      finiteForget f i ≫ finiteRestriction Q i := by
  have h := congrArg (fun η => Functor.whiskerRight η prespectrumFunctor)
    (supportedRowRestriction_forget f)
  simp only [Functor.whiskerRight_comp] at h
  exact mapSquare (strictDiagramIterate (laurentUnderSquareFunctor R) i) _ _ _ _ h

/-- The actual coarse comparison square commutes at every finite Bass stage. -/
theorem finiteOpen_square (i : ℕ) :
    finiteOpen f i ≫ OpenTelescope.finiteRestriction f i =
      finiteRestriction Q i ≫ boundedFlatCoefficientAmbientBassOpen f i := by
  have h := congrArg (fun η => Functor.whiskerRight η prespectrumFunctor)
    (openRowRestriction_changeWeak f)
  simp only [Functor.whiskerRight_comp] at h
  exact mapSquare (strictDiagramIterate (laurentUnderSquareFunctor R) i) _ _ _ _ h

/-- The supported comparison retains the complete actual telescope quotient maps. -/
theorem forget_square :
    SupportedTelescope.telescopeRestriction f ≫
      boundedFlatCoefficientSupportedBassTelescopeForget f =
      forget f ≫ telescopeRestriction Q := by
  apply NatTrans.ext
  funext a
  apply Telescope.hom_ext
  intro n i t x
  change Telescope.cylinder
    (fun j => (boundedFlatCoefficientAmbientBassDiagram Q j).obj a)
    (fun j => (boundedFlatCoefficientAmbientBassTransition Q j).app a) n i
      (t, ((boundedFlatCoefficientSupportedBassForget f i).app a).map n
        (((SupportedTelescope.finiteRestriction f i).app a).map n x)) =
    Telescope.cylinder
    (fun j => (boundedFlatCoefficientAmbientBassDiagram Q j).obj a)
    (fun j => (boundedFlatCoefficientAmbientBassTransition Q j).app a) n i
      (t, ((finiteRestriction Q i).app a).map n (((finiteForget f i).app a).map n x))
  exact congrArg (fun y => Telescope.cylinder
    (fun j => (boundedFlatCoefficientAmbientBassDiagram Q j).obj a)
    (fun j => (boundedFlatCoefficientAmbientBassTransition Q j).app a) n i (t, y))
      (congrArg (fun η => (η.app a).map n x) (finiteForget_square f i))

/-- The coarse comparison retains the complete actual telescope quotient maps. -/
theorem open_square :
    openMap f ≫ OpenTelescope.telescopeRestriction f =
      telescopeRestriction Q ≫ boundedFlatCoefficientAmbientBassTelescopeOpen f := by
  apply NatTrans.ext
  funext a
  apply Telescope.hom_ext
  intro n i t x
  change Telescope.cylinder
    (fun j => (boundedFlatCoefficientOpenBassDiagram f j).obj a)
    (fun j => (boundedFlatCoefficientOpenBassTransition f j).app a) n i
      (t, ((OpenTelescope.finiteRestriction f i).app a).map n
        (((finiteOpen f i).app a).map n x)) =
    Telescope.cylinder
    (fun j => (boundedFlatCoefficientOpenBassDiagram f j).obj a)
    (fun j => (boundedFlatCoefficientOpenBassTransition f j).app a) n i
      (t, ((boundedFlatCoefficientAmbientBassOpen f i).app a).map n
        (((finiteRestriction Q i).app a).map n x))
  exact congrArg (fun y => Telescope.cylinder
    (fun j => (boundedFlatCoefficientOpenBassDiagram f j).obj a)
    (fun j => (boundedFlatCoefficientOpenBassTransition f j).app a) n i (t, y))
      (congrArg (fun η => (η.app a).map n x) (finiteOpen_square f i))

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.LocalizationTelescope
