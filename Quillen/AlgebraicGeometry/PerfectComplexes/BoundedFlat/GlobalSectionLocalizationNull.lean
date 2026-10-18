/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRow
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalOpenModels

/-!
# The actual global supported localization null

The original global chosen zero maps uniquely to supported sections. Actual support makes
this map weak in the coarse-open structure. Its unchanged reversed realization agrees at every
time with the original coefficient null under the actual restriction maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Complex
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The unique map from the original global zero to the unchanged supported inclusion. -/
def globalZeroToOpen (a : Under R) :
    (Functor.const ((supportedRow f).obj a)).obj ((globalRow Q).obj a).waldhausen.zero ⟶
      ((supportedRowForget f).app a).functor where
  app S := ((globalRow Q).obj a).waldhausen.isZero.to_ S.obj
  naturality _ _ _ := ((globalRow Q).obj a).waldhausen.isZero.eq_of_src _ _

private theorem weak_of_zero_source {C : Type*} [Category* C] (W : Structure C)
    {Z X : C} (hZ : IsZero Z) (g : Z ⟶ X) (h : W.weq (W.isZero.to_ X)) : W.weq g := by
  have he : g = (hZ.iso W.isZero).hom ≫ W.isZero.to_ X := hZ.eq_of_src _ _
  rw [he]
  exact W.weq.comp_mem _ _ (W.weq_iso _ (by infer_instance)) h

/-- Original support makes this original zero-to-image map coarse weak. -/
theorem globalZeroToOpen_weak (a : Under R) (S : (supportedRow f).obj a) :
    (openModel f a).waldhausen.weq ((globalZeroToOpen f a).app S) := by
  apply (Structure.withInverseImageWeak_weq_iff
    ((openSourceTransformation f).app a).exact _).mpr
  apply weak_of_zero_source (boundedFlatCoefficientOpenModel f a).waldhausen
    (((openSourceTransformation f).app a).exact.zero
      ((globalRow Q).obj a).waldhausen.isZero)
  exact boundedFlatCoefficientSupportedZeroToOpen_weak f a
    (((supportedRowRestriction f).app a).functor.obj S)

/-- Reverse precisely the actual global weak zero-to-inclusion realization. -/
def globalSupportedOpenNull :
    DiagramNullHomotopy (Functor.whiskerRight (supportedRowForget f) prespectrumFunctor)
      (Functor.whiskerRight (openRowChangeWeak f) prespectrumFunctor) :=
  modelDiagramZeroNull (supportedRowForget f) (openRowChangeWeak f)
    (globalZeroToOpen f) (globalZeroToOpen_weak f)

/-- The two actual strict Model squares give the exact composite localization square. -/
theorem globalSupportedOpen_restriction :
    (supportedRowForget f ≫ openRowChangeWeak f) ≫ openRowRestriction f =
      supportedRowRestriction f ≫
        (boundedFlatCoefficientSupportedForgetModelTransformation f ≫
          boundedFlatCoefficientOpenChangeWeakModelTransformation f) := by
  rw [Category.assoc, openRowRestriction_changeWeak, ← Category.assoc,
    ← supportedRowRestriction_forget, Category.assoc]

/-- Restriction retains every value of the original null at the identical reversed time. -/
theorem globalSupportedOpenNull_restriction (a : Under R) (n : ℕ) (s : unitInterval)
    (x : (prespectrum ((supportedRow f).obj a)).space n) :
    (prespectrumMap ((openRowRestriction f).app a)).map n
        (((globalSupportedOpenNull f).homotopy a).level n (s, x)) =
      ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a).level n
        (s, (prespectrumMap ((supportedRowRestriction f).app a)).map n x) :=
  prespectrumCompositeZeroNullHomotopy_naturality
    ((supportedRowForget f).app a) ((openRowChangeWeak f).app a)
    (boundedFlatCoefficientSupportedForgetModelMap f a)
    (boundedFlatCoefficientOpenChangeWeakModelMap f a)
    ((supportedRowRestriction f).app a) ((openRowRestriction f).app a)
    (congrArg (fun η => η.app a) (globalSupportedOpen_restriction f))
    (globalZeroToOpen f a) (boundedFlatCoefficientSupportedZeroToOpen f a)
    (globalZeroToOpen_weak f a) (boundedFlatCoefficientSupportedZeroToOpen_weak f a) n s x

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
