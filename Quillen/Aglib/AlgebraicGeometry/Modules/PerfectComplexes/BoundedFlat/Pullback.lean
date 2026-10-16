/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlatPullback
public import Aglib.AlgebraicGeometry.Modules.Complex.Pullback
public import Aglib.AlgebraicGeometry.Modules.Complex.Flat.BoundedPullback

/-!
# Arbitrary pullback of bounded-flat perfect complexes

The actual geometric functor preserves local perfection, upper term bounds, stalkwise flatness and
inherited short exact sequences with flat quotient.-/
@[expose] public section



open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

variable {X : Scheme.{u}}

/-- Arbitrary geometric pullback preserves the actual bounded-flat perfect property. -/
theorem boundedFlatPerfect_pullback {Y : Scheme.{u}} (f : X ⟶ Y)
    {K : CochainComplex Y.Modules ℤ} (hK : boundedFlatPerfect Y K) :
    boundedFlatPerfect X ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj K) := by
  obtain ⟨hp, ⟨b, hb⟩, hf⟩ := hK
  refine ⟨locallyPerfect_pullback_of_boundedAbove_stalkwiseFlat f hp ⟨b, hb⟩ hf,
    ⟨b, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩,
    fun n => stalkwiseFlat_pullback f (hf n)⟩
  intro n hn
  exact (Scheme.Modules.pullback f).map_isZero (K.isZero_of_isStrictlyLE b n hn)

/-- The functor is termwise geometric pullback on original complexes and original chain maps. -/
def boundedFlatPerfectPullback {Y : Scheme.{u}} (f : X ⟶ Y) :
    BoundedFlatPerfect Y ⥤ BoundedFlatPerfect X :=
  (boundedFlatPerfect X).lift ((boundedFlatPerfect Y).ι ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.pullback f)
    (fun K => boundedFlatPerfect_pullback f K.property)

instance boundedFlatPerfectPullback_additive {Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatPerfectPullback f).Additive := by
  unfold boundedFlatPerfectPullback
  infer_instance

/-- Actual short exact sequences have flat quotient in each degree, so their pullbacks remain exact.
-/
def boundedFlatPerfectExactPullback {Y : Scheme.{u}} (f : X ⟶ Y) :
    CategoryTheory.ExactCategory.ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex Y.Modules ℤ))
        (boundedFlatPerfect Y))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
        (boundedFlatPerfect X))
        where
  toFunctor := boundedFlatPerfectPullback f
  map_conflation S hS := by
    apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
    intro n
    exact shortExact_pullback_of_stalkwiseFlat_quotient f
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hS n)
      (S.X₃.property.2.2 n)

end Quillen.PerfectComplexes

end

end
