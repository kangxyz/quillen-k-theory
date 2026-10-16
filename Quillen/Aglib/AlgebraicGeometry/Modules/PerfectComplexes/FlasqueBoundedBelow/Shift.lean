/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor

/-!
# Actual shifts of lower-bounded flasque perfect complexes

The original cochain shift, including the differential sign, preserves the full object predicate and inherited exact sequences.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
open AlgebraicGeometry.Scheme.Modules.Godement
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
/-- Original shift preserves the full flasque-perfect object predicate. -/
lemma shift_objects {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
    (hK : FlasqueBoundedBelow.objects X K) (n : ℤ) :
    FlasqueBoundedBelow.objects X (K⟦n⟧) := by
  refine ⟨BoundedBelow.objects_shift hK.1 n, fun i => ?_⟩
  let : TopCat.Presheaf.IsFlasque (K.X (i + n)).presheaf := hK.2 (i + n)
  exact flasque_of_iso (K.shiftFunctorObjXIso n i (i + n) rfl).symm

/-- The literal standard original cochain shift, including its differential sign. -/
def modelShift (X : Scheme.{u}) (n : ℤ) :
    FlasqueBoundedBelow.Obj X ⥤ FlasqueBoundedBelow.Obj X :=
  ObjectProperty.lift _ ((FlasqueBoundedBelow.objects X).ι ⋙ shiftFunctor
    (CochainComplex X.Modules ℤ) n)
    (fun K => shift_objects K.property n)

instance modelShift_additive (X : Scheme.{u}) (n : ℤ) : (modelShift X n).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (shiftFunctor (CochainComplex X.Modules ℤ) n).map (f.hom + g.hom) =
      (shiftFunctor (CochainComplex X.Modules ℤ) n).map f.hom +
        (shiftFunctor (CochainComplex X.Modules ℤ) n).map g.hom
    exact CategoryTheory.Functor.map_add _

/-- Original shift preserves the inherited actual exact sequences. -/
def modelShiftExactFunctor (X : Scheme.{u}) (n : ℤ) : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (FlasqueBoundedBelow.objects X))
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (FlasqueBoundedBelow.objects X)) where
  toFunctor := modelShift X n
  map_conflation S hS := by
    change (S.map (FlasqueBoundedBelow.objects X).ι).ShortExact at hS
    change ((S.map (FlasqueBoundedBelow.objects X).ι).map
      (shiftFunctor (CochainComplex X.Modules ℤ) n)).ShortExact
    exact hS.map_of_exact _


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
end
end
