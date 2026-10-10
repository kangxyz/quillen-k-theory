/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedRepresentativeNaturality
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Triangulated structure on the actual quasi-isomorphism localization

All structures below are inherited from mathlib's constructed standard
localization. No alternative abstract derived category or derived-equivalence
hypothesis is supplied. Exact open restriction gives its actual triangulated
functor and localization factorization.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated

universe u

namespace Quillen.PerfectComplexes

/-- The standard quasi-isomorphism localization of complexes of sheaves of modules on `X`,
supplying the derived-category structure. -/
local instance standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

instance instPreadditiveDerived (X : Scheme.{u}) : Preadditive (Derived X) :=
  inferInstanceAs (Preadditive (DerivedCategory X.Modules))

instance derived_hasZeroObject (X : Scheme.{u}) : HasZeroObject (Derived X) :=
  inferInstanceAs (HasZeroObject (DerivedCategory X.Modules))

instance instHasShiftDerived (X : Scheme.{u}) : HasShift (Derived X) ℤ :=
  inferInstanceAs (HasShift (DerivedCategory X.Modules) ℤ)

instance derived_shift_additive (X : Scheme.{u}) (n : ℤ) :
    (shiftFunctor (Derived X) n).Additive :=
  inferInstanceAs ((shiftFunctor (DerivedCategory X.Modules) n).Additive)

instance instPretriangulatedDerived (X : Scheme.{u}) : Pretriangulated (Derived X) :=
  inferInstanceAs (Pretriangulated (DerivedCategory X.Modules))

instance derived_isTriangulated (X : Scheme.{u}) : IsTriangulated (Derived X) :=
  inferInstanceAs (IsTriangulated (DerivedCategory X.Modules))

instance toDerived_additive (X : Scheme.{u}) : (toDerived X).Additive :=
  inferInstanceAs ((DerivedCategory.Q (C := X.Modules)).Additive)

instance instCommShiftToDerived (X : Scheme.{u}) : (toDerived X).CommShift ℤ :=
  inferInstanceAs ((DerivedCategory.Q (C := X.Modules)).CommShift ℤ)

/-- The actual derived triangle associated to a short exact sequence. -/
def shortExactTriangle {X : Scheme.{u}} {S : ShortComplex (Complex X)} (hS : S.ShortExact) :
    Triangle (Derived X) := DerivedCategory.triangleOfSES hS

/-- Its distinguishedness is a theorem from the actual exact sequence. -/
theorem shortExactTriangle_distinguished {X : Scheme.{u}} {S : ShortComplex (Complex X)}
    (hS : S.ShortExact) : shortExactTriangle hS ∈ distTriang (Derived X) :=
  DerivedCategory.triangleOfSES_distinguished hS

/-- The image of a chain mapping-cone triangle is distinguished. -/
theorem mappingConeTriangle_distinguished {X : Scheme.{u}} {K L : Complex X} (f : K ⟶ L) :
    (toDerived X).mapTriangle.obj (CochainComplex.mappingCone.triangle f) ∈ distTriang (Derived X)
      :=
  DerivedCategory.mappingCone_triangle_distinguished f

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The triangulated derived restriction constructed from actual exact
restriction of module sheaves. -/
def exactDerivedRestrict : Derived X ⥤ Derived U :=
  (Scheme.Modules.restrictFunctor j).mapDerivedCategory

instance instCommShiftExactDerivedRestrict : (exactDerivedRestrict j).CommShift ℤ :=
  inferInstanceAs ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.CommShift ℤ)

instance exactDerivedRestrict_isTriangulated : (exactDerivedRestrict j).IsTriangulated :=
  inferInstanceAs ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.IsTriangulated)

/-- The localization factorization for the triangulated restriction model. -/
def exactDerivedRestrictFactors :
    toDerived X ⋙ exactDerivedRestrict j ≅ restrict j ⋙ toDerived U :=
  (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors

end Quillen.PerfectComplexes
