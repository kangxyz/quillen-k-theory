/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.ScalarRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.OpenCone
public import Aglib.Algebra.Homology.MappingCone.ShortExact
public import Aglib.Algebra.Homology.MappingCone.WeakMap
public import Aglib.CategoryTheory.ExactCategory.FunctorPushout
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# Actual scalar cones on perfect and supported complexes

The literal signed scalar cone and cone maps preserve inherited short exact sequences. A scalar invertible on the specified open gives the same supported cone; no scalar regularity is assumed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

/-- The literal perfect cone of the original global scalar, on objects and maps. -/
def perfectScalarConeFunctor (X : Scheme.{u}) (r : Γ(X, ⊤)) : Perfect X ⥤ Perfect X :=
  (locallyPerfect X).lift
    (mappingConeNatTransFunctor (Functor.whiskerRight (perfectGlobalScalar X r)
      (locallyPerfect X).ι))
    (fun K => locallyPerfect_mappingCone K.property K.property
      ((complexGlobalScalar X r).app K.obj))

/-- The map is the actual signed cone map on the two unchanged coefficient maps. -/
theorem perfectScalarConeFunctor_map_hom (X : Scheme.{u}) (r : Γ(X, ⊤))
    {K L : Perfect X} (g : K ⟶ L) :
    ((perfectScalarConeFunctor X r).map g).hom =
      CochainComplex.mappingCone.map ((complexGlobalScalar X r).app K.obj)
        ((complexGlobalScalar X r).app L.obj) g.hom g.hom
        ((complexGlobalScalar X r).naturality g.hom).symm := rfl

instance perfectScalarConeFunctor_additive (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    (perfectScalarConeFunctor X r).Additive := by
  unfold perfectScalarConeFunctor
  infer_instance

/-- Scalar cones preserve genuine inherited abelian conflations. -/
def perfectScalarConeExactFunctor (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    ExactFunctor (ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex X.Modules ℤ))
      (locallyPerfect X))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
        (locallyPerfect X)) where
  toFunctor := perfectScalarConeFunctor X r
  map_conflation S hS :=
    mappingConeNatTransFunctor_shortExact
      (Functor.whiskerRight (perfectGlobalScalar X r) (locallyPerfect X).ι) S hS hS

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The same scalar cones, with the original open support proof. -/
def perfectSupportedScalarConeFunctor :
    Perfect X ⥤ (perfectSupported j).FullSubcategory :=
  (perfectSupported j).lift
    (mappingConeNatTransFunctor (Functor.whiskerRight (perfectGlobalScalar X r)
      (locallyPerfect X).ι))
    (fun K => perfectOpenWeak_mappingCone_supported j ((perfectGlobalScalar X r).app K)
      (perfectGlobalScalar_openWeak j r q hq K))

instance perfectSupportedScalarConeFunctor_additive :
    (perfectSupportedScalarConeFunctor j r q hq).Additive := by
  unfold perfectSupportedScalarConeFunctor
  infer_instance

/-- Support does not change the preservation of actual inherited conflations. -/
def perfectSupportedScalarConeExactFunctor :
    ExactFunctor (ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex X.Modules ℤ))
      (locallyPerfect X))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
        (perfectSupported j)) where
  toFunctor := perfectSupportedScalarConeFunctor j r q hq
  map_conflation S hS :=
    mappingConeNatTransFunctor_shortExact
      (Functor.whiskerRight (perfectGlobalScalar X r) (locallyPerfect X).ι) S hS hS

end Quillen.PerfectComplexes

end

end
