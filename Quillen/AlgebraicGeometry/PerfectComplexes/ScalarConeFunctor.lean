/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenScalarUnit
public import Aglib.Algebra.Homology.MappingCone.ShortExact
public import Aglib.Algebra.Homology.MappingCone.WeakMap
public import Aglib.CategoryTheory.ExactCategory.FunctorPushout
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# The actual exact scalar-cone functor

The original global scalar gives literal signed cones and literal cone maps. Arbitrary inherited
abelian conflations are preserved. When that same scalar restricts to the specified unit, these
cones lift to the original supported and relative-acyclic categories. No regularity of the scalar
is required, and no boundary or degree-raising operation is identified here.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex Quillen.Waldhausen Quillen.Waldhausen.Fibration
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

/-- The original fine Waldhausen structure is preserved by the literal scalar cone. -/
theorem perfectScalarConeFunctor_waldhausenExact (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    IsExact (perfectWaldhausen X).cof (perfectWaldhausen X).weq
      (perfectWaldhausen X).cof (perfectWaldhausen X).weq (perfectScalarConeFunctor X r) where
  zero h := (perfectScalarConeFunctor X r).map_isZero h
  cofibration g hg := (perfectScalarConeExactFunctor X r).map_inflation g hg
  weak g hg := by
    let : QuasiIso g.hom := hg
    change QuasiIso (((perfectScalarConeFunctor X r).map g).hom)
    rw [perfectScalarConeFunctor_map_hom]
    exact mappingCone_map_quasiIso _ _ _ _ _
  pushout hi h := (perfectScalarConeExactFunctor X r).map_isPushout hi h

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

/-- The original supported fine structure is preserved, including actual pushouts. -/
theorem perfectSupportedScalarConeFunctor_waldhausenExact :
    IsExact (perfectWaldhausen X).cof (perfectWaldhausen X).weq
      (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (perfectSupportedScalarConeFunctor j r q hq) where
  zero h := (perfectSupportedScalarConeFunctor j r q hq).map_isZero h
  cofibration g hg := (perfectSupportedScalarConeExactFunctor j r q hq).map_inflation g hg
  weak g hg := by
    let : QuasiIso g.hom := hg
    change QuasiIso (CochainComplex.mappingCone.map _ _ g.hom g.hom
      ((complexGlobalScalar X r).naturality g.hom).symm)
    exact mappingCone_map_quasiIso _ _ _ _ _
  pushout hi h := (perfectSupportedScalarConeExactFunctor j r q hq).map_isPushout hi h

/-- The actual relative-acyclic cone functor, using the existing inverse support equivalence. -/
def perfectOpenScalarConeFunctor : Perfect X ⥤ AcyclicCategory (perfectOpenNested j) :=
  perfectSupportedScalarConeFunctor j r q hq ⋙ perfectSupportedToAcyclic j

/-- Its object is literally the original supported scalar cone. -/
theorem perfectOpenScalarConeFunctor_obj (K : Perfect X) :
    (perfectOpenScalarConeFunctor j r q hq).obj K = perfectOpenScalarCone j r q hq K := rfl

/-- Forgetting relative acyclicity gives the same actual perfect cone functor. -/
theorem perfectOpenScalarConeFunctor_comp_inclusion :
    perfectOpenScalarConeFunctor j r q hq ⋙ acyclicInclusion (perfectOpenNested j) =
      perfectScalarConeFunctor X r := rfl

/-- Exactness uses the original fine structures on both supported presentations. -/
theorem perfectOpenScalarConeFunctor_waldhausenExact :
    IsExact (perfectWaldhausen X).cof (perfectWaldhausen X).weq
      (acyclicStructure (perfectOpenNested j)).cof (acyclicStructure (perfectOpenNested j)).weq
      (perfectOpenScalarConeFunctor j r q hq) :=
  (perfectSupportedScalarConeFunctor_waldhausenExact j r q hq).comp
    (perfectSupportedToAcyclic_exact j)

/-- The genuine same-degree K-map of the original supported scalar-cone functor. -/
def perfectSupportedScalarConeKMap (n : ℕ) : PerfectK X n →* PerfectSupportedK j n :=
  KMap (perfectSupportedScalarConeFunctor_waldhausenExact j r q hq) n

/-- The genuine same-degree K-map into the original relative-acyclic model. -/
def perfectOpenScalarConeKMap (n : ℕ) :
    PerfectK X n →* (acyclicStructure (perfectOpenNested j)).K n :=
  KMap (perfectOpenScalarConeFunctor_waldhausenExact j r q hq) n

/-- Degree-zero evaluation retains the already fixed original cone object. -/
theorem perfectOpenScalarConeKMap_objectClass (K : Perfect X) :
    perfectOpenScalarConeKMap j r q hq 0 ((perfectWaldhausen X).kZeroObjectClass K) =
      (acyclicStructure (perfectOpenNested j)).kZeroObjectClass
        (perfectOpenScalarCone j r q hq K) :=
  KMap_kZeroObjectClass (perfectOpenScalarConeFunctor_waldhausenExact j r q hq) K

end Quillen.PerfectComplexes
