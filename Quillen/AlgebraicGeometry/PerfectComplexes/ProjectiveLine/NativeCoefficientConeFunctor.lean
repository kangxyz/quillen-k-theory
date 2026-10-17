/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientCoordinate
public import Aglib.Algebra.Homology.MappingCone.ShortExact
public import Aglib.Algebra.Homology.MappingCone.WeakMap
public import Aglib.CategoryTheory.ExactCategory.FunctorPushout

/-!
# Exact native supported coefficient cones

The original global coordinate is a natural transformation from the original native negative
line tensor to the identity. Its literal signed cones and cone maps form an exact functor into
the category supported off the positive native range. No affine presentation is used.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex Quillen.Waldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine

local instance nativeNegativeTwist_additive (X : QuasiCompactSchemes.{u}) :
    (nativeNegativeTwist X).Additive := by
  unfold nativeNegativeTwist
  infer_instance

/-- The existing perfect coordinate transformation for the original tautological first arrow. -/
def coefficientPerfectTransformation (X : QuasiCompactSchemes.{u}) :
    nativeNegativeTwist X ⟶ 𝟭 (Perfect (nativeLineFunctor.obj X).obj) :=
  perfectLineCoordinate _ _ _ _ _ (nativeFirstCoordinate X)

/-- Every component is exactly the already fixed coefficient coordinate. -/
theorem coefficientPerfectTransformation_app (X : QuasiCompactSchemes.{u})
    (K : Perfect (nativeLineFunctor.obj X).obj) :
    (coefficientPerfectTransformation X).app K =
      coefficientPerfectCoordinate X K := rfl

/-- Literal signed cones and literal cone maps in the original supported category. -/
def coefficientConeFunctor (X : QuasiCompactSchemes.{u}) :
    Perfect (nativeLineFunctor.obj X).obj ⥤ (perfectSupported (positiveOpen X).ι).FullSubcategory :=
  (perfectSupported (positiveOpen X).ι).lift
    (mappingConeNatTransFunctor (Functor.whiskerRight
      (coefficientPerfectTransformation X) (locallyPerfect (nativeLineFunctor.obj X).obj).ι))
    (fun K => (coefficientSupportedCone X K).property)

/-- The exact functor retains the same literal supported cone object. -/
theorem coefficientConeFunctor_obj (X : QuasiCompactSchemes.{u})
    (K : Perfect (nativeLineFunctor.obj X).obj) :
    (coefficientConeFunctor X).obj K = coefficientSupportedCone X K := rfl

/-- The underlying map is the original cone map of the actual left tensor and coefficient map. -/
theorem coefficientConeFunctor_map_hom (X : QuasiCompactSchemes.{u})
    {K L : Perfect (nativeLineFunctor.obj X).obj} (g : K ⟶ L) :
    ((coefficientConeFunctor X).map g).hom =
      CochainComplex.mappingCone.map
        (coefficientPerfectCoordinate X K).hom
        (coefficientPerfectCoordinate X L).hom
        ((Scheme.Modules.Complex.tensorLeft (nativeTautologicalLine X)).map g.hom) g.hom
        ((coefficientCoordinate X).naturality g.hom).symm := rfl

instance coefficientConeFunctor_additive (X : QuasiCompactSchemes.{u}) :
    (coefficientConeFunctor X).Additive := by
  unfold coefficientConeFunctor
  infer_instance

/-- The actual cone functor preserves the inherited abelian conflations. -/
def coefficientConeExactFunctor (X : QuasiCompactSchemes.{u}) :
    ExactFunctor
      (ExactSubcategory.exactStructure
        (abelianExactStructure (CochainComplex (nativeLineFunctor.obj X).obj.Modules ℤ))
          (locallyPerfect _))
      (ExactSubcategory.exactStructure
        (abelianExactStructure (CochainComplex (nativeLineFunctor.obj X).obj.Modules ℤ))
        (perfectSupported (positiveOpen X).ι)) where
  toFunctor := coefficientConeFunctor X
  map_conflation S hS := by
    change (S.map (mappingConeNatTransFunctor (Functor.whiskerRight
      (coefficientPerfectTransformation X)
      (locallyPerfect (nativeLineFunctor.obj X).obj).ι))).ShortExact
    apply mappingConeNatTransFunctor_shortExact
    · exact (perfectExactTensorByLine (nativeTautologicalLine X)
        (fun _ : Bool => (Relative.polynomialFunctor.obj X).obj) (nativeChart X)
        (nativeChart_cover X) (nativeLineChartIso X)).map_conflation S hS
    · exact hS

/-- Original cofibrations, weak maps and actual pushouts are preserved by this supported cone. -/
theorem coefficientConeFunctor_waldhausenExact (X : QuasiCompactSchemes.{u}) :
    Waldhausen.IsExact (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq
      (perfectSupportedWaldhausen (positiveOpen X).ι).cof
      (perfectSupportedWaldhausen (positiveOpen X).ι).weq (coefficientConeFunctor X) where
  zero h := (coefficientConeFunctor X).map_isZero h
  cofibration g hg := (coefficientConeExactFunctor X).map_inflation g hg
  weak g hg := by
    let : QuasiIso g.hom := hg
    have : QuasiIso ((Scheme.Modules.Complex.tensorLeft (nativeTautologicalLine X)).map g.hom) :=
      Scheme.Modules.Complex.tensorLeft_quasiIso (nativeTautologicalLine X) g.hom
    change QuasiIso (((coefficientConeFunctor X).map g).hom)
    rw [coefficientConeFunctor_map_hom]
    exact mappingCone_map_quasiIso _ _ _ _ _
  pushout hi h := (coefficientConeExactFunctor X).map_isPushout hi h

/-- The K-map of this actual supported cone functor, in each original connective degree. -/
def coefficientConeKMap (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    PerfectK (nativeLineFunctor.obj X).obj n →* PerfectSupportedK (positiveOpen X).ι n :=
  KMap (coefficientConeFunctor_waldhausenExact X) n

/-- At degree zero the genuine functorial K-map is the already fixed supported object class. -/
theorem coefficientConeKMap_objectClass (X : QuasiCompactSchemes.{u})
    (K : Perfect (nativeLineFunctor.obj X).obj) :
    coefficientConeKMap X 0
        ((perfectWaldhausen (nativeLineFunctor.obj X).obj).kZeroObjectClass K) =
      (perfectSupportedWaldhausen (positiveOpen X).ι).kZeroObjectClass
        (coefficientSupportedCone X K) :=
  KMap_kZeroObjectClass (coefficientConeFunctor_waldhausenExact X) K

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
