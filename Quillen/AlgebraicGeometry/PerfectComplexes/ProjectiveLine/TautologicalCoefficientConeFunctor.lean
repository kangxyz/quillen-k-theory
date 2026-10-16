/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoefficientCoordinate
public import Aglib.Algebra.Homology.MappingCone.ShortExact
public import Aglib.Algebra.Homology.MappingCone.WeakMap
public import Aglib.CategoryTheory.ExactCategory.FunctorPushout

/-!
# The exact original supported coefficient-cone functor

The existing perfect left-tensor functor and original first coordinate give the actual natural
transformation. Its literal signed cone maps lift to the same supported full subcategory.
Genuine short-exact preservation gives inherited cofibrations and pushouts; the actual cone
triangles separately give weak preservation. The resulting supported cone K-map is not yet a
comparison with the original model-level Laurent loop operation or its all-degree boundary.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex Quillen.Waldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine

/-- The existing perfect coordinate transformation for the original tautological first arrow. -/
def tautologicalCoefficientPerfectTransformation (R : CommRingCat.{u}) :
    perfectTensorByLine (tautologicalLine R)
      (fun _ : Bool => Spec (.of (Polynomial R))) (polynomialChart R)
      (polynomialChart_cover R) (fun b => by
        cases b
        · exact tautologicalLineMinusIso R
        · exact tautologicalLinePlusIso R) ⟶ 𝟭 (Perfect (twoChartLine R)) :=
  perfectLineCoordinate _ _ _ _ _ (tautologicalFirstCoordinate R)

/-- Every component is exactly the already fixed coefficient coordinate. -/
theorem tautologicalCoefficientPerfectTransformation_app (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (tautologicalCoefficientPerfectTransformation R).app K =
      tautologicalCoefficientPerfectCoordinate R K := rfl

/-- Literal signed cones and literal cone maps in the original supported category. -/
def tautologicalCoefficientConeFunctor (R : CommRingCat.{u}) :
    Perfect (twoChartLine R) ⥤ (perfectSupported (plusChart R)).FullSubcategory :=
  (perfectSupported (plusChart R)).lift
    (mappingConeNatTransFunctor (Functor.whiskerRight
      (tautologicalCoefficientPerfectTransformation R) (locallyPerfect (twoChartLine R)).ι))
    (fun K => (tautologicalCoefficientSupportedCone R K).property)

/-- The exact functor retains the same literal supported cone object. -/
theorem tautologicalCoefficientConeFunctor_obj (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (tautologicalCoefficientConeFunctor R).obj K = tautologicalCoefficientSupportedCone R K := rfl

/-- The underlying map is the original cone map of the actual left tensor and coefficient map. -/
theorem tautologicalCoefficientConeFunctor_map_hom (R : CommRingCat.{u})
    {K L : Perfect (twoChartLine R)} (g : K ⟶ L) :
    ((tautologicalCoefficientConeFunctor R).map g).hom =
      CochainComplex.mappingCone.map
        (tautologicalCoefficientPerfectCoordinate R K).hom
        (tautologicalCoefficientPerfectCoordinate R L).hom
        ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R)).map g.hom) g.hom
        ((tautologicalCoefficientCoordinate R).naturality g.hom).symm := rfl

instance tautologicalCoefficientConeFunctor_additive (R : CommRingCat.{u}) :
    (tautologicalCoefficientConeFunctor R).Additive := by
  unfold tautologicalCoefficientConeFunctor
  infer_instance

/-- The actual cone functor preserves the inherited abelian conflations. -/
def tautologicalCoefficientConeExactFunctor (R : CommRingCat.{u}) :
    CategoryTheory.ExactCategory.ExactFunctor
      (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
        (CategoryTheory.ExactCategory.abelianExactStructure
          (CochainComplex (twoChartLine R).Modules ℤ)) (locallyPerfect _))
      (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
        (CategoryTheory.ExactCategory.abelianExactStructure
          (CochainComplex (twoChartLine R).Modules ℤ))
        (perfectSupported (plusChart R))) where
  toFunctor := tautologicalCoefficientConeFunctor R
  map_conflation S hS := by
    change (S.map (mappingConeNatTransFunctor (Functor.whiskerRight
      (tautologicalCoefficientPerfectTransformation R)
      (locallyPerfect (twoChartLine R)).ι))).ShortExact
    apply mappingConeNatTransFunctor_shortExact
    · exact (perfectExactTensorByLine (tautologicalLine R)
        (fun _ : Bool => Spec (.of (Polynomial R))) (polynomialChart R)
        (polynomialChart_cover R) (fun b => by
          cases b
          · exact tautologicalLineMinusIso R
          · exact tautologicalLinePlusIso R)).map_conflation S hS
    · exact hS

/-- Original cofibrations, weak maps and actual pushouts are preserved by this supported cone. -/
theorem tautologicalCoefficientConeFunctor_waldhausenExact (R : CommRingCat.{u}) :
    Waldhausen.IsExact (perfectWaldhausen (twoChartLine R)).cof
      (perfectWaldhausen (twoChartLine R)).weq
      (perfectSupportedWaldhausen (plusChart R)).cof
      (perfectSupportedWaldhausen (plusChart R)).weq (tautologicalCoefficientConeFunctor R) where
  zero h := (tautologicalCoefficientConeFunctor R).map_isZero h
  cofibration g hg := (tautologicalCoefficientConeExactFunctor R).map_inflation g hg
  weak g hg := by
    let : QuasiIso g.hom := hg
    have : QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft
      (tautologicalLine R)).map g.hom) :=
      AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft_quasiIso (tautologicalLine R) g.hom
    change QuasiIso (((tautologicalCoefficientConeFunctor R).map g).hom)
    rw [tautologicalCoefficientConeFunctor_map_hom]
    exact mappingCone_map_quasiIso _ _ _ _ _
  pushout hi h := (tautologicalCoefficientConeExactFunctor R).map_isPushout hi h

/-- The K-map of this actual supported cone functor, in each original connective degree. -/
def tautologicalCoefficientConeKMap (R : CommRingCat.{u}) (n : ℕ) :
    PerfectK (twoChartLine R) n →* PerfectSupportedK (plusChart R) n :=
  KMap (tautologicalCoefficientConeFunctor_waldhausenExact R) n

/-- At degree zero the genuine functorial K-map is the already fixed supported object class. -/
theorem tautologicalCoefficientConeKMap_objectClass (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    tautologicalCoefficientConeKMap R 0
        ((perfectWaldhausen (twoChartLine R)).kZeroObjectClass K) =
      (perfectSupportedWaldhausen (plusChart R)).kZeroObjectClass
        (tautologicalCoefficientSupportedCone R K) :=
  KMap_kZeroObjectClass (tautologicalCoefficientConeFunctor_waldhausenExact R) K

end Quillen.PerfectComplexes.ProjectiveLine
