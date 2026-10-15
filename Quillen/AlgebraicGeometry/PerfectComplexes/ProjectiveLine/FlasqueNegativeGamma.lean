/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientOperations

/-!
# The actual left negative-line total functor

The tensor is the original LEFT L tensor used by the native second Phi summand.
Only the original totalization supplies flasque terms. No flasqueness of a line
tensor is asserted, and no Godement/shift comparison is needed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueTensorAdditivity

instance inclusion_additive (X : Scheme.{u}) : (FlasqueBoundedBelow.inclusion X).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    rfl

/-- Original LEFT negative-line tensor on the actual lower-bounded source model. -/
def leftNegative (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ BoundedBelow.Obj (twoChartLine R) :=
  FlasqueBoundedBelow.inclusion (twoChartLine R) ⋙ FlasqueTwoSummands.boundedNegativeTwist R

/-- Actual target endofunctor Gamma(K)=T_P(L LEFT tensor K), in original cochain order. -/
def Gamma (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ FlasqueBoundedBelow.Obj (twoChartLine R) :=
  leftNegative R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

instance Gamma_additive (R : CommRingCat.{u}) : (Gamma R).Additive := by
  dsimp [Gamma, leftNegative]
  infer_instance

/-- The whole original totalized complex, retaining its original differential and zeros. -/
lemma Gamma_obj (R : CommRingCat.{u}) (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((Gamma R).obj K).obj =
      (godementTotal (twoChartLine R)).obj
        ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R)).obj K.obj) :=
          rfl

/-- Original left-tensor and total chain maps, with no tensor-order replacement. -/
lemma Gamma_map (R : CommRingCat.{u})
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    ((Gamma R).map f).hom =
      (godementTotal (twoChartLine R)).map
        ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R)).map f.hom) :=
          rfl

/-- Original left tensor retains any specified input lower bound. -/
lemma leftNegative_isStrictlyGE (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((leftNegative R).obj K).obj.IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)

/-- The original total supplies flasque terms while retaining the same input lower bound. -/
lemma Gamma_isStrictlyGE (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((Gamma R).obj K).obj.IsStrictlyGE a := by
  let : ((leftNegative R).obj K).obj.IsStrictlyGE a := leftNegative_isStrictlyGE R K a
  exact FlasqueBoundedBelow.total_isStrictlyGE (twoChartLine R) ((leftNegative R).obj K) a

/-- Every actual totalized output term is flasque. -/
lemma Gamma_flasque (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((Gamma R).obj K).obj.X n).presheaf :=
  ((Gamma R).obj K).property.2 n

/-- Original local line trivializations and the actual total unit give local perfection. -/
lemma Gamma_locallyPerfect (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    locallyPerfect (twoChartLine R) ((Gamma R).obj K).obj :=
  ((Gamma R).obj K).property.1.1

/-- The inherited exact structure is the original actual-complex flasque-perfect structure. -/
abbrev exactStructure (R : CommRingCat.{u}) :=
  ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
    (FlasqueBoundedBelow.objects (twoChartLine R))

/-- Actual conflations map through the exact original LEFT tensor and exact totalization. -/
def GammaExactFunctor (R : CommRingCat.{u}) :
    ExactFunctor (exactStructure R) (exactStructure R) where
  toFunctor := Gamma R
  map_conflation S hS := by
    change (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact at hS
    change (((S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).map
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R))).map
        (godementTotal (twoChartLine R))).ShortExact
    exact godementTotal_shortExact (hS.map_of_exact _)

/-- Actual inherited weak arrows and quotient-bearing cofibrations are preserved. -/
lemma Gamma_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (Gamma R) :=
  ((FlasqueBoundedBelow.inclusion_exact (twoChartLine R)).comp
    (FlasqueTwoSummands.boundedNegativeTwist_exact R)).comp
      (FlasqueBoundedBelow.total_exact (twoChartLine R))

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueTensorAdditivity
