/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.CokernelPushout
public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueNegativeGamma
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueDiagonalComparisons
public import Quillen.Waldhausen.ExtensionCategory.Functoriality

/-! # The original diagonal conflation after actual left negative-line totalization -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueTensorAdditivity
open FlasqueDiagonal

/-- The actual three original vertex functors followed by actual Gamma. -/
def tensorVertex (R : CommRingCat.{u}) (v : Vertex) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ FlasqueBoundedBelow.Obj (twoChartLine R) :=
  E R v ⋙ Gamma R

instance tensorVertex_additive (R : CommRingCat.{u}) (v : Vertex) :
    (tensorVertex R v).Additive := by
  dsimp [tensorVertex]
  infer_instance

/-- The original incidence is mapped by the actual LEFT tensor and total endofunctor. -/
def tensorIncidence (R : CommRingCat.{u}) : tensorVertex R .first ⟶ tensorVertex R .second :=
  Functor.whiskerRight (incidence R) (Gamma R)

/-- The original quotient is mapped by the actual LEFT tensor and total endofunctor. -/
def tensorQuotient (R : CommRingCat.{u}) : tensorVertex R .second ⟶ tensorVertex R .third :=
  Functor.whiskerRight (quotient R) (Gamma R)

/-- Additive postcomposition retains the actual zero composite. -/
lemma tensorIncidence_quotient (R : CommRingCat.{u}) :
    tensorIncidence R ≫ tensorQuotient R = 0 := by
  apply NatTrans.ext
  funext K
  have hz : (incidence R).app K ≫ (quotient R).app K = 0 :=
    NatTrans.congr_app (incidence_quotient R) K
  change (Gamma R).map ((incidence R).app K) ≫ (Gamma R).map ((quotient R).app K) = 0
  rw [← (Gamma R).map_comp, hz, (Gamma R).map_zero]

/-- The actual natural original sequence after Gamma, with all three original maps. -/
def tensorSequenceFunctor (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
      ShortComplex (FlasqueBoundedBelow.Obj (twoChartLine R)) :=
  naturalSequence (tensorIncidence R) (tensorQuotient R) (tensorIncidence_quotient R)

/-- All mapped vertices and arrows are those of the original diagonal short complex. -/
lemma tensorSequence_obj (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (tensorSequenceFunctor R).obj K = ((sequenceFunctor R).obj K).map (Gamma R) := rfl

/-- This is the actual transported original diagonal conflation, with no caller SES premise. -/
lemma tensorSequence_conflation (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (exactStructure R).conflation ((tensorSequenceFunctor R).obj K) := by
  rw [tensorSequence_obj]
  exact (GammaExactFunctor R).map_conflation _ (sequence_conflation R K)

/-- The actual tensor/total vertex functors are exact for the original weak structure. -/
lemma tensorVertex_exact (R : CommRingCat.{u}) (v : Vertex) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (tensorVertex R v) :=
  (E_exact R v).comp (Gamma_exact R)

/-- Exactness of the actual third quotient forces the genuine relative-cofibration condition. -/
lemma tensorIncidence_cofibration (R : CommRingCat.{u}) :
    Waldhausen.Additivity.IsCofibrationTransformation
      (FlasqueBoundedBelow.waldhausen (twoChartLine R)) (tensorIncidence R)
      (FlasqueBoundedBelow.waldhausen (twoChartLine R)) :=
  cofibrationTransformation_of_conflations (exactStructure R) (exactStructure R)
    (FlasqueBoundedBelow.waldhausen (twoChartLine R))
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)) rfl rfl
    (tensorIncidence R) (tensorQuotient R) (tensorIncidence_quotient R)
    (tensorSequence_conflation R)
    (fun f hf => (tensorVertex_exact R .third).cofibration f hf)

/-- The actual original mapped sequence meets all structural native additivity hypotheses. -/
lemma tensorSequence_isCofibrationSequence (R : CommRingCat.{u}) :
    Waldhausen.Additivity.IsCofibrationSequence
      (FlasqueBoundedBelow.waldhausen (twoChartLine R))
      (FlasqueBoundedBelow.waldhausen (twoChartLine R))
      (tensorIncidence R) (tensorQuotient R) where
  exactF := tensorVertex_exact R .first
  exactG := tensorVertex_exact R .second
  exactH := tensorVertex_exact R .third
  cofibration := tensorIncidence_cofibration R
  cofiber K := CategoryTheory.Limits.isPushout_of_isColimit_cokernel _
    ((exactStructure R).cokernel _ (tensorSequence_conflation R K))
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).isZero _ _

/-- The literal original Reedy extension is transported by the actual exact Gamma functor. -/
def tensorExtensionFunctor (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
      Waldhausen.ExtensionCategory.Obj (FlasqueBoundedBelow.waldhausen (twoChartLine R)) :=
  extensionFunctor R ⋙ Waldhausen.ExtensionCategory.postcompose
    (FlasqueBoundedBelow.waldhausen (twoChartLine R))
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)) (Gamma_exact R)

/-- Original Reedy extension exactness followed by actual exact postcomposition. -/
lemma tensorExtension_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (Waldhausen.ExtensionCategory.waldhausenStructure
      (FlasqueBoundedBelow.waldhausen (twoChartLine R))).cof
    (Waldhausen.ExtensionCategory.waldhausenStructure
      (FlasqueBoundedBelow.waldhausen (twoChartLine R))).weq (tensorExtensionFunctor R) :=
  (extension_exact R).comp (Waldhausen.ExtensionCategory.postcompose_exact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R))
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)) (Gamma_exact R))

/-- The actual transported Reedy arrow is the mapped original incidence. -/
lemma tensorExtension_obj_hom (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((tensorExtensionFunctor R).obj K).obj.hom = (tensorIncidence R).app K := rfl

/-- The whole vertex is the original pushed coefficient total followed by actual LEFT tensor total.
-/
lemma tensorVertex_obj (R : CommRingCat.{u}) (v : Vertex)
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((tensorVertex R v).obj K).obj = (godementTotal (twoChartLine R)).obj
      ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R)).obj
        (((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)).obj
          ((godementTotal (relativeSquare R)).obj
            (((coefficient R v).mapHomologicalComplex (.up ℤ)).obj K.obj)))) := by
  change ((Gamma R).obj ((E R v).obj K)).obj = _
  rw [Gamma_obj, E_obj]

/-- The incidence chain map is actual LEFT tensor followed by total of the original incidence.
The named original incidence retains its literal pushed coefficient map and source section data.
-/
lemma tensorIncidence_original (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((tensorIncidence R).app K).hom = (godementTotal (twoChartLine R)).map
      ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R)).map ((incidence
        R).app K).hom) :=
  Gamma_map R ((incidence R).app K)

/-- The quotient chain map is actual LEFT tensor followed by total of the original quotient.
The named original quotient retains its literal closed-diagonal coefficient and section data.
-/
lemma tensorQuotient_original (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((tensorQuotient R).app K).hom = (godementTotal (twoChartLine R)).map
      ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R)).map ((quotient
        R).app K).hom) :=
  Gamma_map R ((quotient R).app K)

/-- Each transported original vertex retains the specified input lower bound. -/
lemma tensorVertex_isStrictlyGE (R : CommRingCat.{u}) (v : Vertex)
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((tensorVertex R v).obj K).obj.IsStrictlyGE a := by
  let : ((E R v).obj K).obj.IsStrictlyGE a := raw_isStrictlyGE R v K a
  exact Gamma_isStrictlyGE R ((E R v).obj K) a

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueTensorAdditivity
