/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.EulerAdditivity
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.EulerMiddle
public import Quillen.AlgebraicGeometry.PerfectComplexes.FlasqueShift
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.LineTensorAssociator

/-! # The original Euler O(-2)[1] coefficient identity on every connective K-group -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.Euler
open FlasqueCoefficients
variable (R : CommRingCat.{u})

/-- Two actual line factors use the native original sheafification units and associator. -/
def twoLineAssociator :
    tensorByLineComplex (tautologicalLine R) ⋙ tensorByLineComplex (tautologicalLine R) ≅
      tensorByLineComplex (sequence R).X₁ :=
  Functor.mapHomologicalComplexCompIso
    (moduleLineTensorAssociator (tautologicalLine R) (tautologicalLine R)
      (fun _ : Bool => Spec (CommRingCat.of (Polynomial R)))
      (lineChart R) (lineChart_cover R) (lineChartIso R) (lineChartIso R)) (.up ℤ)

/-- Original (L tensor p*A) tensor L uses the actual symmetry and two-line associator. -/
def originalRightTensorIso :
    endpointComplex R (tautologicalLine R) ⋙ tensorByLineRightComplex (tautologicalLine R) ≅
      endpointComplex R (sequence R).X₁ :=
  Functor.isoWhiskerLeft ((strictPerfect (Spec R)).ι ⋙ pullbackComplex (projection R))
    (Functor.isoWhiskerLeft (tensorByLineComplex (tautologicalLine R))
      (tensorByLineComplexSymmetry (tautologicalLine R)).symm ≪≫ twoLineAssociator R)

/-- Euler additivity and the canonical weak-zero middle give the literal inverse coefficient. -/
lemma KMap_E2_inv_eq_E0 (n : ℕ) (x : (strictWaldhausen (Spec R)).K n) :
    (Waldhausen.KMap (E2_exact R) n x)⁻¹ = Waldhausen.KMap (E0_exact R) n x := by
  have he := KMap_euler_additivity R n x
  simp only [KMap_E1_zero, MonoidHom.one_apply] at he
  calc
    (Waldhausen.KMap (E2_exact R) n x)⁻¹ =
        (Waldhausen.KMap (E2_exact R) n x)⁻¹ * 1 := (mul_one _).symm
    _ = (Waldhausen.KMap (E2_exact R) n x)⁻¹ *
        (Waldhausen.KMap (E2_exact R) n x * Waldhausen.KMap (E0_exact R) n x) := by rw [← he]
    _ = Waldhausen.KMap (E0_exact R) n x := inv_mul_cancel_left _ _

/-- Every original projected endpoint retains the coefficient's specified strict lower bound. -/
lemma projectedEndpoint_isStrictlyGE (M : (twoChartLine R).Modules)
    (hM : ∀ A, strictPerfect (twoChartLine R) ((endpointComplex R M).obj A))
    (A : StrictPerfect (Spec R)) (a : ℤ) [A.obj.IsStrictlyGE a] :
    ((projectedEndpoint R M hM).obj A).obj.IsStrictlyGE a := by
  have ht : ((endpointBounded R M hM).obj A).obj.IsStrictlyGE a :=
    endpointComplex_isStrictlyGE R M A a
  let := ht
  have hT : ((FlasqueBoundedBelow.total (twoChartLine R)).obj
      ((endpointBounded R M hM).obj A)).obj.IsStrictlyGE a :=
    FlasqueBoundedBelow.total_isStrictlyGE _ _ a
  let := hT
  exact G0Raw_isStrictlyGE R _ a

/-- The literal projected O(-2) coefficient, with the original functors and tensor association. -/
lemma E2_obj_underlying (A : StrictPerfect (Spec R)) : ((E2 R).obj A).obj =
    ((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ)).obj
      ((godementTotal (twoChartLine R)).obj
        ((tensorByLineComplex ((moduleTensorLeftFunctor (twoChartLine R)
          (tautologicalLine R)).obj (tautologicalLine R))).obj
          ((pullbackComplex (projection R)).obj A.obj))) := rfl

/-- Every original coefficient arrow retains the original tensor, total, and projection maps. -/
lemma E2_map_underlying {A B : StrictPerfect (Spec R)} (f : A ⟶ B) :
    ((E2 R).map f).hom =
      ((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ)).map
        ((godementTotal (twoChartLine R)).map
          ((tensorByLineComplex ((moduleTensorLeftFunctor (twoChartLine R)
            (tautologicalLine R)).obj (tautologicalLine R))).map
            ((pullbackComplex (projection R)).map f.hom))) := rfl

/-- The actual original signed shift of the projected Euler square coefficient. -/
def E2Shift := E2 R ⋙ modelShift (Spec R) 1

lemma E2Shift_exact : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (E2Shift R) :=
  (E2_exact R).comp (modelShift_exact (Spec R) 1)

/-- A specified original coefficient bound a becomes exactly a-1 after the signed shift. -/
lemma E2Shift_isStrictlyGE (A : StrictPerfect (Spec R)) (a : ℤ) [A.obj.IsStrictlyGE a] :
    ((E2Shift R).obj A).obj.IsStrictlyGE (a - 1) := by
  have hp : ((E2 R).obj A).obj.IsStrictlyGE a := projectedEndpoint_isStrictlyGE R _ _ A a
  let := hp
  change (((E2 R).obj A).obj⟦(1 : ℤ)⟧).IsStrictlyGE (a - 1)
  exact CochainComplex.isStrictlyGE_shift ((E2 R).obj A).obj a 1 (a - 1) (by omega)

/-- Original KMap(E2[1]) equals original KMap(E0), with original rebasing for all n including 0. -/
lemma KMap_E2Shift_eq_E0 (n : ℕ) :
    Waldhausen.KMap (E2Shift_exact R) n = Waldhausen.KMap (E0_exact R) n := by
  change Waldhausen.KMap ((E2_exact R).comp (modelShift_exact (Spec R) 1)) n = _
  rw [← Waldhausen.KMap_comp_KMap (E2_exact R) (modelShift_exact (Spec R) 1) n]
  apply MonoidHom.ext
  intro x
  exact (FlasqueBoundedBelow.KMap_modelShift_one_apply (Spec R) n
    (Waldhausen.KMap (E2_exact R) n x)).trans (KMap_E2_inv_eq_E0 R n x)

end Quillen.PerfectComplexes.ProjectiveLine.Euler
