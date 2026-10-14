/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.OriginalLineContractionComplexes
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.GodementTensorUnit
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.OriginalUnitPostcomposition

/-! # Natural weak original line contractions after Godement totalization

The literal maps insert the original Godement augmentation inside the left line
tensor. The determinant pairing and the original right-tensor braiding contract
the unresolved pair before the original outer total is applied.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
namespace Quillen.SchemeSheaf

/-- The unresolved pair followed by the actual outer total. -/
def godementContractionPlain (X : Scheme.{u}) (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) :
    CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules :=
  (F.mapCochainComplexPlus ⋙
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus) ⋙ godementTotalPlus X

/-- The literal resolved pair, with a Godement total between its two tensors. -/
def godementContractionResolved (X : Scheme.{u}) (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) :
    CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules :=
  ((F.mapCochainComplexPlus ⋙ godementTotalPlus X) ⋙
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus) ⋙ godementTotalPlus X

/-- The actual module contraction, lifted with its original comparison units and total. -/
def godementContractionPlainIso {X : Scheme.{u}} (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) (e : F ⋙ moduleTensorLeftFunctor X E ≅ 𝟭 X.Modules) :
    godementContractionPlain X F E ≅ godementTotalPlus X :=
  isoWhiskerRight (plusContractionIso F (moduleTensorLeftFunctor X E) e)
      (godementTotalPlus X) ≪≫ Functor.leftUnitor (godementTotalPlus X)

/-- The actual inner augmentation after the input functor, before tensor and outer total. -/
def godementContractionInputUnit (X : Scheme.{u}) (F : X.Modules ⥤ X.Modules)
    [F.Additive] : F.mapCochainComplexPlus ⟶ F.mapCochainComplexPlus ⋙ godementTotalPlus X :=
  originalNaturalUnitPrecompose (godementTotalPlus X) F.mapCochainComplexPlus
    (godementTotalPlusUnit X)

/-- The actual input unit is weak, without a resolution premise. -/
theorem godementContractionInputUnit_quasiIso {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementContractionInputUnit X F).app K).hom :=
  originalNaturalUnitPrecompose_quasiIso _ _ _ (godementTotalPlusUnit_quasiIso X) K

/-- The literal left tensor of the input augmentation, before the outer total. -/
def godementContractionPreTotalMap (X : Scheme.{u}) (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) :
    F.mapCochainComplexPlus ⋙ (moduleTensorLeftFunctor X E).mapCochainComplexPlus ⟶
      (F.mapCochainComplexPlus ⋙ godementTotalPlus X) ⋙
        (moduleTensorLeftFunctor X E).mapCochainComplexPlus :=
  Functor.whiskerRight (godementContractionInputUnit X F)
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus

/-- The proved exact left tensor makes the actual pre-total map weak. -/
theorem godementContractionPreTotalMap_quasiIso {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules)
    [IsFiniteLocallyFree X E] (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementContractionPreTotalMap X F E).app K).hom :=
  originalPlusNatTransPostcomposeWeak _ _ (godementContractionInputUnit_quasiIso F)
    (fun f hf => by
      let := hf
      exact exactPlus_map_quasiIso _ f) K

/-- Insert the original augmentation inside the original left tensor. -/
def godementContractionInsertion (X : Scheme.{u}) (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) :
    godementContractionPlain X F E ⟶ godementContractionResolved X F E :=
  Functor.whiskerRight (godementContractionPreTotalMap X F E) (godementTotalPlus X)

/-- The insertion is a weak arrow for every original Plus input. -/
theorem godementContractionInsertion_quasiIso {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules)
    [IsFiniteLocallyFree X E] (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementContractionInsertion X F E).app K).hom :=
  originalPlusNatTransPostcomposeWeak _ _ (godementContractionPreTotalMap_quasiIso F E)
    (fun f hf => by
      let := hf
      exact godementTotalPlus_map_quasiIso f) K

/-- The contracted total maps naturally and weakly to the resolved pair. -/
def godementContractionMap {X : Scheme.{u}} (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) (e : F ⋙ moduleTensorLeftFunctor X E ≅ 𝟭 X.Modules) :
    godementTotalPlus X ⟶ godementContractionResolved X F E :=
  (godementContractionPlainIso F E e).inv ≫ godementContractionInsertion X F E

/-- The literal map first reverses the same original contraction, then inserts the unit. -/
lemma godementContractionMap_app {X : Scheme.{u}} (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) (e : F ⋙ moduleTensorLeftFunctor X E ≅ 𝟭 X.Modules)
    (K : CochainComplex.Plus X.Modules) :
    (godementContractionMap F E e).app K =
      (godementContractionPlainIso F E e).inv.app K ≫
        (godementContractionInsertion X F E).app K := rfl

/-- Both legs of the actual comparison are weak, with no resolution premise. -/
theorem godementContractionMap_quasiIso {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules)
    [IsFiniteLocallyFree X E] (e : F ⋙ moduleTensorLeftFunctor X E ≅ 𝟭 X.Modules)
    (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementContractionMap F E e).app K).hom :=
  originalPlusNatTransWeakComp _ _
    (fun C => originalPlusIsoWeak ((godementContractionPlainIso F E e).inv.app C))
    (fun C => godementContractionInsertion_quasiIso F E C) K

/-- The actual resolved pair has the same specified lower bound as its input. -/
theorem godementContractionResolved_sameLowerBound {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules)
    (K : CochainComplex.Plus X.Modules) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((godementContractionResolved X F E).obj K).obj.IsStrictlyGE a := by
  have : (F.mapCochainComplexPlus.obj K).obj.IsStrictlyGE a :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (.up ℤ)).obj K.obj) a)
  have : ((godementTotalPlus X).obj (F.mapCochainComplexPlus.obj K)).obj.IsStrictlyGE a :=
    godementTotalPlus_sameLowerBound (F.mapCochainComplexPlus.obj K) a
  have : ((moduleTensorLeftFunctor X E).mapCochainComplexPlus.obj
      ((godementTotalPlus X).obj (F.mapCochainComplexPlus.obj K))).obj.IsStrictlyGE a :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      (((moduleTensorLeftFunctor X E).mapHomologicalComplex (.up ℤ)).obj
        ((godementTotalPlus X).obj (F.mapCochainComplexPlus.obj K)).obj) a)
  let B := ((F.mapCochainComplexPlus ⋙ godementTotalPlus X) ⋙
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus).obj K
  have : B.obj.IsStrictlyGE a := inferInstanceAs
    (((moduleTensorLeftFunctor X E).mapCochainComplexPlus.obj
      ((godementTotalPlus X).obj (F.mapCochainComplexPlus.obj K))).obj.IsStrictlyGE a)
  exact godementTotalPlus_sameLowerBound B a

/-- Every degree of the resolved pair is flasque through its actual outer total. -/
theorem godementContractionResolved_termwiseFlasque {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules)
    (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    TopCat.Presheaf.IsFlasque
      (((godementContractionResolved X F E).obj K).obj.X n).presheaf :=
  godementTotalPlus_termwiseFlasque
    ((moduleTensorLeftFunctor X E).mapCochainComplexPlus.obj
      ((godementTotalPlus X).obj (F.mapCochainComplexPlus.obj K))) n

end Quillen.SchemeSheaf

namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf
variable (R : CommRingCat.{u})

/-- The literal total T(L tensor T(Q tensor K)). -/
def originalLeftLineGodementResolved :=
  godementContractionResolved (twoChartLine R)
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine R))
    (tautologicalLine R)

/-- The literal total T(L tensor T(K tensor Q)). -/
def originalRightLineGodementResolved :=
  godementContractionResolved (twoChartLine R)
    (moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R))
    (tautologicalLine R)

/-- The actual original left-pair contraction followed by the original outer total. -/
def originalLeftLineGodementPlainIso :=
  godementContractionPlainIso _ _ (originalLeftLineContractionIso R)

/-- The actual original right-pair contraction followed by the original outer total. -/
def originalRightLineGodementPlainIso :=
  godementContractionPlainIso _ _ (originalRightLineContractionIso R)

/-- The natural comparison T(K) to the actual left resolved pair. -/
def originalLeftLineGodementContractionMap :=
  godementContractionMap _ _ (originalLeftLineContractionIso R)

/-- The natural comparison T(K) to the actual right resolved pair. -/
def originalRightLineGodementContractionMap :=
  godementContractionMap _ _ (originalRightLineContractionIso R)

/-- The actual original left comparison is weak on every Plus input, including zero-ring inputs.
-/
theorem originalLeftLineGodementContractionMap_quasiIso
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    QuasiIso ((originalLeftLineGodementContractionMap R).app K).hom :=
  godementContractionMap_quasiIso _ _ (originalLeftLineContractionIso R) K

/-- The actual original right comparison is weak on every Plus input. -/
theorem originalRightLineGodementContractionMap_quasiIso
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    QuasiIso ((originalRightLineGodementContractionMap R).app K).hom :=
  godementContractionMap_quasiIso _ _ (originalRightLineContractionIso R) K

end Quillen.Scheme.ProjectiveLine
