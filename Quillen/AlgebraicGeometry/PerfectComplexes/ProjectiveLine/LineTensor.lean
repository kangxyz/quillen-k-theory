/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.FlatPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.LocalDescent
public import Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.TensorPushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
/-! # Exact tensor with an actually trivialized line on locally perfect complexes

Degreewise tensor uses the original sheafified tensor functor. Actual line
trivializations identify its open restrictions with the original restrictions.
This proves preservation of the local perfect predicate, with no global strict
representative and no derived tensor product of two arbitrary complexes.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen



open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.MonoidalCategory

/-- Local perfection descends along actual open-immersion covers. -/
theorem locallyPerfect_of_openImmersionCover {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
    {ι : Type v} (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hc : ∀ x : X, ∃ i y, j i y = x)
    (hK : ∀ i, locallyPerfect (Y i) ((restrict (j i)).obj K)) : locallyPerfect X K := by
  intro x
  obtain ⟨i, y, rfl⟩ := hc x
  obtain ⟨V, hy, P, ⟨eP⟩⟩ := hK i y
  let O : X.Opens := j i ''ᵁ V
  let e : V.toScheme ≅ O.toScheme := (j i).isoImage V
  let ec : (restrict (j i) ⋙ restrict V.ι) ⋙ restrict e.inv ≅ restrict O.ι :=
    Functor.isoWhiskerRight (restrictCompIso V.ι (j i)) (restrict e.inv) ≪≫
      restrictCompIso e.inv (V.ι ≫ j i) ≪≫
      eqToIso (restrict_congr ((j i).isoImage_inv_ι V))
  exact ⟨O, ⟨y, hy, rfl⟩, ⟨(restrict e.inv).obj P.obj,
    strictPerfect_restrict _ P.property⟩,
    ⟨(DerivedCategory.Q (C := O.toScheme.Modules)).mapIso
      (ec.app K).symm ≪≫ restrictDerivedIso e.inv eP⟩⟩

instance moduleTensor_preservesFiniteLimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteLimits (moduleTensorLeftFunctor X L) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance moduleTensor_preservesFiniteColimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteColimits (moduleTensorLeftFunctor X L) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- The same original sheafified tensor with the fixed line written on the right. -/
def moduleTensorByLineRight {X : Scheme.{u}} (L : X.Modules) : X.Modules ⥤ X.Modules :=
  SheafOfModulesOfCommRing.toPresheaf X.sheaf ⋙
    tensorRight ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L) ⋙
      SheafOfModulesOfCommRing.associatedSheaf X.sheaf

/-- The actual presheaf symmetry, followed by sheafification, changes the tensor order. -/
def moduleTensorByLineSymmetry {X : Scheme.{u}} (L : X.Modules) :
    moduleTensorLeftFunctor X L ≅ moduleTensorByLineRight L :=
  Functor.isoWhiskerLeft (SheafOfModulesOfCommRing.toPresheaf X.sheaf)
    (Functor.isoWhiskerRight
      ((BraidedCategory.curriedBraidingNatIso
        (PresheafOfModulesOfCommRing.{u} X.sheaf.obj)).app
          ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L))
      (SheafOfModulesOfCommRing.associatedSheaf X.sheaf))

instance moduleTensorByLineRight_additive {X : Scheme.{u}} (L : X.Modules) :
    (moduleTensorByLineRight L).Additive := Functor.additive_of_iso (moduleTensorByLineSymmetry L)

/-- An actual line trivialization supplies a natural chart tensor identification. -/
def tensorByLineModuleChartIso {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (L : X.Modules) (e : L.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) :
    moduleTensorLeftFunctor X L ⋙ Scheme.Modules.restrictFunctor j ≅
      Scheme.Modules.restrictFunctor j :=
  (tensorRestrictionNatIso j L).symm ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor j)
      ((SheafOfModulesOfCommRing.tensorFunctor Y.sheaf).mapIso e ≪≫
        SheafOfModulesOfCommRing.tensorLeftUnitIso Y.sheaf) ≪≫
    Functor.rightUnitor _

/-- The degreewise tensor comparison retains the original restriction functor. -/
def tensorByLineComplexChartIso {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (L : X.Modules) (e : L.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) :
    AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft L ⋙ restrict j ≅ restrict j :=
  Functor.mapHomologicalComplexCompIso (tensorByLineModuleChartIso j L e) _

variable {X : Scheme.{u}} (L : X.Modules) {ι : Type v}
  (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
  (hc : ∀ x : X, ∃ i y, j i y = x)
  (e : ∀ i, L.restrict (j i) ≅ SheafOfModules.unit (Y i).ringCatSheaf)

include hc e

/-- Actual chartwise trivial tensor preserves arbitrary locally perfect input. -/
theorem locallyPerfect_tensorByLine {K : CochainComplex X.Modules ℤ} (hK : locallyPerfect X K) :
    locallyPerfect X ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft L).obj K) := by
  apply locallyPerfect_of_openImmersionCover Y j hc
  intro i
  exact locallyPerfect_of_iso ((tensorByLineComplexChartIso (j i) L (e i)).app K).symm
    (locallyPerfect_restrict (j i) hK)

/-- Original degreewise line tensor on the full locally-perfect category. -/
def perfectTensorByLine : Perfect X ⥤ Perfect X :=
  (locallyPerfect X).lift ((locallyPerfect X).ι ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft L)
    (fun K => locallyPerfect_tensorByLine L Y j hc e K.property)

instance perfectTensorByLine_additive : (perfectTensorByLine L Y j hc e).Additive := by
  unfold perfectTensorByLine
  infer_instance

/-- Chart tensor trivializations lift to the actual perfect restriction functor. -/
def perfectTensorByLineChartIso (i : ι) :
    perfectTensorByLine L Y j hc e ⋙ perfectRestrict (j i) ≅ perfectRestrict (j i) :=
  Functor.fullyFaithfulCancelRight (locallyPerfect (Y i)).ι
    (Functor.isoWhiskerLeft (locallyPerfect X).ι
      (tensorByLineComplexChartIso (j i) L (e i)))

variable [IsFiniteLocallyFree X L]

/-- Actual line tensor preserves the inherited exact structure. -/
def perfectExactTensorByLine :
    ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
        (locallyPerfect X))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
        (locallyPerfect X)) where
  toFunctor := perfectTensorByLine L Y j hc e
  map_conflation S hS := by
    change ((S.map (locallyPerfect X).ι).map (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft
      L)).ShortExact
    exact hS.map_of_exact _

/-- The original perfect Waldhausen structure sees actual line tensor as exact. -/
theorem perfectTensorByLine_waldhausenExact :
    Waldhausen.IsExact (perfectWaldhausen X).cof (perfectWaldhausen X).weq
      (perfectWaldhausen X).cof (perfectWaldhausen X).weq (perfectTensorByLine L Y j hc e) where
  zero h := (perfectTensorByLine L Y j hc e).map_isZero h
  cofibration s hs := (perfectExactTensorByLine L Y j hc e).map_inflation s hs
  weak s hs := by
    let : QuasiIso s.hom := hs
    exact AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft_quasiIso L s.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (locallyPerfect X).ι
    exact (Waldhausen.fullSubcategory_map_pushout (abelianExactStructure
      (CochainComplex X.Modules ℤ))
      (locallyPerfect X) hi h).map (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft L)

end Quillen.PerfectComplexes
