/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.FlatPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.LocalDescent
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.TensorDerivedPushforward

/-! # Exact tensor with an actually trivialized line on locally perfect complexes

Degreewise tensor uses the original sheafified tensor functor. Actual line
trivializations identify its open restrictions with the original restrictions.
This proves preservation of the local perfect predicate, with no global strict
representative and no derived tensor product of two arbitrary complexes.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
open Quillen.SchemeSheaf
open CategoryTheory.MonoidalCategory

/-- Local perfection descends along actual open-immersion covers. -/
theorem locallyPerfect_of_openImmersionCover {X : Scheme.{u}} {K : Complex X}
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
    ⟨(toDerived O.toScheme).mapIso (ec.app K).symm ≪≫ restrictDerivedIso e.inv eP⟩⟩

instance moduleTensor_preservesFiniteLimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteLimits (moduleTensorLeftFunctor X L) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance moduleTensor_preservesFiniteColimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteColimits (moduleTensorLeftFunctor X L) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Degreewise original sheafified tensor with the fixed line. -/
def tensorByLineComplex {X : Scheme.{u}} (L : X.Modules) : Complex X ⥤ Complex X :=
  (moduleTensorLeftFunctor X L).mapHomologicalComplex (ComplexShape.up ℤ)

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

/-- Degreewise original tensor in the convention K tensor L. -/
def tensorByLineRightComplex {X : Scheme.{u}} (L : X.Modules) : Complex X ⥤ Complex X :=
  (moduleTensorByLineRight L).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The order comparison is a natural chain isomorphism, using the original tensor symmetry. -/
def tensorByLineComplexSymmetry {X : Scheme.{u}} (L : X.Modules) :
    tensorByLineComplex L ≅ tensorByLineRightComplex L :=
  NatIso.mapHomologicalComplex (moduleTensorByLineSymmetry L) _

instance tensorByLineComplex_additive {X : Scheme.{u}} (L : X.Modules) :
    (tensorByLineComplex L).Additive := by unfold tensorByLineComplex; infer_instance

instance tensorByLineComplex_preservesFiniteLimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteLimits (tensorByLineComplex L) := by
  unfold tensorByLineComplex
  infer_instance

instance tensorByLineComplex_preservesFiniteColimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteColimits (tensorByLineComplex L) := by
  unfold tensorByLineComplex
  infer_instance

instance tensorByLineComplex_quasiIso {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] {K M : Complex X} (f : K ⟶ M) [QuasiIso f] :
    QuasiIso ((tensorByLineComplex L).map f) := by
  unfold tensorByLineComplex
  infer_instance

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
    tensorByLineComplex L ⋙ restrict j ≅ restrict j :=
  Functor.mapHomologicalComplexCompIso (tensorByLineModuleChartIso j L e) _

variable {X : Scheme.{u}} (L : X.Modules) {ι : Type v}
  (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
  (hc : ∀ x : X, ∃ i y, j i y = x)
  (e : ∀ i, L.restrict (j i) ≅ SheafOfModules.unit (Y i).ringCatSheaf)

include hc e

/-- Actual chartwise trivial tensor preserves arbitrary locally perfect input. -/
theorem locallyPerfect_tensorByLine {K : Complex X} (hK : locallyPerfect X K) :
    locallyPerfect X ((tensorByLineComplex L).obj K) := by
  apply locallyPerfect_of_openImmersionCover Y j hc
  intro i
  exact locallyPerfect_of_iso ((tensorByLineComplexChartIso (j i) L (e i)).app K).symm
    (locallyPerfect_restrict (j i) hK)

/-- Original degreewise line tensor on the full locally-perfect category. -/
def perfectTensorByLine : Perfect X ⥤ Perfect X :=
  (locallyPerfect X).lift ((locallyPerfect X).ι ⋙ tensorByLineComplex L)
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
      (ExactSubcategory.exactStructure (abelianExactStructure (Complex X)) (locallyPerfect X))
      (ExactSubcategory.exactStructure (abelianExactStructure (Complex X)) (locallyPerfect X)) where
  toFunctor := perfectTensorByLine L Y j hc e
  map_conflation S hS := by
    change ((S.map (locallyPerfect X).ι).map (tensorByLineComplex L)).ShortExact
    exact hS.map_of_exact _

/-- The original perfect Waldhausen structure sees actual line tensor as exact. -/
theorem perfectTensorByLine_waldhausenExact :
    Waldhausen.IsExact (perfectWaldhausen X).cof (perfectWaldhausen X).weq
      (perfectWaldhausen X).cof (perfectWaldhausen X).weq (perfectTensorByLine L Y j hc e) where
  zero h := (perfectTensorByLine L Y j hc e).map_isZero h
  cofibration s hs := (perfectExactTensorByLine L Y j hc e).map_inflation s hs
  weak s hs := by
    let : QuasiIso s.hom := hs
    exact tensorByLineComplex_quasiIso L s.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (locallyPerfect X).ι
    exact (Waldhausen.fullSubcategory_map_pushout (abelianExactStructure (Complex X))
      (locallyPerfect X) hi h).map (tensorByLineComplex L)

end Quillen.PerfectComplexes
