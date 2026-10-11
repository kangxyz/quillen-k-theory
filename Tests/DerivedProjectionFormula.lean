/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.DerivedProjectionFormula
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalIncidence
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalQuotient

/-!
# Original-map consumers of the derived projection formula

Retain original open restrictions, finite-free retractions, installed units,
ordinary projection arrows, arbitrary derived maps, and the actual second
projection and quotient line on the genuine projective-line square.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
namespace Quillen.Tests.DerivedProjectionFormula

/-- Standard original derived categories for the geometric consumers. -/
local instance projectionConsumerStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- Local detection retains the literal original restricted cochain maps. -/
theorem original_local_quasi_iso {X : Scheme.{u}} {ι : Type v}
    (U : ι → Scheme.{u}) (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : U i), j i y = x)
    {K L : CochainComplex X.Modules ℤ} (q : K ⟶ L)
    (hq : ∀ i, QuasiIso (((Scheme.Modules.restrictFunctor (j i)).mapHomologicalComplex
      (.up ℤ)).map q)) : QuasiIso q :=
  quasiIso_of_restrict_openCover U j hcover q hq

/-- The original locally flasque computation has no upper bound on the complex. -/
theorem original_local_unit_inverse {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type v}
    (U : ι → Scheme.{u}) (j : ∀ i, U i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ y : Y, ∃ (i : ι) (z : U i), j i z = y)
    (K : CochainComplex.Plus X.Modules)
    (hK : ∀ i n, TopCat.Presheaf.IsFlasque
      ((K.obj.X n).restrict (pullback.fst f (j i))).presheaf) :
    let := isIso_derivedPushforwardPlusUnit_of_locally_flasque f U j hcover K hK
    (derivedPushforwardPlusUnit f).app K ≫ inv ((derivedPushforwardPlusUnit f).app K) = 𝟙 _ := by
  let := isIso_derivedPushforwardPlusUnit_of_locally_flasque f U j hcover K hK
  exact IsIso.hom_inv_id _

/-- Empty finite-free coefficients are covered by the genuine generic injectivity result. -/
theorem empty_free_injective {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (R : Sheaf J CommRingCat) [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat]
    (M : SheafOfModulesOfCommRing R) [Injective M] :
    Injective ((SheafOfModulesOfCommRing.tensorLeftFunctor R (SheafOfModules.free
      (R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (Fin 0))).obj M) :=
  SheafOfModulesOfCommRing.tensorFiniteFree_injective R (Fin 0) M

/-- The actual tensor coefficient maps preserve the given inclusion/retraction identity. -/
theorem original_tensor_retraction {X : Scheme.{u}} {E F : X.Modules}
    (h : Retract E F) (M : X.Modules) :
    (moduleTensorCoefficientMap X h.i).app M ≫
      (moduleTensorCoefficientMap X h.r).app M = 𝟙 _ := by
  exact congrArg (fun α => α.app M)
    (h.map (SheafOfModulesOfCommRing.tensorFunctor X.sheaf)).retract
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Y.Modules) [IsFiniteLocallyFree Y E]

/-- Each degree of the comparison is the literal existing ordinary projection map. -/
theorem original_projection_degree (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    ((NatIso.mapCochainComplexPlus (projectionFormulaNatIso f E)).hom.app K).hom.f n =
      projectionFormulaMap f E (K.obj.X n) := rfl

/-- The exact tensor comparison retains the inverse of its actual installed unit. -/
theorem original_tensor_unit_inverse (K : CochainComplex.Plus Y.Modules) :
    let := isIso_moduleTensorLeft_derivedUnit E
    (moduleTensorLeftFunctor Y E).rightDerivedFunctorPlusUnit.app K ≫
      inv ((moduleTensorLeftFunctor Y E).rightDerivedFunctorPlusUnit.app K) = 𝟙 _ := by
  let := isIso_moduleTensorLeft_derivedUnit E
  exact IsIso.hom_inv_id _

/-- Both sides expand to the original installed tensor and direct-image units. -/
theorem original_projection_units (K : CochainComplex.Plus X.Modules) :
    (moduleTensorLeftFunctor Y E).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj K) ≫
      (moduleTensorLeftFunctor Y E).rightDerivedFunctorPlus.map
        ((derivedPushforwardPlusUnit f).app K) ≫
      (derivedProjectionFormulaIso f E).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
      ((NatIso.mapCochainComplexPlus (projectionFormulaNatIso f E)).hom.app K) ≫
      (derivedPushforwardPlusUnit f).app
        ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).mapCochainComplexPlus.obj
          K) ≫
      (derivedPushforwardPlus f).map
        ((moduleTensorLeftFunctor X
          ((Scheme.Modules.pullback f).obj E)).rightDerivedFunctorPlusUnit.app
          K) := by
  have h := derivedProjectionFormulaIso_unit f E K
  rw [Functor.rightDerivedFunctorPlusCompUnit_app,
    Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc] at h
  exact h

/-- Naturality applies to arbitrary original bounded-below derived arrows. -/
theorem original_projection_naturality
    {K L : DerivedCategory.Plus X.Modules} (q : K ⟶ L) :
    (moduleTensorLeftFunctor Y E).rightDerivedFunctorPlus.map
        ((derivedPushforwardPlus f).map q) ≫
      (derivedProjectionFormulaIso f E).hom.app L =
    (derivedProjectionFormulaIso f E).hom.app K ≫
      (derivedPushforwardPlus f).map
        ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).rightDerivedFunctorPlus.map
          q) :=
  (derivedProjectionFormulaIso f E).hom.naturality q

/-- The actual Rp₂ comparison uses the original quotient line and pullback coefficient. -/
def originalSecondProjectionQuotient (R : CommRingCat.{u}) :
    derivedPushforwardPlus (relativeSecond R) ⋙
      (moduleTensorLeftFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus ≅
    (moduleTensorLeftFunctor (relativeSquare R)
      ((Scheme.Modules.pullback (relativeSecond R)).obj
        (tautologicalQuotientLine R))).rightDerivedFunctorPlus ⋙
      derivedPushforwardPlus (relativeSecond R) :=
  derivedProjectionFormulaIso (relativeSecond R) (tautologicalQuotientLine R)

end Quillen.Tests.DerivedProjectionFormula
