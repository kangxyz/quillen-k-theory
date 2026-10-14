/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.StrictPositiveRetraction
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.Strictification
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.GodementBaseChangeUnit

/-! # The actual positive unit on all affine perfect bounded-below complexes

The canonical cochain map is the original geometric adjunction unit followed
by direct image of the original Godement augmentation. Its localized natural
transformation transports the proved bounded-bundle calculation through a
genuine affine derived representative; target terms need not be quasicoherent.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

local instance positiveUnitStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The literal original geometric module adjunction unit on cochain complexes. -/
def geometricPlusUnit {P X : Scheme.{u}} (p : P ⟶ X) :
    𝟭 (CochainComplex.Plus X.Modules) ⟶
      (Scheme.Modules.pullback p).mapCochainComplexPlus ⋙
        (Scheme.Modules.pushforward p).mapCochainComplexPlus where
  app K := ObjectProperty.homMk
    { f i := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (K.obj.X i)
      comm' i j _ :=
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality (K.obj.d i j)).symm }
  naturality {_ _} f := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.Hom.ext
    funext i
    exact (Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality (f.hom.f i)

/-- Actual ordinary pullback, the original total, then actual ordinary pushforward. -/
def positivePlus {P X : Scheme.{u}} (p : P ⟶ X) :
    CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules :=
  (Scheme.Modules.pullback p).mapCochainComplexPlus ⋙ godementTotalPlus P ⋙
    (Scheme.Modules.pushforward p).mapCochainComplexPlus

/-- The requested canonical unit with both original constituent maps retained. -/
def positivePlusUnit {P X : Scheme.{u}} (p : P ⟶ X) :
    𝟭 (CochainComplex.Plus X.Modules) ⟶ positivePlus p :=
  geometricPlusUnit p ≫ Functor.whiskerRight
    (Functor.whiskerLeft (Scheme.Modules.pullback p).mapCochainComplexPlus
      (godementTotalPlusUnit P)) (Scheme.Modules.pushforward p).mapCochainComplexPlus

lemma positivePlusUnit_app {P X : Scheme.{u}} (p : P ⟶ X)
    (K : CochainComplex.Plus X.Modules) :
    (positivePlusUnit p).app K = (geometricPlusUnit p).app K ≫
      (Scheme.Modules.pushforward p).mapCochainComplexPlus.map
        ((godementTotalPlusUnit P).app
          ((Scheme.Modules.pullback p).mapCochainComplexPlus.obj K)) := rfl

/-- The installed derived functor target of this same original positive unit. -/
def derivedPositive {P X : Scheme.{u}} (p : P ⟶ X) [Flat p] :
    DerivedCategory.Plus X.Modules ⥤ DerivedCategory.Plus X.Modules :=
  derivedFlatPullbackPlus p ⋙ derivedPushforwardPlus p

/-- Original geometric unit, installed direct-image unit, then installed exact pullback unit. -/
def unitOnPlus {P X : Scheme.{u}} (p : P ⟶ X) [Flat p] :
    DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ derivedPositive p :=
  Functor.whiskerRight (geometricPlusUnit p) DerivedCategory.Plus.Q ≫
    Functor.whiskerLeft (Scheme.Modules.pullback p).mapCochainComplexPlus
      (derivedPushforwardPlusUnit p) ≫
    Functor.whiskerRight (Scheme.Modules.pullback p).rightDerivedFunctorPlusUnit
      (derivedPushforwardPlus p)

local instance identityQLifting (X : Scheme.{u}) : Localization.Lifting
    DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso X.Modules)
    DerivedCategory.Plus.Q (𝟭 (DerivedCategory.Plus X.Modules)) :=
  ⟨Functor.rightUnitor _⟩

local instance positiveQLifting {P X : Scheme.{u}} (p : P ⟶ X) [Flat p] :
    Localization.Lifting DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso X.Modules)
      (DerivedCategory.Plus.Q ⋙ derivedPositive p) (derivedPositive p) := ⟨Iso.refl _⟩

/-- Localization of the same unit, used only to transport its QI property through true isos. -/
def derivedPositiveUnit {P X : Scheme.{u}} (p : P ⟶ X) [Flat p] :
    𝟭 (DerivedCategory.Plus X.Modules) ⟶ derivedPositive p :=
  Localization.liftNatTrans DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso X.Modules)
    DerivedCategory.Plus.Q (DerivedCategory.Plus.Q ⋙ derivedPositive p)
    (𝟭 (DerivedCategory.Plus X.Modules)) (derivedPositive p) (unitOnPlus p)

lemma derivedPositiveUnit_app {P X : Scheme.{u}} (p : P ⟶ X) [Flat p]
    (K : CochainComplex.Plus X.Modules) :
    (derivedPositiveUnit p).app (DerivedCategory.Plus.Q.obj K) = (unitOnPlus p).app K := by
  simp [derivedPositiveUnit, Localization.liftNatTrans_app,
    Localization.Lifting.iso, identityQLifting, positiveQLifting]

/-- The actual total-derived comparison followed by the installed exact pullback unit. -/
def positiveValueDerivedIso {P X : Scheme.{u}} (p : P ⟶ X) [Flat p]
    (K : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.obj ((positivePlus p).obj K) ≅
      (derivedPositive p).obj (DerivedCategory.Plus.Q.obj K) := by
  have : IsIso (Scheme.Modules.pullback p).rightDerivedFunctorPlusUnit :=
    isIso_derivedFlatPullbackPlusUnit p
  exact (godementTotalDerivedPushforwardIso p).app
      ((Scheme.Modules.pullback p).mapCochainComplexPlus.obj K) ≪≫
    (derivedPushforwardPlus p).mapIso
      (asIso ((Scheme.Modules.pullback p).rightDerivedFunctorPlusUnit.app K))

/-- The installed comparison cancels the actual pushed total augmentation by naturality. -/
lemma positivePlusUnit_original_comparison {P X : Scheme.{u}} (p : P ⟶ X) [Flat p]
    (K : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.map ((positivePlusUnit p).app K) ≫
        (positiveValueDerivedIso p K).hom =
      (unitOnPlus p).app K := by
  dsimp only [positiveValueDerivedIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    asIso_hom, positivePlus]
  let C := (Scheme.Modules.pullback p).mapCochainComplexPlus.obj K
  let v := (derivedPushforwardPlus p).map
    ((Scheme.Modules.pullback p).rightDerivedFunctorPlusUnit.app K)
  have hc := godementBaseChange_total_unit_cancel p C
  have he := congrArg (fun q =>
    DerivedCategory.Plus.Q.map ((geometricPlusUnit p).app K) ≫ q ≫ v) hc
  calc
    _ = DerivedCategory.Plus.Q.map ((geometricPlusUnit p).app K) ≫
        (DerivedCategory.Plus.Q.map
          ((Scheme.Modules.pushforward p).mapCochainComplexPlus.map
            ((godementTotalPlusUnit P).app C)) ≫
          (godementTotalDerivedPushforwardIso p).hom.app C) ≫ v := by
      rw [positivePlusUnit_app, Functor.map_comp]
      dsimp only [C, v]
      simp only [Category.assoc]
    _ = DerivedCategory.Plus.Q.map ((geometricPlusUnit p).app K) ≫
        (derivedPushforwardPlusUnit p).app C ≫ v := he
    _ = _ := rfl

lemma unitOnPlus_isIso_of_quasiIso {P X : Scheme.{u}} (p : P ⟶ X) [Flat p]
    (K : CochainComplex.Plus X.Modules) (hK : QuasiIso ((positivePlusUnit p).app K).hom) :
    IsIso ((unitOnPlus p).app K) := by
  have : IsIso (DerivedCategory.Plus.Q.map ((positivePlusUnit p).app K)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso X.Modules) _ hK
  let e := positiveValueDerivedIso p K
  have : IsIso e.hom := inferInstance
  rw [← positivePlusUnit_original_comparison p K]
  change IsIso (DerivedCategory.Plus.Q.map ((positivePlusUnit p).app K) ≫ e.hom)
  infer_instance

lemma positivePlusUnit_quasiIso_of_derivedUnit {P X : Scheme.{u}} (p : P ⟶ X) [Flat p]
    (K : CochainComplex.Plus X.Modules)
    (hK : IsIso ((derivedPositiveUnit p).app (DerivedCategory.Plus.Q.obj K))) :
    QuasiIso ((positivePlusUnit p).app K).hom := by
  have hU : IsIso ((unitOnPlus p).app K) := by
    rw [← derivedPositiveUnit_app p K]
    exact hK
  let e := positiveValueDerivedIso p K
  have : IsIso e.hom := inferInstance
  have hQ : IsIso (DerivedCategory.Plus.Q.map ((positivePlusUnit p).app K)) := by
    have h := hU
    rw [← positivePlusUnit_original_comparison p K] at h
    change IsIso (DerivedCategory.Plus.Q.map ((positivePlusUnit p).app K) ≫ e.hom) at h
    exact (isIso_comp_right_iff _ _).mp h
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules _).mp
  change IsIso (DerivedCategory.Plus.ι.map
    (DerivedCategory.Plus.Q.map ((positivePlusUnit p).app K)))
  infer_instance

/-- The original affine strict positive unit is retained literally. -/
lemma positivePlusUnit_affine (R : CommRingCat.{u}) (K : CochainComplex.Plus (Spec R).Modules) :
    (positivePlusUnit (projection R)).app K =
      (StrictPositiveRetraction.positivePlusUnit R).app K := rfl

/-- Actual affine perfect complexes have the same canonical weak unit without term-QC premises. -/
theorem positivePlusUnit_affine_quasiIso (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (hK : locallyPerfect (Spec R) K.obj) :
    QuasiIso ((positivePlusUnit (projection R)).app K).hom := by
  obtain ⟨P, ⟨eP⟩⟩ := Affine.locallyPerfect_exists_strictPerfect_representative R hK
  let A := (strictToPlus (Spec R)).obj P
  let e : DerivedCategory.Plus.Q.obj A ≅ DerivedCategory.Plus.Q.obj K :=
    DerivedCategory.Plus.ι.preimageIso eP
  have hA : QuasiIso ((positivePlusUnit (projection R)).app A).hom := by
    rw [positivePlusUnit_affine]
    obtain ⟨a, b, hab⟩ := P.property.1
    exact StrictPositiveRetraction.positivePlusUnit_quasiIso R A a b
      (fun i hi => hab i (Or.inl hi)) (fun i hi => hab i (Or.inr hi)) P.property.2
  have hD : IsIso ((derivedPositiveUnit (projection R)).app (DerivedCategory.Plus.Q.obj A)) := by
    rw [derivedPositiveUnit_app]
    exact unitOnPlus_isIso_of_quasiIso (projection R) A hA
  exact positivePlusUnit_quasiIso_of_derivedUnit (projection R) K
    ((NatTrans.isIso_app_iff_of_iso (derivedPositiveUnit (projection R)) e).mp hD)

end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
