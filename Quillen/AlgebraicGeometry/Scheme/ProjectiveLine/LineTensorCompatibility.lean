/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalQuotient
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TensorSections
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.TensorLocalExactness

/-!
# The original tautological line pairs with its original quotient

The determinant defined by the actual tautological inclusion into the structure-module square
vanishes on tensoring that inclusion. Its unique descent through the original cokernel therefore
pairs the tautological line with the actual quotient line. On both original polynomial charts,
the pairing is multiplication in the specified line and quotient trivializations, with sign +1.
These chart formulas prove that the global pairing is an isomorphism over every commutative base
ring. No abstract replacement of either line or additional gluing compatibility is used.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
  SheafOfModulesOfCommRing
open CategoryTheory.MonoidalCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf

/-- The original left unitor sends each original pure-tensor generator to scalar multiplication. -/
lemma tensorLeftUnit_section (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (m : Γ(M, U)) :
    ((tensorLeftUnitIso X.sheaf).hom.app M).val.app (op U)
        (moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U r m) = r • m := by
  exact congrArg (fun f => f.app (op U) (r ⊗ₜ[Γ(X, U)] m))
    (associatedSheafUnit_tensorLeftUnitIso X.sheaf M)

variable (R : CommRingCat.{u})

/-- The global determinant formed from the original tautological inclusion and unit square. -/
def tautologicalDeterminant :
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).obj
        ((SheafOfModules.unit (twoChartLine R).ringCatSheaf : (twoChartLine R).Modules) ⨯
          SheafOfModules.unit (twoChartLine R).ringCatSheaf) ⟶
      SheafOfModules.unit (twoChartLine R).ringCatSheaf :=
  (moduleTensorCoefficientMap (twoChartLine R)
      (tautologicalLineInclusion R ≫ prod.fst)).app _ ≫
    (tensorLeftUnitIso (twoChartLine R).sheaf).hom.app _ ≫ prod.snd -
  (moduleTensorCoefficientMap (twoChartLine R)
      (tautologicalLineInclusion R ≫ prod.snd)).app _ ≫
    (tensorLeftUnitIso (twoChartLine R).sheaf).hom.app _ ≫ prod.fst

/-- The determinant retains its literal two-coordinate formula on tensor generators. -/
lemma tautologicalDeterminant_section (U : (twoChartLine R).Opens)
    (a : Γ(tautologicalLine R, U))
    (b : Γ((SheafOfModules.unit (twoChartLine R).ringCatSheaf :
      (twoChartLine R).Modules) ⨯ SheafOfModules.unit (twoChartLine R).ringCatSheaf, U)) :
    (tautologicalDeterminant R).app U (moduleTensorSection (twoChartLine R)
        (tautologicalLine R) _ U a b) =
      (show Γ(twoChartLine R, U) from (tautologicalLineInclusion R ≫ prod.fst).app U a) *
        (show Γ(twoChartLine R, U) from Scheme.Modules.Hom.app (prod.snd : (_ ⨯ _) ⟶
          SheafOfModules.unit (twoChartLine R).ringCatSheaf) U b) -
      (show Γ(twoChartLine R, U) from (tautologicalLineInclusion R ≫ prod.snd).app U a) *
        (show Γ(twoChartLine R, U) from Scheme.Modules.Hom.app (prod.fst : (_ ⨯ _) ⟶
          SheafOfModules.unit (twoChartLine R).ringCatSheaf) U b) := by
  let X := twoChartLine R
  let S : X.Modules := (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
    SheafOfModules.unit X.ringCatSheaf
  let c₁ : tautologicalLine R ⟶ SheafOfModules.unit X.ringCatSheaf :=
    tautologicalLineInclusion R ≫ prod.fst
  let c₂ : tautologicalLine R ⟶ SheafOfModules.unit X.ringCatSheaf :=
    tautologicalLineInclusion R ≫ prod.snd
  have h₁ := moduleTensorCoefficientMap_section c₁ S U a b
  have h₂ := moduleTensorCoefficientMap_section c₂ S U a b
  change Scheme.Modules.Hom.app (prod.snd : S ⟶ _) U
      (((tensorLeftUnitIso X.sheaf).hom.app S).val.app (op U)
        (((moduleTensorCoefficientMap X c₁).app S).app U
          (moduleTensorSection X (tautologicalLine R) S U a b))) -
    Scheme.Modules.Hom.app (prod.fst : S ⟶ _) U
      (((tensorLeftUnitIso X.sheaf).hom.app S).val.app (op U)
        (((moduleTensorCoefficientMap X c₂).app S).app U
          (moduleTensorSection X (tautologicalLine R) S U a b))) = _
  rw [h₁, h₂]
  erw [tensorLeftUnit_section X S U (c₁.app U a) b,
    tensorLeftUnit_section X S U (c₂.app U a) b]
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
  rfl

/-- The first original positive coordinate is the given positive trivialization. -/
lemma tautologicalPairingFirstCoordinate_plus :
    (Scheme.Modules.restrictFunctor (plusChart R)).map
        (tautologicalLineInclusion R ≫ prod.fst) ≫
      (Scheme.Modules.restrictUnitIso (plusChart R)).hom =
        (tautologicalLinePlusIso R).hom := by
  have h := congrArg (fun f => (tautologicalLinePlusIso R).hom ≫ f ≫
    (Scheme.Modules.restrictUnitIso (plusChart R)).hom)
      (firstColumn_fst (plusChart R) (polynomialCoordinate R))
  rw [Functor.map_comp, tautologicalLineInclusion_plus]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- The second original positive coordinate is multiplication by the positive chart coordinate. -/
lemma tautologicalSecondCoordinate_plus :
    (Scheme.Modules.restrictFunctor (plusChart R)).map
        (tautologicalLineInclusion R ≫ prod.snd) ≫
      (Scheme.Modules.restrictUnitIso (plusChart R)).hom =
        (tautologicalLinePlusIso R).hom ≫
          unitMul (Spec (.of (Polynomial R))) (polynomialCoordinate R) := by
  have h := congrArg (fun f => (tautologicalLinePlusIso R).hom ≫ f ≫
    (Scheme.Modules.restrictUnitIso (plusChart R)).hom)
      (firstColumn_snd (plusChart R) (polynomialCoordinate R))
  rw [Functor.map_comp, tautologicalLineInclusion_plus]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- The first original negative coordinate is multiplication by the negative chart coordinate. -/
lemma tautologicalPairingFirstCoordinate_minus :
    (Scheme.Modules.restrictFunctor (minusChart R)).map
        (tautologicalLineInclusion R ≫ prod.fst) ≫
      (Scheme.Modules.restrictUnitIso (minusChart R)).hom =
        (tautologicalLineMinusIso R).hom ≫
          unitMul (Spec (.of (Polynomial R))) (polynomialCoordinate R) := by
  have h := congrArg (fun f => (tautologicalLineMinusIso R).hom ≫ f ≫
    (Scheme.Modules.restrictUnitIso (minusChart R)).hom)
      (secondColumn_fst (minusChart R) (polynomialCoordinate R))
  rw [Functor.map_comp, tautologicalLineInclusion_minus]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- The second original negative coordinate is the given negative trivialization. -/
lemma tautologicalPairingSecondCoordinate_minus :
    (Scheme.Modules.restrictFunctor (minusChart R)).map
        (tautologicalLineInclusion R ≫ prod.snd) ≫
      (Scheme.Modules.restrictUnitIso (minusChart R)).hom =
        (tautologicalLineMinusIso R).hom := by
  have h := congrArg (fun f => (tautologicalLineMinusIso R).hom ≫ f ≫
    (Scheme.Modules.restrictUnitIso (minusChart R)).hom)
      (secondColumn_snd (minusChart R) (polynomialCoordinate R))
  rw [Functor.map_comp, tautologicalLineInclusion_minus]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

lemma tautologicalDeterminant_self_section (U : (twoChartLine R).Opens)
    (a b : Γ(tautologicalLine R, U)) :
    ((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
        (tautologicalLineInclusion R) ≫ tautologicalDeterminant R).app U
      (moduleTensorSection (twoChartLine R) (tautologicalLine R) (tautologicalLine R) U a b) =
      (show Γ(twoChartLine R, U) from (tautologicalLineInclusion R ≫ prod.fst).app U a) *
        (show Γ(twoChartLine R, U) from (tautologicalLineInclusion R ≫ prod.snd).app U b) -
      (show Γ(twoChartLine R, U) from (tautologicalLineInclusion R ≫ prod.snd).app U a) *
        (show Γ(twoChartLine R, U) from (tautologicalLineInclusion R ≫ prod.fst).app U b) := by
  change (tautologicalDeterminant R).app U
    (((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
      (tautologicalLineInclusion R)).app U
        (moduleTensorSection (twoChartLine R) (tautologicalLine R) (tautologicalLine R) U a b)) = _
  rw [moduleTensorLeftFunctor_map_section (tautologicalLine R)
    (tautologicalLineInclusion R) U a b, tautologicalDeterminant_section]
  rfl

lemma tautologicalDeterminant_self_plus :
    (Scheme.Modules.restrictFunctor (plusChart R)).map
      ((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
        (tautologicalLineInclusion R) ≫ tautologicalDeterminant R) = 0 := by
  apply (cancel_epi (tensorRestrictionIso (plusChart R)
    (tautologicalLine R) (tautologicalLine R)).hom).mp
  apply (cancel_mono (Scheme.Modules.restrictUnitIso (plusChart R)).hom).mp
  rw [comp_zero, zero_comp]
  apply moduleTensor_hom_ext
  intro U a b
  have h₁ (c : Γ((tautologicalLine R).restrict (plusChart R), U)) :
      ((plusChart R).appIso U).hom.hom
        ((tautologicalLineInclusion R ≫ prod.fst).app ((plusChart R) ''ᵁ U) c) =
          (tautologicalLinePlusIso R).hom.val.app (op U) c :=
    congrArg (fun f => f.val.app (op U) c) (tautologicalPairingFirstCoordinate_plus R)
  have h₂ (c : Γ((tautologicalLine R).restrict (plusChart R), U)) :
      ((plusChart R).appIso U).hom.hom
        ((tautologicalLineInclusion R ≫ prod.snd).app ((plusChart R) ''ᵁ U) c) =
          (show Γ(Spec (.of (Polynomial R)), U) from
            (tautologicalLinePlusIso R).hom.val.app (op U) c) *
            ((Spec (.of (Polynomial R))).presheaf.map (homOfLE le_top).op).hom
              (polynomialCoordinate R) :=
    congrArg (fun f => f.val.app (op U) c) (tautologicalSecondCoordinate_plus R)
  change ((plusChart R).appIso U).hom.hom
    (((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
      (tautologicalLineInclusion R) ≫ tautologicalDeterminant R).app ((plusChart R) ''ᵁ U)
        ((tensorRestrictionIso (plusChart R) (tautologicalLine R) (tautologicalLine R)).hom.app U
          (moduleTensorSection _ _ _ U a b))) = 0
  rw [tensorRestrictionIso_section, tautologicalDeterminant_self_section,
    map_sub, map_mul, map_mul]
  rw [h₁ a, h₁ b, h₂ a, h₂ b]
  ring

lemma tautologicalDeterminant_self_minus :
    (Scheme.Modules.restrictFunctor (minusChart R)).map
      ((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
        (tautologicalLineInclusion R) ≫ tautologicalDeterminant R) = 0 := by
  apply (cancel_epi (tensorRestrictionIso (minusChart R)
    (tautologicalLine R) (tautologicalLine R)).hom).mp
  apply (cancel_mono (Scheme.Modules.restrictUnitIso (minusChart R)).hom).mp
  rw [comp_zero, zero_comp]
  apply moduleTensor_hom_ext
  intro U a b
  have h₁ (c : Γ((tautologicalLine R).restrict (minusChart R), U)) :
      ((minusChart R).appIso U).hom.hom
        ((tautologicalLineInclusion R ≫ prod.snd).app ((minusChart R) ''ᵁ U) c) =
          (tautologicalLineMinusIso R).hom.val.app (op U) c :=
    congrArg (fun f => f.val.app (op U) c) (tautologicalPairingSecondCoordinate_minus R)
  have h₂ (c : Γ((tautologicalLine R).restrict (minusChart R), U)) :
      ((minusChart R).appIso U).hom.hom
        ((tautologicalLineInclusion R ≫ prod.fst).app ((minusChart R) ''ᵁ U) c) =
          (show Γ(Spec (.of (Polynomial R)), U) from
            (tautologicalLineMinusIso R).hom.val.app (op U) c) *
            ((Spec (.of (Polynomial R))).presheaf.map (homOfLE le_top).op).hom
              (polynomialCoordinate R) :=
    congrArg (fun f => f.val.app (op U) c) (tautologicalPairingFirstCoordinate_minus R)
  change ((minusChart R).appIso U).hom.hom
    (((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
      (tautologicalLineInclusion R) ≫ tautologicalDeterminant R).app ((minusChart R) ''ᵁ U)
        ((tensorRestrictionIso (minusChart R) (tautologicalLine R) (tautologicalLine R)).hom.app U
          (moduleTensorSection _ _ _ U a b))) = 0
  rw [tensorRestrictionIso_section, tautologicalDeterminant_self_section,
    map_sub, map_mul, map_mul]
  rw [h₁ a, h₁ b, h₂ a, h₂ b]
  ring

private lemma eq_zero_of_chart_restrictions {M N : (twoChartLine R).Modules} (f : M ⟶ N)
    (hp : (Scheme.Modules.restrictFunctor (plusChart R)).map f = 0)
    (hm : (Scheme.Modules.restrictFunctor (minusChart R)).map f = 0) : f = 0 := by
  have hk {Y : Scheme.{u}} (j : Y ⟶ twoChartLine R) [IsOpenImmersion j]
      (h : (Scheme.Modules.restrictFunctor j).map f = 0) :
      IsIso ((Scheme.Modules.restrictFunctor j).map (kernel.ι f)) := by
    have hi : IsIso (kernel.ι ((Scheme.Modules.restrictFunctor j).map f)) := by
      exact kernel.ι_of_zero h
    have : IsIso ((PreservesKernel.iso (Scheme.Modules.restrictFunctor j) f).inv ≫
        (Scheme.Modules.restrictFunctor j).map (kernel.ι f)) := by
      rw [PreservesKernel.iso_inv_ι]
      exact hi
    exact IsIso.of_isIso_comp_left (PreservesKernel.iso
      (Scheme.Modules.restrictFunctor j) f).inv _
  have : IsIso (kernel.ι f) := isIso_of_restrict_openCover
    (fun _ : Bool => Spec (.of (Polynomial R))) (polynomialChart R) (polynomialChart_cover R)
    (kernel.ι f) (fun b => by
      cases b
      · exact hk (minusChart R) hm
      · exact hk (plusChart R) hp)
  exact (cancel_epi (kernel.ι f)).mp (by simp)

/-- The global determinant vanishes on the actual tensor image of the tautological inclusion. -/
lemma tautologicalDeterminant_self :
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
      (tautologicalLineInclusion R) ≫ tautologicalDeterminant R = 0 :=
  eq_zero_of_chart_restrictions R _
    (tautologicalDeterminant_self_plus R) (tautologicalDeterminant_self_minus R)

/-- Exact tensor with the original line retains the actual quotient as a cokernel. -/
def tautologicalTensorCokernel :
    IsColimit (CokernelCofork.ofπ
      ((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
        (tautologicalQuotientMap R))
      (show (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
          (tautologicalLineInclusion R) ≫
          (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
            (tautologicalQuotientMap R) = 0 from
        ((tautologicalSequence R).map
          (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R))).zero)) := by
  let S := (tautologicalSequence R).map
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R))
  have hS : S.ShortExact := tensor_shortExact_finiteLocallyFree (tautologicalLine R)
    (tautologicalSequence R) (tautologicalSequence_shortExact R)
  let := hS.epi_g
  exact hS.exact.gIsCokernel

/-- The unique determinant pairing descended through the original tautological quotient. -/
def tautologicalLinePairing :
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).obj
      (tautologicalQuotientLine R) ⟶ SheafOfModules.unit (twoChartLine R).ringCatSheaf :=
  (tautologicalTensorCokernel R).desc
    (CokernelCofork.ofπ (tautologicalDeterminant R) (tautologicalDeterminant_self R))

/-- The descended pairing retains the literal original quotient map and global determinant. -/
lemma tautologicalLinePairing_quotient :
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).map
        (tautologicalQuotientMap R) ≫ tautologicalLinePairing R = tautologicalDeterminant R :=
  Cofork.IsColimit.π_desc (t := CokernelCofork.ofπ
    (tautologicalDeterminant R) (tautologicalDeterminant_self R)) (tautologicalTensorCokernel R)

/-- Two specified unit trivializations give the original tensor multiplication chart isomorphism. -/
def tensorPairingTrivialization {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M N : X.Modules) (eM : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (eN : N.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) :
    ((moduleTensorLeftFunctor X M).obj N).restrict j ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (tensorRestrictionIso j M N).symm ≪≫
    ((tensorFunctor Y.sheaf).mapIso eM).app (N.restrict j) ≪≫
    (tensorLeftUnitIso Y.sheaf).app (N.restrict j) ≪≫ eN

/-- Multiplication in the original positive line and quotient trivializations. -/
def tautologicalLinePairingPlusIso :
    ((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).obj
      (tautologicalQuotientLine R)).restrict (plusChart R) ≅
        SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf :=
  tensorPairingTrivialization (plusChart R) (tautologicalLine R) (tautologicalQuotientLine R)
    (tautologicalLinePlusIso R) (tautologicalQuotientPlusIso R)

/-- Multiplication in the original negative line and quotient trivializations. -/
def tautologicalLinePairingMinusIso :
    ((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).obj
      (tautologicalQuotientLine R)).restrict (minusChart R) ≅
        SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf :=
  tensorPairingTrivialization (minusChart R) (tautologicalLine R) (tautologicalQuotientLine R)
    (tautologicalLineMinusIso R) (tautologicalQuotientMinusIso R)

private lemma tensorPairingTrivialization_section {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (M N : X.Modules)
    (eM : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (eN : N.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (U : Y.Opens) (m : Γ(M.restrict j, U)) (n : Γ(N.restrict j, U)) :
    ((tensorRestrictionIso j M N).hom ≫
      (tensorPairingTrivialization j M N eM eN).hom).val.app (op U)
        (moduleTensorSection Y (M.restrict j) (N.restrict j) U m n) =
      (show Γ(Y, U) from eM.hom.val.app (op U) m) *
        (show Γ(Y, U) from eN.hom.val.app (op U) n) := by
  have h : (tensorRestrictionIso j M N).hom ≫
      (tensorPairingTrivialization j M N eM eN).hom =
        (moduleTensorCoefficientMap Y eM.hom).app (N.restrict j) ≫
          (tensorLeftUnitIso Y.sheaf).hom.app (N.restrict j) ≫ eN.hom := by
    simp only [tensorPairingTrivialization, Iso.trans_hom, Iso.symm_hom,
      Iso.hom_inv_id_assoc, Iso.app_hom, Functor.mapIso_hom]
    rfl
  rw [h]
  change eN.hom.val.app (op U)
    (((tensorLeftUnitIso Y.sheaf).hom.app (N.restrict j)).val.app (op U)
      (((moduleTensorCoefficientMap Y eM.hom).app (N.restrict j)).app U
        (moduleTensorSection Y (M.restrict j) (N.restrict j) U m n))) = _
  rw [moduleTensorCoefficientMap_section eM.hom (N.restrict j) U m n]
  erw [tensorLeftUnit_section Y (N.restrict j) U (eM.hom.val.app (op U) m) n]
  rw [map_smul]
  rfl

/-- The global pairing has sign +1 in the two original positive-chart trivializations. -/
lemma tautologicalLinePairing_plus :
    (Scheme.Modules.restrictFunctor (plusChart R)).map (tautologicalLinePairing R) ≫
      (Scheme.Modules.restrictUnitIso (plusChart R)).hom =
        (tautologicalLinePairingPlusIso R).hom := by
  let X := twoChartLine R
  let Y := Spec (.of (Polynomial R))
  let S : X.Modules := (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
    SheafOfModules.unit X.ringCatSheaf
  let j := plusChart R
  let T := moduleTensorLeftFunctor X (tautologicalLine R)
  let F := Scheme.Modules.restrictFunctor j
  let : Epi (T.map (tautologicalQuotientMap R)) :=
    (tensor_shortExact_finiteLocallyFree (tautologicalLine R)
      (tautologicalSequence R) (tautologicalSequence_shortExact R)).epi_g
  apply (cancel_epi (F.map (T.map (tautologicalQuotientMap R)))).mp
  change (F.map (T.map (tautologicalQuotientMap R)) ≫ F.map (tautologicalLinePairing R)) ≫
    (Scheme.Modules.restrictUnitIso j).hom = _
  rw [← Functor.map_comp, tautologicalLinePairing_quotient]
  apply (cancel_epi (tensorRestrictionIso j (tautologicalLine R) S).hom).mp
  have hn := (tensorRestrictionNatIso j (tautologicalLine R)).hom.naturality
    (tautologicalQuotientMap R)
  change (moduleTensorLeftFunctor Y ((tautologicalLine R).restrict j)).map
      (F.map (tautologicalQuotientMap R)) ≫
        (tensorRestrictionIso j (tautologicalLine R) (tautologicalQuotientLine R)).hom =
    (tensorRestrictionIso j (tautologicalLine R) S).hom ≫
      F.map (T.map (tautologicalQuotientMap R)) at hn
  rw [← reassoc_of% hn]
  apply moduleTensor_hom_ext
  intro U a b
  have h₁ : (j.appIso U).hom.hom
      ((tautologicalLineInclusion R ≫ prod.fst).app (j ''ᵁ U) a) =
        (tautologicalLinePlusIso R).hom.val.app (op U) a :=
    congrArg (fun f => f.val.app (op U) a) (tautologicalPairingFirstCoordinate_plus R)
  have h₂ : (j.appIso U).hom.hom
      ((tautologicalLineInclusion R ≫ prod.snd).app (j ''ᵁ U) a) =
        (show Γ(Y, U) from (tautologicalLinePlusIso R).hom.val.app (op U) a) *
          (Y.presheaf.map (homOfLE le_top).op).hom (polynomialCoordinate R) :=
    congrArg (fun f => f.val.app (op U) a) (tautologicalSecondCoordinate_plus R)
  have hq := congrArg (fun f => f.val.app (op U) b) (tautologicalQuotientMap_plus R)
  rw [firstRow_eq j (polynomialCoordinate R)] at hq
  change (tautologicalQuotientPlusIso R).hom.val.app (op U)
      ((F.map (tautologicalQuotientMap R)).app U b) =
    (j.appIso U).hom.hom (Scheme.Modules.Hom.app (prod.snd : S ⟶ _) (j ''ᵁ U) b) -
      (j.appIso U).hom.hom (Scheme.Modules.Hom.app (prod.fst : S ⟶ _) (j ''ᵁ U) b) *
        (Y.presheaf.map (homOfLE le_top).op).hom (polynomialCoordinate R) at hq
  change (j.appIso U).hom.hom ((tautologicalDeterminant R).app (j ''ᵁ U)
      ((tensorRestrictionIso j (tautologicalLine R) S).hom.app U
        (moduleTensorSection Y ((tautologicalLine R).restrict j) (S.restrict j) U a b))) =
    ((tensorRestrictionIso j (tautologicalLine R) (tautologicalQuotientLine R)).hom ≫
      (tensorPairingTrivialization j (tautologicalLine R) (tautologicalQuotientLine R)
        (tautologicalLinePlusIso R) (tautologicalQuotientPlusIso R)).hom).val.app (op U)
      (((moduleTensorLeftFunctor Y ((tautologicalLine R).restrict j)).map
        (F.map (tautologicalQuotientMap R))).app U
          (moduleTensorSection Y ((tautologicalLine R).restrict j) (S.restrict j) U a b))
  rw [tensorRestrictionIso_section, tautologicalDeterminant_section, map_sub, map_mul, map_mul]
  rw [moduleTensorLeftFunctor_map_section ((tautologicalLine R).restrict j)
    (F.map (tautologicalQuotientMap R)) U a b]
  rw [tensorPairingTrivialization_section j (tautologicalLine R) (tautologicalQuotientLine R)
    (tautologicalLinePlusIso R) (tautologicalQuotientPlusIso R) U a]
  rw [h₁, h₂, hq]
  ring

/-- The global pairing has sign +1 in the two original negative-chart trivializations. -/
lemma tautologicalLinePairing_minus :
    (Scheme.Modules.restrictFunctor (minusChart R)).map (tautologicalLinePairing R) ≫
      (Scheme.Modules.restrictUnitIso (minusChart R)).hom =
        (tautologicalLinePairingMinusIso R).hom := by
  let X := twoChartLine R
  let Y := Spec (.of (Polynomial R))
  let S : X.Modules := (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
    SheafOfModules.unit X.ringCatSheaf
  let j := minusChart R
  let T := moduleTensorLeftFunctor X (tautologicalLine R)
  let F := Scheme.Modules.restrictFunctor j
  let : Epi (T.map (tautologicalQuotientMap R)) :=
    (tensor_shortExact_finiteLocallyFree (tautologicalLine R)
      (tautologicalSequence R) (tautologicalSequence_shortExact R)).epi_g
  apply (cancel_epi (F.map (T.map (tautologicalQuotientMap R)))).mp
  change (F.map (T.map (tautologicalQuotientMap R)) ≫ F.map (tautologicalLinePairing R)) ≫
    (Scheme.Modules.restrictUnitIso j).hom = _
  rw [← Functor.map_comp, tautologicalLinePairing_quotient]
  apply (cancel_epi (tensorRestrictionIso j (tautologicalLine R) S).hom).mp
  have hn := (tensorRestrictionNatIso j (tautologicalLine R)).hom.naturality
    (tautologicalQuotientMap R)
  change (moduleTensorLeftFunctor Y ((tautologicalLine R).restrict j)).map
      (F.map (tautologicalQuotientMap R)) ≫
        (tensorRestrictionIso j (tautologicalLine R) (tautologicalQuotientLine R)).hom =
    (tensorRestrictionIso j (tautologicalLine R) S).hom ≫
      F.map (T.map (tautologicalQuotientMap R)) at hn
  rw [← reassoc_of% hn]
  apply moduleTensor_hom_ext
  intro U a b
  have h₁ : (j.appIso U).hom.hom
      ((tautologicalLineInclusion R ≫ prod.snd).app (j ''ᵁ U) a) =
        (tautologicalLineMinusIso R).hom.val.app (op U) a :=
    congrArg (fun f => f.val.app (op U) a) (tautologicalPairingSecondCoordinate_minus R)
  have h₂ : (j.appIso U).hom.hom
      ((tautologicalLineInclusion R ≫ prod.fst).app (j ''ᵁ U) a) =
        (show Γ(Y, U) from (tautologicalLineMinusIso R).hom.val.app (op U) a) *
          (Y.presheaf.map (homOfLE le_top).op).hom (polynomialCoordinate R) :=
    congrArg (fun f => f.val.app (op U) a) (tautologicalPairingFirstCoordinate_minus R)
  have hq := congrArg (fun f => f.val.app (op U) b) (tautologicalQuotientMap_minus R)
  rw [secondRow_eq j (polynomialCoordinate R)] at hq
  change (tautologicalQuotientMinusIso R).hom.val.app (op U)
      ((F.map (tautologicalQuotientMap R)).app U b) =
    (j.appIso U).hom.hom (Scheme.Modules.Hom.app (prod.snd : S ⟶ _) (j ''ᵁ U) b) *
      (Y.presheaf.map (homOfLE le_top).op).hom (polynomialCoordinate R) -
        (j.appIso U).hom.hom (Scheme.Modules.Hom.app (prod.fst : S ⟶ _) (j ''ᵁ U) b) at hq
  change (j.appIso U).hom.hom ((tautologicalDeterminant R).app (j ''ᵁ U)
      ((tensorRestrictionIso j (tautologicalLine R) S).hom.app U
        (moduleTensorSection Y ((tautologicalLine R).restrict j) (S.restrict j) U a b))) =
    ((tensorRestrictionIso j (tautologicalLine R) (tautologicalQuotientLine R)).hom ≫
      (tensorPairingTrivialization j (tautologicalLine R) (tautologicalQuotientLine R)
        (tautologicalLineMinusIso R) (tautologicalQuotientMinusIso R)).hom).val.app (op U)
      (((moduleTensorLeftFunctor Y ((tautologicalLine R).restrict j)).map
        (F.map (tautologicalQuotientMap R))).app U
          (moduleTensorSection Y ((tautologicalLine R).restrict j) (S.restrict j) U a b))
  rw [tensorRestrictionIso_section, tautologicalDeterminant_section, map_sub, map_mul, map_mul]
  rw [moduleTensorLeftFunctor_map_section ((tautologicalLine R).restrict j)
    (F.map (tautologicalQuotientMap R)) U a b]
  rw [tensorPairingTrivialization_section j (tautologicalLine R) (tautologicalQuotientLine R)
    (tautologicalLineMinusIso R) (tautologicalQuotientMinusIso R) U a]
  rw [h₁, h₂, hq]
  ring


/-- The actual global determinant pairing is invertible, detected on its original charts. -/
instance tautologicalLinePairing_isIso : IsIso (tautologicalLinePairing R) := by
  apply isIso_of_restrict_openCover (fun _ : Bool => Spec (.of (Polynomial R)))
    (polynomialChart R) (polynomialChart_cover R)
  intro b
  cases b
  · change IsIso ((Scheme.Modules.restrictFunctor (minusChart R)).map _)
    have : IsIso ((Scheme.Modules.restrictFunctor (minusChart R)).map
        (tautologicalLinePairing R) ≫ (Scheme.Modules.restrictUnitIso (minusChart R)).hom) := by
      rw [tautologicalLinePairing_minus]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Scheme.Modules.restrictUnitIso (minusChart R)).hom
  · change IsIso ((Scheme.Modules.restrictFunctor (plusChart R)).map _)
    have : IsIso ((Scheme.Modules.restrictFunctor (plusChart R)).map
        (tautologicalLinePairing R) ≫ (Scheme.Modules.restrictUnitIso (plusChart R)).hom) := by
      rw [tautologicalLinePairing_plus]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Scheme.Modules.restrictUnitIso (plusChart R)).hom

/-- The actual original tautological subline and quotient line pair to the structure module. -/
def tautologicalLineTensorQuotientIso :
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).obj
      (tautologicalQuotientLine R) ≅ SheafOfModules.unit (twoChartLine R).ringCatSheaf :=
  asIso (tautologicalLinePairing R)

lemma tautologicalLineTensorQuotientIso_hom :
    (tautologicalLineTensorQuotientIso R).hom = tautologicalLinePairing R := rfl

end Quillen.Scheme.ProjectiveLine
