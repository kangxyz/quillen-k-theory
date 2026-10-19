/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeDoubleZeroSign
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationStableComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterDoubleCorrection
public import Quillen.KTheory.Bass.SchemeDoubleContractionProductTransport

/-!
# The actual second ambient negative-class correction

The genuine native two-unit sign is transported through original evaluation
and the actual fixed-factor double Laurent interchange. The original finite
negative-class comparison then makes the second ambient correction identity.
Positive Bass invertibility is used only on quasi-compact quasi-separated
schemes; all transports retain the specified original maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
open Quillen.Bass.TwoChart Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass.GeometricConeInterchange
universe u w
namespace Quillen.PerfectComplexes
open PolynomialLaurent.Relative GlobalSectionChangeIndex
local notation "p" => NatTrans.op plus
local notation "m" => NatTrans.op minus

private theorem swap_neg_of_natIso
    {F G : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}} (e : F ≅ G)
    (X : QuasiCompactSchemes.{u}ᵒᵖ) (h : doubleContractionSwap F X = -𝟙 _) :
    doubleContractionSwap G X = -𝟙 _ := by
  let e₂ := (contractionFunctor p m).mapIso ((contractionFunctor p m).mapIso e)
  have hn : e₂.hom.app X ≫ doubleContractionSwap G X =
      doubleContractionSwap F X ≫ e₂.hom.app X := doubleContractionSwap_groupMap e.hom X
  apply (cancel_epi (e₂.hom.app X)).1
  rw [hn, h]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.id_comp]
  exact (Category.comp_id _).symm

/-- The original global Model inherits the genuine fixed double-quotient sign through evaluation. -/
theorem globalModel_doubleContractionSwap_neg (X : QuasiCompactSchemes.{u}ᵒᵖ)
    [QuasiSeparatedSpace X.unop.obj] :
    doubleContractionSwap (quasiCompactStableZero (globalModel ⋙ prespectrumFunctor)) X =
      -𝟙 _ := by
  let e : CoefficientDoubleNativeUnit.quasiCompactKFunctor 0 ≅
      quasiCompactStableZero (globalModel ⋙ prespectrumFunctor) :=
    Functor.isoWhiskerLeft quasiCompactSchemesInclusion.op (globalKStableNatIso 0)
  exact swap_neg_of_natIso e X (CoefficientDoubleNativeUnit.doubleContractionSwap_KZero_eq_neg_id X)

namespace GlobalParameterCoefficient
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
  [CompactSpace P.left] [QuasiSeparatedSpace P.left]

/-- The fixed right factor is moved past both Laurent variables using the actual geometric braid. -/
theorem parameter_doubleContractionSwap_neg (X : QuasiCompactSchemes.{u}ᵒᵖ)
    [QuasiSeparatedSpace X.unop.obj] :
    doubleContractionSwap (quasiCompactStableZero (parameterDiagram P)) X = -𝟙 _ := by
  let q := toIntegerBase P.left
  have : QuasiSeparatedSpace ((qcBaseProductFunctor q).op.obj X).unop.obj :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst (toIntegerBase X.unop.obj) q)
  exact doubleContractionSwap_neg_product_app q
    (quasiCompactStableZero (globalModel ⋙ prespectrumFunctor)) X
    (globalModel_doubleContractionSwap_neg ((qcBaseProductFunctor q).op.obj X))

/-- The original second ambient class correction is identity on every integral coefficient fiber. -/
theorem negativeClassCorrection_two_hom
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (negativeClassCorrection P 2 a).hom = 𝟙 _ := by
  have : QuasiSeparatedSpace (coefficientParameterScheme a).unop.obj :=
    inferInstanceAs (QuasiSeparatedSpace (Spec a.right))
  exact negativeClassCorrection_two_hom_of_quotient_swap P a
    (parameter_doubleContractionSwap_neg P (coefficientParameterScheme a))

end GlobalParameterCoefficient
end Quillen.PerfectComplexes
