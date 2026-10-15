/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedGroups
public import Quillen.AlgebraicGeometry.PerfectComplexes.BassNegativeGroups
public import Quillen.KTheory.Bass.DiagramTransport

/-!
The original forget-support K0 map extends naturally through every actual Bass cokernel. All-degree
pair naturality and the literal Laurent representative square are preserved by the genuine geometric
chart identification.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.Bass
open AlgebraicGeometry.Scheme

/-- The original supported-to-absolute K0 homomorphism as a genuine natural transformation. -/
def supportedKZeroForget : supportedKZeroFunctor.{u} ⟶
    quasiCompactOpenPairsBase.op ⋙ perfectKZeroFunctor where
  app A := AddCommGrpCat.ofHom (perfectSupportedKMap A.unop.obj.obj.hom 0).toAdditive
  naturality {A B} f := by
    apply AddCommGrpCat.hom_ext
    exact congrArg MonoidHom.toAdditive (perfectSupportedKMap_pullback f.unop 0).symm

/-- Forgetting the open retains the exact polynomial/Laurent quotient diagram. -/
def supportedContractionForgetIso
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Quillen.Bass.TwoChart.contraction (NatTrans.op Scheme.Bass.pairPlus)
      (NatTrans.op Scheme.Bass.pairMinus) (quasiCompactOpenPairsBase.op ⋙ F) ≅
    quasiCompactOpenPairsBase.op ⋙
      Quillen.Bass.TwoChart.contraction (NatTrans.op
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) F :=
  Quillen.Bass.TwoChart.contractionTransportIso (NatTrans.op
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus)
    (NatTrans.op Scheme.Bass.pairPlus) (NatTrans.op Scheme.Bass.pairMinus)
    quasiCompactOpenPairsBase.op (Iso.refl _) (Iso.refl _)
    (by intro A; rfl)
    (by intro A; rfl) F

/-- The actual original forget-support map extends through every Bass cokernel. -/
def supportedNegativeKForgetNat : (n : ℕ) → supportedNegativeKFunctor.{u} n ⟶
    quasiCompactOpenPairsBase.op ⋙ negativeKFunctor n
  | 0 => supportedKZeroForget
  | n+1 => Quillen.Bass.TwoChart.contractionMap (NatTrans.op Scheme.Bass.pairPlus)
      (NatTrans.op Scheme.Bass.pairMinus) (supportedNegativeKForgetNat n) ≫
        (supportedContractionForgetIso (negativeKFunctor n)).hom

/-- The component of the forget-support map on the actual iterated Bass groups. -/
abbrev supportedNegativeKForget (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    supportedNegativeK A n ⟶ negativeK (quasiCompactOpenPairsBase.obj A) n :=
  (supportedNegativeKForgetNat n).app (op A)

@[simp] lemma supportedNegativeKForget_zero (A : QuasiCompactOpenPairs.{u})
    (a : PerfectSupportedK A.obj.obj.hom 0) :
    supportedNegativeKForget A 0 (Additive.ofMul a) =
      Additive.ofMul (perfectSupportedKMap A.obj.obj.hom 0 a) := rfl

/-- Arbitrary pair pullback commutes with the actual forget-support map in every degree. -/
@[reassoc] lemma supportedNegativeKForget_naturality {A B : QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (n : ℕ) :
    supportedNegativeKPullback f n ≫ supportedNegativeKForget A n =
      supportedNegativeKForget B n ≫ negativeKPullback (quasiCompactOpenPairsBase.map f) n :=
  (supportedNegativeKForgetNat n).naturality f.op

/-- The original supported Laurent representative square is retained, without a model change. -/
@[reassoc] lemma supportedNegativeKForget_π (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    supportedNegativeKπ A n ≫ supportedNegativeKForget A (n+1) =
      supportedNegativeKForget (Scheme.Bass.pairLaurentFunctor.obj A) n ≫
        negativeKπ (quasiCompactOpenPairsBase.obj A) n := by
  change (Quillen.Bass.TwoChart.contractionπ _ _ (supportedNegativeKFunctor n)).app (op A) ≫
    (Quillen.Bass.TwoChart.contractionMap _ _ (supportedNegativeKForgetNat n)).app (op A) ≫
      (supportedContractionForgetIso (negativeKFunctor n)).hom.app (op A) = _
  rw [Quillen.Bass.TwoChart.contractionMap_π_assoc]
  unfold supportedContractionForgetIso
  rw [Quillen.Bass.TwoChart.contractionTransportIso_π]
  change supportedNegativeKForget (Scheme.Bass.pairLaurentFunctor.obj A) n ≫
    (negativeKFunctor n).map (𝟙 _) ≫ negativeKπ (quasiCompactOpenPairsBase.obj A) n = _
  rw [(negativeKFunctor n).map_id,Category.id_comp]

end Quillen.PerfectComplexes.Bass

end
