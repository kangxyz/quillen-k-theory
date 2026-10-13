/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.KTheory.Bass.SchemeDiagram
public import Quillen.KTheory.Bass.DiagramTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassNegativeGroups
public import Quillen.AlgebraicGeometry.PerfectComplexes.BassNegativeGroups
public import Quillen.KTheory.Bass.AffineDiagram

/-!
The genuine affine comparison for recursively defined Bass negative groups. In every degree, the
scheme group at Spec R agrees naturally with the original affine group; degree zero is the literal
original perfect K0 identity. The original Laurent quotient square includes the actual
Spec/base-product chart isomorphism. No spectral or fundamental-theorem comparison is inferred.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Quillen.Bass

/-- The degree-zero comparison is literally the unchanged original perfect K0 map. -/
def affineSchemeKZeroIso : affineKZeroFunctor.{u} ≅
    Scheme.Bass.affineSchemeFunctor ⋙ PerfectComplexes.Bass.perfectKZeroFunctor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro R S f; rfl)

/-- The genuine geometric chart comparison transports the actual next Bass cokernel. -/
def affineSchemeContractionIso
    (F : Quillen.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  :
    contraction (Scheme.Bass.affineSchemeFunctor ⋙ F) ≅
      Scheme.Bass.affineSchemeFunctor ⋙
        TwoChart.contraction (NatTrans.op Scheme.Bass.plus) (NatTrans.op Scheme.Bass.minus) F :=
  TwoChart.contractionTransportIso (NatTrans.op Scheme.Bass.plus) (NatTrans.op Scheme.Bass.minus)
    plus minus Scheme.Bass.affineSchemeFunctor Scheme.Bass.polynomialDiagramIso
    Scheme.Bass.laurentDiagramIso Scheme.Bass.diagramIso_plus Scheme.Bass.diagramIso_minus F

/-- Actual affine and scheme Bass groups agree naturally in every negative degree. -/
def affineSchemeNegativeKIso : (n : ℕ) → negativeKFunctor.{u} n ≅
    Scheme.Bass.affineSchemeFunctor ⋙ PerfectComplexes.Bass.negativeKFunctor n
  | 0 => affineSchemeKZeroIso
  | n+1 => contractionFunctor.mapIso (affineSchemeNegativeKIso n) ≪≫
      affineSchemeContractionIso (PerfectComplexes.Bass.negativeKFunctor n)

@[simp] lemma affineSchemeNegativeKIso_zero (R : CommRingCat.{u}) :
    (affineSchemeNegativeKIso 0).hom.app R = 𝟙 _ := rfl

/-- The comparison retains the original arbitrary ring-map actions on both constructions. -/
@[reassoc] lemma affineSchemeNegativeKIso_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) :
    negativeKMap f n ≫ (affineSchemeNegativeKIso n).hom.app S =
      (affineSchemeNegativeKIso n).hom.app R ≫
        (PerfectComplexes.Bass.negativeKFunctor n).map (Scheme.Bass.affineSchemeFunctor.map f) :=
  (affineSchemeNegativeKIso n).hom.naturality f

/--
Every actual Laurent representative is retained, including the genuine Spec/product isomorphism.
-/
@[reassoc] lemma affineSchemeNegativeKIso_π (R : CommRingCat.{u}) (n : ℕ) :
    negativeKπ R n ≫ (affineSchemeNegativeKIso (n+1)).hom.app R =
      (affineSchemeNegativeKIso n).hom.app (laurentFunctor.obj R) ≫
        (PerfectComplexes.Bass.negativeKFunctor n).map (Scheme.Bass.laurentDiagramIso.hom.app R) ≫
          PerfectComplexes.Bass.negativeKπ (Scheme.Bass.affineSchemeFunctor.obj R).unop n := by
  change (contractionπ (negativeKFunctor n)).app R ≫
    (contractionMap (affineSchemeNegativeKIso n).hom).app R ≫
      (affineSchemeContractionIso (PerfectComplexes.Bass.negativeKFunctor n)).hom.app R = _
  rw [contractionMap_π_assoc]
  congr 1
  exact TwoChart.contractionTransportIso_π _ _ _ _ _ _ _ _ _ _ _

/-- The inverse comparison retains every original arbitrary ring-map action as well. -/
@[reassoc] lemma affineSchemeNegativeKIso_inv_naturality {R S : CommRingCat.{u}}
    (f : R ⟶ S) (n : ℕ) :
    (PerfectComplexes.Bass.negativeKFunctor n).map (Scheme.Bass.affineSchemeFunctor.map f) ≫
      (affineSchemeNegativeKIso n).inv.app S =
        (affineSchemeNegativeKIso n).inv.app R ≫ negativeKMap f n :=
  (affineSchemeNegativeKIso n).inv.naturality f

/-- The whole representative square also determines the original inverse comparison. -/
@[reassoc] lemma affineSchemeNegativeKIso_inv_π (R : CommRingCat.{u}) (n : ℕ) :
    (affineSchemeNegativeKIso n).hom.app (laurentFunctor.obj R) ≫
      (PerfectComplexes.Bass.negativeKFunctor n).map (Scheme.Bass.laurentDiagramIso.hom.app R) ≫
        PerfectComplexes.Bass.negativeKπ (Scheme.Bass.affineSchemeFunctor.obj R).unop n ≫
          (affineSchemeNegativeKIso (n+1)).inv.app R = negativeKπ R n := by
  rw [← affineSchemeNegativeKIso_π_assoc]
  simp only [Iso.hom_inv_id_app,Category.comp_id]

end Quillen.Bass

end
