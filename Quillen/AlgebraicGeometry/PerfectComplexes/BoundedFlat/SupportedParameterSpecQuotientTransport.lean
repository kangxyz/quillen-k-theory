/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.NaturalDiagram
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseSpecSquare
public import Quillen.KTheory.Bass.DiagramTransport
public import Quillen.KTheory.Bass.TwoChartDoubleDescent

/-!
# The supported parameter quotient on the actual integral Spec row

The actual integral Spec parameter row carries the original polynomial and Laurent
chart isomorphisms. These give the two successive quotient transports, with both
original Laurent Spec comparison maps in the representative equation. This is a
comparison of parameter domains, independent of the chosen support pair.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
universe u w
namespace Quillen.PerfectComplexes.SupportedParameterSpecQuotientTransport
local notation "R" => AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing
local notation "p" => NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus
local notation "m" => NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus
local notation "L" => AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.op

/-- Integral coefficients give the genuine affine quasi-compact parameter row. -/
def specRow : Under R ⥤ Scheme.QuasiCompactSchemes.{u}ᵒᵖ :=
  Under.forget R ⋙ Scheme.Bass.affineSchemeFunctor

/-- The original polynomial Spec isomorphism on this actual parameter row. -/
def polynomialIso : polynomialUnderFunctor R ⋙ specRow ≅
    specRow ⋙ AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.op :=
  NatIso.ofComponents (fun a => Scheme.Bass.polynomialDiagramIso.app a.right)
    (fun g => Scheme.Bass.polynomialDiagramIso.hom.naturality g.right)

/-- The original Laurent Spec isomorphism on this actual parameter row. -/
def laurentIso : laurentUnderFunctor R ⋙ specRow ≅ specRow ⋙ L :=
  NatIso.ofComponents (fun a => Scheme.Bass.laurentDiagramIso.app a.right)
    (fun g => Scheme.Bass.laurentDiagramIso.hom.naturality g.right)

/-- The positive chart keeps its original integral Spec square. -/
theorem plus_square (a : Under R) :
    specRow.map ((underToLaurent R).app a) ≫ laurentIso.hom.app a =
      polynomialIso.hom.app a ≫ (p).app (specRow.obj a) :=
  Scheme.Bass.diagramIso_plus a.right

/-- The inverse-coordinate chart keeps its original integral Spec square. -/
theorem minus_square (a : Under R) :
    specRow.map ((underToLaurentInvert R).app a) ≫ laurentIso.hom.app a =
      polynomialIso.hom.app a ≫ (m).app (specRow.obj a) :=
  Scheme.Bass.diagramIso_minus a.right

/-- One actual parameter quotient transported along the original integral Spec diagram. -/
def contractionIso (F : Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    contraction (underToLaurent R) (underToLaurentInvert R) (specRow ⋙ F) ≅
      specRow ⋙ contraction p m F :=
  contractionTransportIso p m (underToLaurent R) (underToLaurentInvert R)
    specRow polynomialIso laurentIso plus_square minus_square F

/-- The original single quotient representative retains its Laurent Spec map. -/
@[reassoc]
theorem contractionIso_π (F : Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (a : Under R) :
    (contractionπ (underToLaurent R) (underToLaurentInvert R) (specRow ⋙ F)).app a ≫
      (contractionIso F).hom.app a =
    F.map (laurentIso.hom.app a) ≫ (contractionπ p m F).app (specRow.obj a) :=
  contractionTransportIso_π p m (underToLaurent R) (underToLaurentInvert R)
    specRow polynomialIso laurentIso plus_square minus_square F a

/-- Both original Laurent Spec isomorphisms, in the actual qc parameter category. -/
def doubleLaurentIso (a : Under R) :
    specRow.obj ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)) ≅
      (L).obj ((L).obj (specRow.obj a)) :=
  laurentIso.app ((laurentUnderFunctor R).obj a) ≪≫ (L).mapIso (laurentIso.app a)

/-- Both actual parameter quotients transported along the original integral Spec diagram. -/
def doubleContractionIso (F : Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    contraction (underToLaurent R) (underToLaurentInvert R)
        (contraction (underToLaurent R) (underToLaurentInvert R) (specRow ⋙ F)) ≅
      specRow ⋙ contraction p m (contraction p m F) :=
  (contractionFunctor (underToLaurent R) (underToLaurentInvert R)).mapIso
      (contractionIso F) ≪≫ contractionIso (contraction p m F)

/-- The two original quotient projections retain both actual Laurent Spec maps. -/
@[reassoc]
theorem doubleContractionIso_π (F : Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (a : Under R) :
    doubleContractionπ (underToLaurent R) (underToLaurentInvert R) (specRow ⋙ F) a ≫
      (doubleContractionIso F).hom.app a =
    F.map (laurentIso.hom.app ((laurentUnderFunctor R).obj a) ≫
        (L).map (laurentIso.hom.app a)) ≫ doubleContractionπ p m F (specRow.obj a) := by
  simp only [doubleContractionIso, Iso.trans_hom, Functor.mapIso_hom,
    NatTrans.comp_app, doubleContractionπ, Category.assoc]
  change (contractionπ (underToLaurent R) (underToLaurentInvert R)
      (specRow ⋙ F)).app ((laurentUnderFunctor R).obj a) ≫
    (contractionπ (underToLaurent R) (underToLaurentInvert R)
      (contraction (underToLaurent R) (underToLaurentInvert R) (specRow ⋙ F))).app a ≫
      (contractionMap (underToLaurent R) (underToLaurentInvert R)
        (contractionIso F).hom).app a ≫ _ = _
  rw [contractionMap_π_assoc, ← Category.assoc, contractionIso_π]
  rw [Category.assoc, contractionIso_π]
  have hn := (contractionπ p m F).naturality (laurentIso.hom.app a)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simpa only [Functor.comp_obj, Functor.map_comp, Category.assoc] using
    congrArg (fun k => F.map (laurentIso.hom.app ((laurentUnderFunctor R).obj a)) ≫
      k ≫ (contractionπ p m (contraction p m F)).app (specRow.obj a)) hn.symm

end Quillen.PerfectComplexes.SupportedParameterSpecQuotientTransport
