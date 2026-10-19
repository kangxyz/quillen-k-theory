/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialLaurentTransport
public import Quillen.KTheory.Bass.TwoChartDoubleDescent

/-!
# The actual double coefficient Bass quotient transport

The original coefficient/product diagram isomorphisms induce an isomorphism
of the two successive Bass quotients. Its representative square retains both
actual Laurent comparison maps and both original quotient projections.
The coefficient and quasi-compact-scheme domains remain distinct.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
universe u w
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
local notation "p" => NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus
local notation "m" => NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus
local notation "L" => AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.op

/-- Transport of both original quotients through the two genuine diagram isomorphisms. -/
def boundedFlatCoefficientDoubleContractionTransportIso
    (F : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    contraction (underToLaurent R) (underToLaurentInvert R)
        (contraction (underToLaurent R) (underToLaurentInvert R)
          (boundedFlatCoefficientQuasiCompactRow P ⋙ F)) ≅
      boundedFlatCoefficientQuasiCompactRow P ⋙ contraction p m (contraction p m F) :=
  (contractionFunctor (underToLaurent R) (underToLaurentInvert R)).mapIso
      (boundedFlatCoefficientContractionTransportIso P F) ≪≫
    boundedFlatCoefficientContractionTransportIso P (contraction p m F)

/-- Both quotient projections transport through both specified Laurent comparison maps. -/
@[reassoc]
theorem boundedFlatCoefficientDoubleContractionTransportIso_π
    (F : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (a : Under R) :
    doubleContractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientQuasiCompactRow P ⋙ F) a ≫
      (boundedFlatCoefficientDoubleContractionTransportIso P F).hom.app a =
    F.map ((boundedFlatCoefficientLaurentIso P).hom.app ((laurentUnderFunctor R).obj a) ≫
        (L).map ((boundedFlatCoefficientLaurentIso P).hom.app a)) ≫
      doubleContractionπ p m F ((boundedFlatCoefficientQuasiCompactRow P).obj a) := by
  simp only [boundedFlatCoefficientDoubleContractionTransportIso, Iso.trans_hom,
    Functor.mapIso_hom, NatTrans.comp_app, doubleContractionπ, Category.assoc]
  change (contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientQuasiCompactRow P ⋙ F)).app ((laurentUnderFunctor R).obj a) ≫
    (contractionπ (underToLaurent R) (underToLaurentInvert R)
      (contraction (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientQuasiCompactRow P ⋙ F))).app a ≫
      (contractionMap (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientContractionTransportIso P F).hom).app a ≫ _ = _
  rw [contractionMap_π_assoc, ← Category.assoc,
    boundedFlatCoefficientContractionTransportIso_π]
  rw [Category.assoc, boundedFlatCoefficientContractionTransportIso_π]
  have hn := (contractionπ p m F).naturality
    ((boundedFlatCoefficientLaurentIso P).hom.app a)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simpa only [Functor.comp_obj, Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦
      F.map ((boundedFlatCoefficientLaurentIso P).hom.app ((laurentUnderFunctor R).obj a)) ≫
        k ≫ (contractionπ p m (contraction p m F)).app
          ((boundedFlatCoefficientQuasiCompactRow P).obj a)) hn.symm

end Quillen.PerfectComplexes
