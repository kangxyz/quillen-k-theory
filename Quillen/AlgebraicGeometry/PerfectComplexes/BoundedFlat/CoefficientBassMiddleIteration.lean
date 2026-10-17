/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassMiddleTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassAdditiveMiddleExactness
public import Quillen.KTheory.Bass.TwoChartIteration

/-!
# Exact original middle rows after iterated independent Bass contraction

The actual coefficient restriction and independent-variable comparisons identify iterated
contraction of the original positive K-row with the native middle row of the iterated group
functor. Exactness follows from the two already constructed natural split rows and additivity
of each iterate. No general exactness preservation by a right-exact functor is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
universe u w
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
local notation "Bs" => contractionFunctor
  (NatTrans.op Scheme.PolynomialLaurent.Relative.plus)
  (NatTrans.op Scheme.PolynomialLaurent.Relative.minus)
local notation "Bu" => contractionFunctor (underToLaurent R) (underToLaurentInvert R)
local notation "Is" => iteratedContractionFunctor
  (NatTrans.op Scheme.PolynomialLaurent.Relative.plus)
  (NatTrans.op Scheme.PolynomialLaurent.Relative.minus)
local notation "Iu" => iteratedContractionFunctor (underToLaurent R) (underToLaurentInvert R)

/-- The original native scheme middle row on the actual coefficient family. -/
def boundedFlatCoefficientRestrictedMiddle
    (F : Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    ShortComplex (Under R ⥤ AddCommGrpCat.{w}) :=
  (Scheme.PolynomialLaurent.Relative.bassMiddleComplex F).map
    ((Functor.whiskeringLeft (Under R) Scheme.QuasiCompactSchemes.{u}ᵒᵖ
      AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactRow P))

/-- Actual restriction and independent-variable transport commute on the whole middle row. -/
def boundedFlatCoefficientRestrictedMiddleContractionIso
    (F : Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (boundedFlatCoefficientRestrictedMiddle P F).map Bu ≅
      boundedFlatCoefficientRestrictedMiddle P ((Bs).obj F) :=
  boundedFlatCoefficientContractionShortComplexIso P
    (Scheme.PolynomialLaurent.Relative.bassMiddleComplex F) ≪≫
      (((Functor.whiskeringLeft (Under R) Scheme.QuasiCompactSchemes.{u}ᵒᵖ
        AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactRow P)).mapShortComplex.mapIso
          (Scheme.PolynomialLaurent.Relative.contractionBassMiddleIso F))

attribute [local irreducible] boundedFlatCoefficientRestrictedMiddle

/-- The same actual whole-row comparison iterates with the original contraction functors. -/
def boundedFlatCoefficientRestrictedMiddleIteratedIso
    (F : Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) (i : ℕ) :
    (boundedFlatCoefficientRestrictedMiddle P F).map (Iu i) ≅
      boundedFlatCoefficientRestrictedMiddle P ((Is i).obj F) :=
  match i with
  | 0 => Iso.refl _
  | i + 1 => by
      change ((boundedFlatCoefficientRestrictedMiddle P F).map (Iu i)).map Bu ≅
        boundedFlatCoefficientRestrictedMiddle P ((Bs).obj ((Is i).obj F))
      exact (Bu).mapShortComplex.mapIso
        (boundedFlatCoefficientRestrictedMiddleIteratedIso F i) ≪≫
          boundedFlatCoefficientRestrictedMiddleContractionIso P ((Is i).obj F)

/-- The original bounded-flat K-row is exactly the restricted native K-row under actual charts.
-/
def boundedFlatCoefficientKRestrictedMiddleIso (n : ℕ) :
    boundedFlatCoefficientMiddleSequence P n ≅
      boundedFlatCoefficientRestrictedMiddle P
        (Scheme.quasiCompactSchemeProperty.ι.op ⋙ boundedFlatPerfectKAddFunctor n) := by
  unfold boundedFlatCoefficientRestrictedMiddle
  exact boundedFlatCoefficientKMiddleIso P n ≪≫
    boundedFlatCoefficientMiddleTransportIso P
      (Scheme.quasiCompactSchemeProperty.ι.op ⋙ boundedFlatPerfectKAddFunctor n)

variable [QuasiSeparatedSpace P.left]

/-- All iterated native middle rows of positive K-groups are exact on the actual qcqs family. -/
theorem boundedFlatCoefficientRestrictedMiddle_iteratedK_exact (n i : ℕ) :
    (boundedFlatCoefficientRestrictedMiddle P
      ((Is i).obj (Scheme.quasiCompactSchemeProperty.ι.op ⋙
        boundedFlatPerfectKAddFunctor (n + 1)))).Exact :=
  ShortComplex.exact_of_iso
    ((Iu i).mapShortComplex.mapIso (boundedFlatCoefficientKRestrictedMiddleIso P (n + 1)) ≪≫
      boundedFlatCoefficientRestrictedMiddleIteratedIso P
        (Scheme.quasiCompactSchemeProperty.ι.op ⋙ boundedFlatPerfectKAddFunctor (n + 1)) i)
    (boundedFlatCoefficientMiddleSequence_map_exact P n (Iu i))

end Quillen.PerfectComplexes
