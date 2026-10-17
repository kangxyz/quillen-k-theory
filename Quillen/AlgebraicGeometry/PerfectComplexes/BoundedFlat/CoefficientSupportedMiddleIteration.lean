/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedMiddleTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedKStableNaturality
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
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]
local notation "Bs" => contractionFunctor
  (NatTrans.op Scheme.Bass.pairPlus)
  (NatTrans.op Scheme.Bass.pairMinus)
local notation "Bu" => contractionFunctor (underToLaurent R) (underToLaurentInvert R)
local notation "Is" => iteratedContractionFunctor
  (NatTrans.op Scheme.Bass.pairPlus)
  (NatTrans.op Scheme.Bass.pairMinus)
local notation "Iu" => iteratedContractionFunctor (underToLaurent R) (underToLaurentInvert R)

/-- The original native pair middle row on the actual coefficient family. -/
def boundedFlatCoefficientSupportedRestrictedMiddle
    (F : Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    ShortComplex (Under R ⥤ AddCommGrpCat.{w}) :=
  (Scheme.Bass.pairBassMiddleComplex F).map
    ((Functor.whiskeringLeft (Under R) Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ
      AddCommGrpCat.{w}).obj (boundedFlatCoefficientQuasiCompactOpenPairRow f))

/-- Actual restriction and independent-variable transport commute on the whole middle row. -/
def boundedFlatCoefficientSupportedRestrictedMiddleContractionIso
    (F : Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (boundedFlatCoefficientSupportedRestrictedMiddle f F).map Bu ≅
      boundedFlatCoefficientSupportedRestrictedMiddle f ((Bs).obj F) :=
  boundedFlatCoefficientSupportedContractionShortComplexIso f
    (Scheme.Bass.pairBassMiddleComplex F) ≪≫
      (((Functor.whiskeringLeft (Under R) Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ
        AddCommGrpCat.{w}).obj
          (boundedFlatCoefficientQuasiCompactOpenPairRow f)).mapShortComplex.mapIso
          (Scheme.Bass.pairContractionBassMiddleIso F))

attribute [local irreducible] boundedFlatCoefficientSupportedRestrictedMiddle

/-- The same actual whole-row comparison iterates with the original contraction functors. -/
def boundedFlatCoefficientSupportedRestrictedMiddleIteratedIso
    (F : Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) (i : ℕ) :
    (boundedFlatCoefficientSupportedRestrictedMiddle f F).map (Iu i) ≅
      boundedFlatCoefficientSupportedRestrictedMiddle f ((Is i).obj F) :=
  match i with
  | 0 => Iso.refl _
  | i + 1 => by
      change ((boundedFlatCoefficientSupportedRestrictedMiddle f F).map (Iu i)).map Bu ≅
        boundedFlatCoefficientSupportedRestrictedMiddle f ((Bs).obj ((Is i).obj F))
      exact (Bu).mapShortComplex.mapIso
        (boundedFlatCoefficientSupportedRestrictedMiddleIteratedIso F i) ≪≫
          boundedFlatCoefficientSupportedRestrictedMiddleContractionIso f ((Is i).obj F)

/-- The original supported K-row is exactly the restricted native K-row under actual charts.
-/
def boundedFlatCoefficientSupportedKRestrictedMiddleIso (n : ℕ) :
    boundedFlatCoefficientSupportedMiddleSequence f (n : ℤ) ≅
      boundedFlatCoefficientSupportedRestrictedMiddle f
        (Bass.supportedKAddFunctor n) := by
  unfold boundedFlatCoefficientSupportedRestrictedMiddle
  exact (middleIso (polynomialUnderCoefficient R) (underToLaurent R)
    (underToLaurentInvert R) (boundedFlatCoefficientSupportedCommonCorner (R := R))
    (boundedFlatCoefficientSupportedKStableNatIso f n).symm) ≪≫
      boundedFlatCoefficientSupportedMiddleTransportIso f (Bass.supportedKAddFunctor n)

variable [CompactSpace P.left] [QuasiSeparatedSpace Q.left]

/-- Iterated native middle rows of positive K-groups are exact on the actual qcqs ambient and
compact-open family. -/
theorem boundedFlatCoefficientSupportedRestrictedMiddle_iteratedK_exact (n i : ℕ) :
    (boundedFlatCoefficientSupportedRestrictedMiddle f
      ((Is i).obj (Bass.supportedKAddFunctor (n + 1)))).Exact :=
  ShortComplex.exact_of_iso
    ((Iu i).mapShortComplex.mapIso
      (boundedFlatCoefficientSupportedKRestrictedMiddleIso f (n + 1)) ≪≫
      boundedFlatCoefficientSupportedRestrictedMiddleIteratedIso f
        (Bass.supportedKAddFunctor (n + 1)) i)
    (boundedFlatCoefficientSupportedMiddleSequence_map_exact f n (Iu i))

end Quillen.PerfectComplexes
