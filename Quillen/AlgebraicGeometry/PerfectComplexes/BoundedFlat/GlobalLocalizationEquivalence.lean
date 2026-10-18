/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRow
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalOpenModels
public import Quillen.Waldhausen.Fibration.InverseImageWeakEquivalence
public import Quillen.KTheory.Bass.ModelDiagramStableEquivalence

/-!
# Exact inverse comparisons for the actual global localization rows

Supported restriction has an exact categorical inverse because its complete original evaluation
square commutes. Coarse restriction uses the same original ambient inverse, whose counit proves
preservation of the actual inverse-image weak class. Every finite Bass iterate of these actual
row restrictions is a stable equivalence, with no coarse or supported equivalence premise.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
open Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] globalModel boundedFlatCoefficientSectionWaldhausen
  boundedFlatCoefficientOriginalEvaluation

private theorem exactIntoEvaluation
    {A B C : Type*} [Category A] [Category B] [Category C]
    (WA : Structure A) (WC : Structure C) (e : B ≌ C) (z : B)
    (hz : IsZero (e.functor.obj z)) (F : A ⥤ B)
    (h : IsExact WA.cof WA.weq WC.cof WC.weq (F ⋙ e.functor)) :
    IsExact WA.cof WA.weq (WC.ofEquivalence e z hz).cof
      (WC.ofEquivalence e z hz).weq F where
  zero hx := IsZero.of_full_of_faithful_of_isZero e.functor _ (h.zero hx)
  cofibration g hg := h.cofibration g hg
  weak g hg := h.weak g hg
  pushout hi hp := IsPushout.of_map_of_faithful e.functor (h.pushout hi hp)

/-- The actual supported restriction inverse is exact for the original transported classes. -/
theorem supportedRestriction_inverse_exact (R : CommRingCat.{u}) (c : Index R)
    {U : Scheme.{u}} (j : U ⟶ space c) [IsOpenImmersion j] :
    IsExact (boundedFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen j).weq
      (supportedWaldhausen (X :=
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j).cof
      (supportedWaldhausen (X :=
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j).weq
      (supportedRestriction R c j).asEquivalence.inverse := by
  let e := (supportedRestriction R c j).asEquivalence
  have hi : e.inverse ⋙ supportedEvaluation
      (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j ≅
      boundedFlatCoefficientSupportedEvaluation j :=
    Functor.isoWhiskerLeft e.inverse (eqToIso (supportedRestriction_evaluation R c j).symm) ≪≫
      e.invFunIdAssoc (boundedFlatCoefficientSupportedEvaluation j)
  apply exactIntoEvaluation _ _ (supportedEvaluation
    (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j).asEquivalence
  exact ExtensionCategory.isExact_of_natIso _ _
    (boundedFlatCoefficientSupportedEvaluation_exact j) hi.symm

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- Each actual supported row component has its unchanged exact categorical inverse. -/
theorem supportedRowRestriction_inverse_exact (a : Under R) :
    IsExact ((boundedFlatCoefficientSupportedModelFunctor f).obj a).waldhausen.cof
      ((boundedFlatCoefficientSupportedModelFunctor f).obj a).waldhausen.weq
      ((supportedRow f).obj a).waldhausen.cof ((supportedRow f).obj a).waldhausen.weq
      (supportedRestriction R (op Q, a) (schemeMap f a)).asEquivalence.inverse :=
  supportedRestriction_inverse_exact R (op Q, a) (schemeMap f a)

/-- Every finite iterate retains the actual supported restriction and is stable. -/
theorem supportedRowRestriction_iterate_isStableEquivalence
    (S : Under R ⥤ Arrow (Arrow (Under R))) (i : ℕ) (a : Under R) :
    IsStableEquivalence (((strictDiagramIterate S i).map
      (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor)).app a) := by
  apply modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence S i
    (supportedRow f) (boundedFlatCoefficientSupportedModelFunctor f)
    (supportedRowRestriction f)
    (fun a => (supportedRestriction R (op Q, a) (schemeMap f a)).asEquivalence)
    (fun _ => rfl)
  exact fun a => supportedRowRestriction_inverse_exact f a

/-- The actual coarse component is the unchanged ambient restriction functor. -/
theorem openRowRestriction_functor (a : Under R) :
    ((openRowRestriction f).app a).functor =
      ((coefficientRestriction R).app (op Q, a)).functor := by
  change ((coefficientRestriction R).app (op Q, a)).functor ⋙ 𝟭 _ = _
  exact Functor.comp_id _

/-- The actual coarse restriction is a categorical equivalence with the original ambient inverse. -/
def openRowRestrictionEquivalence (a : Under R) :
    (openRow f).obj a ≌ (boundedFlatCoefficientOpenModelFunctor f).obj a :=
  ((coefficientRestriction R).app (op Q, a)).functor.asEquivalence.changeFunctor
    (eqToIso (openRowRestriction_functor f a).symm)

/-- The equivalence retains the actual coarse component functor literally. -/
theorem openRowRestrictionEquivalence_functor (a : Under R) :
    (openRowRestrictionEquivalence f a).functor = ((openRowRestriction f).app a).functor := rfl

/-- The coarse categorical inverse is the original fine restriction inverse. -/
theorem openRowRestrictionEquivalence_inverse (a : Under R) :
    (openRowRestrictionEquivalence f a).inverse =
      ((coefficientRestriction R).app (op Q, a)).functor.asEquivalence.inverse := rfl

/-- The original fine restriction inverse is also exact for the actual coarse weak classes. -/
theorem openRowRestriction_inverse_exact (a : Under R) :
    IsExact ((boundedFlatCoefficientOpenModelFunctor f).obj a).waldhausen.cof
      ((boundedFlatCoefficientOpenModelFunctor f).obj a).waldhausen.weq
      ((openRow f).obj a).waldhausen.cof ((openRow f).obj a).waldhausen.weq
      ((coefficientRestriction R).app (op Q, a)).functor.asEquivalence.inverse := by
  exact Structure.withInverseImageWeak_inverse_exact
    ((coefficientRestriction R).app (op Q, a)).functor.asEquivalence
    ((coefficientRestriction R).app (op Q, a)).exact
    (coefficientRestriction_inverse_exact R (op Q, a))
    (boundedFlatCoefficientOpenNested f a)

/-- Every finite iterate retains the actual coarse restriction and is stable. -/
theorem openRowRestriction_iterate_isStableEquivalence
    (S : Under R ⥤ Arrow (Arrow (Under R))) (i : ℕ) (a : Under R) :
    IsStableEquivalence (((strictDiagramIterate S i).map
      (Functor.whiskerRight (openRowRestriction f) prespectrumFunctor)).app a) := by
  apply modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence S i
    (openRow f) (boundedFlatCoefficientOpenModelFunctor f) (openRowRestriction f)
    (openRowRestrictionEquivalence f) (openRowRestrictionEquivalence_functor f)
  intro a
  rw [openRowRestrictionEquivalence_inverse]
  exact openRowRestriction_inverse_exact f a

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
