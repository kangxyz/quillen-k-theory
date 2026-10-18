/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalLocalizationEquivalence
public import Quillen.Waldhausen.ExtensionCategory.ExactTransport

/-!
# Actual restriction from coarse global sections to fine global open sections

The underlying functor is the original joint global reindexing. Exactness is transported
through the actual coefficient restriction equivalence; the chosen global zero is unchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] globalModel boundedFlatCoefficientSectionWaldhausen
  boundedFlatCoefficientOriginalEvaluation
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The original fine global cross-row reindexing. -/
def globalOpenFineRestriction : globalRow Q ⟶ globalRow P :=
  Functor.whiskerRight (rowTransformation f)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R ⋙ globalModel)

/-- Full-index naturality retains the original joint section reindexing. -/
theorem globalOpenRestriction_functor_square (a : Under R) :
    ((globalOpenFineRestriction f).app a).functor ⋙ ((rowRestriction P).app a).functor =
      ((openRowRestriction f).app a).functor ⋙
        (boundedFlatCoefficientOpenRestrictionModelMap f a).functor := by
  rw [openRowRestriction_functor]
  exact congrArg Model.Hom.functor
    ((coefficientRestriction R).naturality (show (op Q, a) ⟶ (op P, a) from (f.op, 𝟙 a)))

/-- Coarse-to-fine exactness follows from the actual restriction inverse and its unit. -/
theorem globalOpenRestriction_exact (a : Under R) :
    IsExact ((openRow f).obj a).waldhausen.cof ((openRow f).obj a).waldhausen.weq
      ((globalRow P).obj a).waldhausen.cof ((globalRow P).obj a).waldhausen.weq
      ((globalOpenFineRestriction f).app a).functor := by
  let e := ((coefficientRestriction R).app (op P, a)).functor.asEquivalence
  have h := (((openRowRestriction f).app a).exact.comp
    (boundedFlatCoefficientOpenRestrictionModelMap f a).exact).comp
      (coefficientRestriction_inverse_exact R (op P, a))
  let i : (((openRowRestriction f).app a).functor ⋙
      (boundedFlatCoefficientOpenRestrictionModelMap f a).functor) ⋙ e.inverse ≅
      ((globalOpenFineRestriction f).app a).functor :=
    Functor.isoWhiskerRight (eqToIso (globalOpenRestriction_functor_square f a).symm)
      e.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _
  exact ExtensionCategory.isExact_of_natIso _ _ h i

/-- The original reindexing with coarse source weakness and the same chosen global zero. -/
def globalOpenRestrictionModelMap (a : Under R) :
    (openRow f).obj a ⟶ (globalRow P).obj a where
  functor := ((globalOpenFineRestriction f).app a).functor
  exact := globalOpenRestriction_exact f a
  zero := ((globalOpenFineRestriction f).app a).zero

/-- Actual restriction is strictly natural in the coefficient object. -/
def globalOpenRestriction : openRow f ⟶ globalRow P where
  app := globalOpenRestrictionModelMap f
  naturality a b g := by
    apply Model.Hom.ext
    change ((globalRow Q).map g).functor ⋙
        ((globalOpenFineRestriction f).app b).functor =
      ((globalOpenFineRestriction f).app a).functor ⋙ ((globalRow P).map g).functor
    exact congrArg Model.Hom.functor ((globalOpenFineRestriction f).naturality g)

/-- The actual full-open coefficient comparison square is strict. -/
theorem globalOpenRestriction_square :
    globalOpenRestriction f ≫ rowRestriction P =
      openRowRestriction f ≫ boundedFlatCoefficientOpenRestrictionModelTransformation f := by
  ext a
  apply Model.Hom.ext
  exact globalOpenRestriction_functor_square f a

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
