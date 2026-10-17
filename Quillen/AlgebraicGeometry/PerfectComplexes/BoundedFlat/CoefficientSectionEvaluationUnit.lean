/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismRebase


public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationNaturality
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSectionUnits
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismSquare

/-!
# The actual normalized joint evaluation and original geometric unit

Original faithful-evaluation section units are retained by the lifted, zero-normalized
evaluation functor. The existing normalized raw pullback unit is the target's same
identity action on its original Model functor. Their categorical square therefore
commutes along the unchanged E1 evaluation comparison. These equations do not supply
the two-chart Bass boundary, cone null comparison, iterates or telescope.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.FunctorIdentityAutomorphism
universe u u₁ v₁
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso

local instance {X : Scheme.{u}} :
    (AsSmall.down : Quillen.Waldhausen.SmallModel (BoundedFlatPerfect X) ⥤
      BoundedFlatPerfect X).IsEquivalence :=
  (AsSmall.equiv : BoundedFlatPerfect X ≌
    Quillen.Waldhausen.SmallModel (BoundedFlatPerfect X)).isEquivalence_inverse

/-- The same prescribed geometric identity action in its genuine common-universe model. -/
def boundedFlatCoefficientSmallUnitIso (i : Index R) (r : (Γ(space i, ⊤))ˣ) :
    𝟭 (Quillen.Waldhausen.SmallModel (BoundedFlatPerfect (space i))) ≅
      𝟭 (Quillen.Waldhausen.SmallModel (BoundedFlatPerfect (space i))) :=
  lift (AsSmall.down : Quillen.Waldhausen.SmallModel (BoundedFlatPerfect (space i)) ⥤
    BoundedFlatPerfect (space i)) (boundedFlatPerfectGlobalUnitIso (space i) r)

private theorem sectionSmallEquivalence_unit_preserves (i : Index R)
    (r : (Γ(space i, ⊤))ˣ) :
    Preserves (boundedFlatCoefficientSectionSmallEquivalence i).functor
      (boundedFlatCoefficientSectionUnitIso i r) (boundedFlatCoefficientSmallUnitIso i r) := by
  intro S
  apply (AsSmall.down : Quillen.Waldhausen.SmallModel (BoundedFlatPerfect (space i)) ⥤
    BoundedFlatPerfect (space i)).map_injective
  change (boundedFlatCoefficientOriginalEvaluation i).map
      ((boundedFlatCoefficientSectionUnitIso i r).hom.app S) =
    AsSmall.down.map ((boundedFlatCoefficientSmallUnitIso i r).hom.app
      (AsSmall.up.obj ((boundedFlatCoefficientOriginalEvaluation i).obj S)))
  rw [boundedFlatCoefficientSmallUnitIso, map_lift_hom]
  exact boundedFlatCoefficientSectionUnitIso_evaluation_hom i r S

/-- The original evaluated forward unit survives both universe lifting and actual zero rebasing. -/
theorem boundedFlatCoefficientSectionEvaluation_unit_preserves (i : Index R)
    (r : (Γ(space i, ⊤))ˣ) :
    Preserves (boundedFlatCoefficientSectionEvaluationModelMap i).functor
      (boundedFlatCoefficientSectionUnitIso i r) (boundedFlatCoefficientSmallUnitIso i r) := by
  change Preserves (Quillen.rebaseFunctor
    (boundedFlatCoefficientSectionSmallEquivalence i).functor
    (boundedFlatCoefficientSectionWaldhausen i).zero
    (boundedFlatPerfectWaldhausen (space i)).smallModel.zero
    (boundedFlatCoefficientSectionEvaluationZeroIso i)) _ _
  exact rebase_preserves _ _ _ _ _ _ (sectionSmallEquivalence_unit_preserves i r)

/-- The unchanged original raw geometric unit, with its actual zero normalization and lift. -/
def boundedFlatCoefficientOriginalModelUnit {i k : Index R} (f : i ⟶ k)
    (r : (Γ(space k, ⊤))ˣ) :
    (boundedFlatCoefficientOriginalModelMap f).functor ⟶
      (boundedFlatCoefficientOriginalModelMap f).functor :=
  whiskerLeft AsSmall.down (whiskerRight
    (normalizedWeakTransformation
      (boundedFlatPerfectPullback_exact (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f))
      (boundedFlatPerfectPullback_exact (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f))
      (boundedFlatPerfectPullbackUnitIso
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) r).hom) AsSmall.up)

/-- Its forward component is exactly the same target unit on the actual normalized raw functor. -/
theorem boundedFlatCoefficientOriginalModelUnit_eq {i k : Index R} (f : i ⟶ k)
    (r : (Γ(space k, ⊤))ˣ) :
    boundedFlatCoefficientOriginalModelUnit f r =
      (onFunctor (boundedFlatCoefficientOriginalModelMap f).functor
        (boundedFlatCoefficientSmallUnitIso k r)).hom := by
  apply NatTrans.ext
  funext X
  change Quillen.Waldhausen.SmallModel (BoundedFlatPerfect (space i)) at X
  apply (AsSmall.down : Quillen.Waldhausen.SmallModel (BoundedFlatPerfect (space k)) ⥤
    BoundedFlatPerfect (space k)).map_injective
  rw [onFunctor_hom_app, boundedFlatCoefficientSmallUnitIso, map_lift_hom]
  simp only [boundedFlatCoefficientOriginalModelUnit, whiskerLeft_app, whiskerRight_app,
    AsSmall.down_map, AsSmall.up_map_down, normalizedWeakTransformation, NatTrans.comp_app]
  let p := boundedFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
  let h := boundedFlatPerfectPullback_exact (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
  let q := Quillen.rebaseFunctor p
    (boundedFlatPerfectWaldhausen (space i)).zero
    (boundedFlatPerfectWaldhausen (space k)).zero
    ((h.zero (boundedFlatPerfectWaldhausen (space i)).isZero).iso
      (boundedFlatPerfectWaldhausen (space k)).isZero)
  let z : p ≅ q := Quillen.rebaseFunctorIso _ _ _ _
  simp only [boundedFlatPerfectPullbackUnitIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom]
  have hn := (boundedFlatPerfectGlobalUnitIso (space k) r).hom.naturality
    (z.hom.app (AsSmall.down.obj X))
  simp only [Functor.id_map, Functor.id_obj] at hn
  change z.inv.app (AsSmall.down.obj X) ≫
      (boundedFlatPerfectGlobalUnitIso (space k) r).hom.app
        (p.obj (AsSmall.down.obj X)) ≫ z.hom.app (AsSmall.down.obj X) =
    (boundedFlatPerfectGlobalUnitIso (space k) r).hom.app (q.obj (AsSmall.down.obj X))
  rw [← hn, Iso.inv_hom_id_app_assoc]

/-- The actual E1 comparison intertwines the original section and normalized raw geometric units. -/
theorem boundedFlatCoefficientSectionEvaluation_unit_square {i k : Index R} (f : i ⟶ k)
    (r : (Γ(space k, ⊤))ˣ) :
    whiskerRight (onFunctor (boundedFlatCoefficientSectionModelMap f).functor
        (boundedFlatCoefficientSectionUnitIso k r)).hom
        (boundedFlatCoefficientSectionEvaluationModelMap k).functor ≫
      (boundedFlatCoefficientSectionEvaluationIso f).hom =
    (boundedFlatCoefficientSectionEvaluationIso f).hom ≫
      whiskerLeft (boundedFlatCoefficientSectionEvaluationModelMap i).functor
        (boundedFlatCoefficientOriginalModelUnit f r) := by
  rw [boundedFlatCoefficientOriginalModelUnit_eq]
  exact onFunctor_whisker_square
    (boundedFlatCoefficientSectionModelMap f).functor
    (boundedFlatCoefficientOriginalModelMap f).functor
    (boundedFlatCoefficientSectionEvaluationModelMap i).functor
    (boundedFlatCoefficientSectionEvaluationModelMap k).functor
    (boundedFlatCoefficientSectionEvaluationIso f).hom
    (boundedFlatCoefficientSectionUnitIso k r) (boundedFlatCoefficientSmallUnitIso k r)
    (boundedFlatCoefficientSectionEvaluation_unit_preserves k r).whisker

end Quillen.PerfectComplexes
