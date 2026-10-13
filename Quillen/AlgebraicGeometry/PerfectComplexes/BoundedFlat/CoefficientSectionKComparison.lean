/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSections
public import Quillen.Waldhausen.Functoriality.ExactEquivalence
public import Quillen.Waldhausen.GrothendieckComparison.SmallModel

/-!
# The canonical original native section evaluation on K-groups

One common-universe evaluation bridge retains the original exact forward map and
universe lowering. Its canonical fine-fiber specialization is shared by native open
cofinality and actual geometric spectrum evaluation. The original evaluated object
classes and natural-isomorphism K-map transport are unchanged, including degree zero.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes

section CoefficientOpenKTransport
variable {C C' : Type (u + 1)} [Category.{u + 1} C] [Category.{u + 1} C']
  {D D' : Type (u + 1)} [Category.{u} D] [Category.{u} D']
  (V : Structure C) (W : Structure D) (e : C ≌ D)
  (hE : IsExact V.cof V.weq W.cof W.weq e.functor)
  (hEi : IsExact W.cof W.weq V.cof V.weq e.inverse)

/-- The original exact evaluation, with only the existing universe lift and lowering. -/
def boundedFlatCoefficientEvaluationKEquiv (n : ℕ) : V.K n ≃* W.K n :=
  (KEquivOfExactEquivalence V W.smallModel (e.trans AsSmall.equiv)
    (hE.comp W.smallModel_up_exact) (W.smallModel_down_exact.comp hEi) n).trans
      (W.smallModelKEquiv n).symm

private theorem evaluationKEquiv_apply (n : ℕ) (x : V.K n) :
    boundedFlatCoefficientEvaluationKEquiv V W e hE hEi n x =
      (W.smallModelKEquiv n).symm (KMap (hE.comp W.smallModel_up_exact) n x) := rfl

private theorem evaluationKEquiv_objectClass (A : C) :
    boundedFlatCoefficientEvaluationKEquiv V W e hE hEi 0 (V.kZeroObjectClass A) =
      W.kZeroObjectClass (e.functor.obj A) := by
  rw [evaluationKEquiv_apply]
  apply (W.smallModelKEquiv 0).injective
  rw [MulEquiv.apply_symm_apply, Structure.smallModelKEquiv_objectClass]
  exact KMap_kZeroObjectClass (hE.comp W.smallModel_up_exact) A

variable (V' : Structure C') (W' : Structure D') (e' : C' ≌ D')
  (hE' : IsExact V'.cof V'.weq W'.cof W'.weq e'.functor)
  (hEi' : IsExact W'.cof W'.weq V'.cof V'.weq e'.inverse)
  {F : C ⥤ C'} {G : D ⥤ D'}
  (hF : IsExact V.cof V.weq V'.cof V'.weq F)
  (hG : IsExact W.cof W.weq W'.cof W'.weq G)
  (s : F ⋙ e'.functor ≅ e.functor ⋙ G)

include s in
/-- A genuine evaluation square preserves the original KMaps across the hom universes. -/
theorem boundedFlatCoefficientEvaluationKEquiv_natural (n : ℕ) (x : V.K n) :
    boundedFlatCoefficientEvaluationKEquiv V' W' e' hE' hEi' n (KMap hF n x) =
      KMap hG n (boundedFlatCoefficientEvaluationKEquiv V W e hE hEi n x) := by
  have hs :
      (KMap (hE'.comp W'.smallModel_up_exact) n).comp (KMap hF n) =
        (KMap hG.smallModel n).comp (KMap (hE.comp W.smallModel_up_exact) n) := by
    rw [KMap_comp_KMap, KMap_comp_KMap]
    exact KMap_eq_of_iso _ _ (Functor.isoWhiskerRight s AsSmall.up) n
  apply (W'.smallModelKEquiv n).injective
  have hn := DFunLike.congr_fun (smallModelKEquiv_naturality hG n)
    (boundedFlatCoefficientEvaluationKEquiv V W e hE hEi n x)
  change W'.smallModelKEquiv n
      (KMap hG n (boundedFlatCoefficientEvaluationKEquiv V W e hE hEi n x)) =
    KMap hG.smallModel n
      (W.smallModelKEquiv n (boundedFlatCoefficientEvaluationKEquiv V W e hE hEi n x)) at hn
  simp only [evaluationKEquiv_apply, MulEquiv.apply_symm_apply] at hn ⊢
  rw [hn]
  exact DFunLike.congr_fun hs x

end CoefficientOpenKTransport

variable {R : CommRingCat.{u}}

/-- Original identity evaluation computes all native bounded-flat fiber K-groups. -/
def boundedFlatCoefficientSectionKEquiv (i : Index R) (n : ℕ) :
    (boundedFlatCoefficientSectionWaldhausen i).K n ≃*
      (boundedFlatPerfectWaldhausen (space i)).K n :=
  boundedFlatCoefficientEvaluationKEquiv (boundedFlatCoefficientSectionWaldhausen i)
    (boundedFlatPerfectWaldhausen (space i)) (boundedFlatCoefficientSectionEquivalence i)
    (boundedFlatCoefficientOriginalEvaluation_exact i)
    (boundedFlatCoefficientSectionEquivalence_inverse_exact i) n

/-- Original evaluation retains exactly the original bounded-flat object's K-zero class. -/
@[simp] theorem boundedFlatCoefficientSectionKEquiv_objectClass (i : Index R)
    (S : BoundedFlatCoefficientSections i) :
    boundedFlatCoefficientSectionKEquiv i 0
        ((boundedFlatCoefficientSectionWaldhausen i).kZeroObjectClass S) =
      (boundedFlatPerfectWaldhausen (space i)).kZeroObjectClass
        ((boundedFlatCoefficientOriginalEvaluation i).obj S) :=
  evaluationKEquiv_objectClass
    (boundedFlatCoefficientSectionWaldhausen i) (boundedFlatPerfectWaldhausen (space i))
    (boundedFlatCoefficientSectionEquivalence i) (boundedFlatCoefficientOriginalEvaluation_exact i)
    (boundedFlatCoefficientSectionEquivalence_inverse_exact i) S

end Quillen.PerfectComplexes
