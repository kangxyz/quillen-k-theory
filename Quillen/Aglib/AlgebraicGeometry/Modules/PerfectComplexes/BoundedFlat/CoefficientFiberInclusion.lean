/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSupportRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SupportUnion
public import Quillen.Aglib.CategoryTheory.ObjectProperty.LiftComposition

/-!
# Actual native fiber-support inclusion

Only the additional fiber support is forgotten. The original evaluation retains the same
complex and literal full-subcategory inclusion.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence

/-- Original intersection support implies the unchanged auxiliary support. -/
theorem boundedFlatCoefficientFiberSupport_le (a : Under R) :
    boundedFlatCoefficientSectionSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι ≤
      boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T a).ι := by
  intro S hS
  exact ((restrictAcyclic_sup_iff (boundedFlatCoefficientSupportOpen Q T a)
    (schemeMap f a).opensRange
    ((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj S).obj).mp hS).1

/-- Forget only the additional closed fiber support, keeping the actual native section. -/
def boundedFlatCoefficientSupportedFiberForget (a : Under R) :
    BoundedFlatCoefficientSupportedFiberSections f T a ⥤
      BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a :=
  ObjectProperty.ιOfLE (boundedFlatCoefficientFiberSupport_le f T a)

theorem propertyEvaluation_forget {C D : Type*} [Category* C] [Category* D]
    (P Q : ObjectProperty C) (hPQ : P ≤ Q) (A B : ObjectProperty D) (hAB : A ≤ B)
    (E : C ⥤ D) (hEA : ∀ X : P.FullSubcategory, A (E.obj X.obj))
    (hEB : ∀ X : Q.FullSubcategory, B (E.obj X.obj)) :
    A.lift (P.ι ⋙ E) hEA ⋙ ObjectProperty.ιOfLE hAB =
      ObjectProperty.ιOfLE hPQ ⋙ B.lift (Q.ι ⋙ E) hEB := rfl

/-- Original intersection support inclusion after evaluation keeps the actual complex. -/
theorem boundedFlatCoefficientSupportedFiberEvaluation_forget (a : Under R) :
    boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientFiberSupportOpen f T a).ι ⋙
      ObjectProperty.ιOfLE
        (show boundedFlatPerfectSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι ≤
          boundedFlatPerfectSupported (boundedFlatCoefficientSupportOpen Q T a).ι from
          fun K hK ↦ ((boundedFlatPerfectSupported_sup_opensRange_iff (schemeMap f a)
            (boundedFlatCoefficientSupportOpen Q T a) K).mp hK).1) =
      boundedFlatCoefficientSupportedFiberForget f T a ⋙
        boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientSupportOpen Q T a).ι := by
  unfold boundedFlatCoefficientSupportedEvaluation
  dsimp only [boundedFlatCoefficientSupportedFiberForget]
  exact propertyEvaluation_forget _ _ _ _ _ _ _ _ _

theorem supportLift_congr {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ D} (h : F = G)
    (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X)) :
    P.lift F hF = P.lift G hG := by
  subst h
  rfl

end Quillen.PerfectComplexes

end

end
