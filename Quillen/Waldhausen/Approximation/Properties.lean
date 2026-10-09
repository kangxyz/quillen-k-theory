import Quillen.Waldhausen.SplitComplexes.FactorizationSubcategory

/-!
# The approximation properties and saturation for split complex models

The two approximation properties are reflection of weak equivalences and
factorization of maps out of an image by an image cofibration followed by
a weak equivalence. They are proved for the canonical identity comparison
from split to ambient cofibrations on a cone-closed complex subcategory.
Both weak-equivalence classes satisfy the two-out-of-three saturation
axiom. No approximation theorem or K-equivalence is stated here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CochainComplex

universe v u v' u'

namespace Quillen.Waldhausen

/-- Waldhausen's App1 and App2, using the cofibration version of App2.
Exactness of the functor and the cylinder hypotheses are separate. -/
structure HasApproximationProperty {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (W : Structure C) (W' : Structure D)
    (F : C ⥤ D) : Prop where
  reflects {X Y : C} (f : X ⟶ Y) : W'.weq (F.map f) → W.weq f
  lift {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    ∃ (X' : C) (i : X ⟶ X') (p : F.obj X' ⟶ Y),
      W.cof i ∧ W'.weq p ∧ F.map i ≫ p = f

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The saturation axiom for actual quasi-isomorphisms in the ambient model. -/
theorem complexes_saturated : (complexes A).weq.HasTwoOutOfThreeProperty :=
  inferInstanceAs ((HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty)

/-- Changing the cofibrations to split maps retains saturation. -/
theorem splitComplexes_saturated : (splitComplexes A).weq.HasTwoOutOfThreeProperty :=
  complexes_saturated

attribute [local instance] Abelian.hasFiniteBiproducts

variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- Saturation is inherited by the actual full complex subcategory. -/
theorem complexSubcategory_saturated : (complexSubcategory P).weq.HasTwoOutOfThreeProperty :=
  inferInstanceAs (((HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).inverseImage P.ι).HasTwoOutOfThreeProperty)

/-- Saturation also holds with the split-cofibration convention. -/
theorem splitComplexSubcategory_saturated :
    (splitComplexSubcategory P).weq.HasTwoOutOfThreeProperty :=
  complexSubcategory_saturated P

/-- Both approximation properties are proved for the canonical identity
comparison, provided the actual object predicate is closed under cones. -/
theorem splitComparison_approximation
    (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
      ∀ f : K ⟶ L, P (mappingCone f)) :
    HasApproximationProperty (splitComplexSubcategory P) (complexSubcategory P)
      (𝟭 P.FullSubcategory) where
  reflects _ h := h
  lift f := SplitFactorization.exists_subcategory_factorization P hcone f

end Quillen.Waldhausen
