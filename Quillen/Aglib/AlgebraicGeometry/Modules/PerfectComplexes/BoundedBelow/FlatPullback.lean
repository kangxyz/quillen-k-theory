/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlatPullback
public import Aglib.CategoryTheory.ExactCategory.Functor

/-!
# Flat pullback of lower-bounded perfect complexes

Actual flat termwise pullback preserves the same specified lower bound and inherited short
exact sequences.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine.SelfBaseChange
/-- Literal flat pullback with the original existential strict lower bound. -/
def boundedFlatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    BoundedBelow.Obj Y ⥤ BoundedBelow.Obj X :=
  ObjectProperty.lift _ ((BoundedBelow.objects Y).ι ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.pullback f) (fun K => by
    obtain ⟨hp, a, ha⟩ := K.property
    let := ha
    refine ⟨locallyPerfect_flatPullback f hp, a, ?_⟩
    apply (CochainComplex.isStrictlyGE_iff _ a).mpr
    intro n hn
    exact (Scheme.Modules.pullback f).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn))

instance boundedFlatPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (boundedFlatPullback f).Additive := by
  unfold boundedFlatPullback
  infer_instance

/-- Every specified original lower bound is retained by flat pullback. -/
lemma boundedFlatPullback_isStrictlyGE {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (K : BoundedBelow.Obj Y) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((boundedFlatPullback f).obj K).obj.IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (Scheme.Modules.pullback f).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)

/-- Flat pullback preserves the inherited actual short exact sequences. -/
def boundedFlatPullbackExactFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex Y.Modules ℤ))
      (BoundedBelow.objects Y))
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (BoundedBelow.objects X)) where
  toFunctor := boundedFlatPullback f
  map_conflation S hs := by
    change (S.map (BoundedBelow.objects Y).ι).ShortExact at hs
    change ((S.map (BoundedBelow.objects Y).ι).map
      (AlgebraicGeometry.Scheme.Modules.Complex.pullback f)).ShortExact
    exact hs.map_of_exact _


end Quillen.PerfectComplexes.ProjectiveLine.SelfBaseChange
end
end

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
/-- Literal flat geometric pullback on original lower-bounded perfect complexes. -/
def boundedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    BoundedBelow.Obj Y ⥤ BoundedBelow.Obj X :=
  ObjectProperty.lift _ ((BoundedBelow.objects Y).ι ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.pullback f) (fun K => by
    obtain ⟨hp, a, ha⟩ := K.property
    let := ha
    refine ⟨locallyPerfect_flatPullback f hp, a, ?_⟩
    apply (CochainComplex.isStrictlyGE_iff _ a).mpr
    intro n hn
    exact (Scheme.Modules.pullback f).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn))

instance boundedPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (boundedPullback f).Additive := by
  unfold boundedPullback
  infer_instance

/-- Original flat pullback preserves inherited actual exact sequences. -/
def boundedPullbackExactFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex Y.Modules ℤ))
      (BoundedBelow.objects Y))
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (BoundedBelow.objects X)) where
  toFunctor := boundedPullback f
  map_conflation S hs := by
    change (S.map (BoundedBelow.objects Y).ι).ShortExact at hs
    change ((S.map (BoundedBelow.objects Y).ι).map
      (AlgebraicGeometry.Scheme.Modules.Complex.pullback f)).ShortExact
    exact hs.map_of_exact _


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
end
end
