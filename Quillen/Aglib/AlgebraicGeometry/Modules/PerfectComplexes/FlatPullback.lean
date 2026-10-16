/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Extension
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Pullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.RestrictionFunctoriality
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.Complex.Pullback

/-!
# Flat pullback of locally perfect complexes

Actual flat termwise pullback descends to the existing derived localization and preserves local strict models. The inherited exact functor and all geometric comparison isomorphisms are retained.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen





open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- The actual flat termwise pullback, followed by localization, inverts quasi-isomorphisms. -/
theorem pullback_toDerived_inverts {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)).IsInvertedBy
      (AlgebraicGeometry.Scheme.Modules.Complex.pullback f ⋙ DerivedCategory.Q
        (C := X.Modules)) := by
  intro K L s hs
  let : QuasiIso s := hs
  exact (inferInstanceAs (IsIso (DerivedCategory.Q.map
    ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).map s))))

/-- The actual functor on the existing quasi-isomorphism localization. -/
def derivedFlatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] : DerivedCategory Y.Modules
    ⥤ DerivedCategory X.Modules :=
  Localization.Construction.lift (AlgebraicGeometry.Scheme.Modules.Complex.pullback f
    ⋙ DerivedCategory.Q (C := X.Modules))
    (pullback_toDerived_inverts f)

/-- The constructed derived functor retains the original geometric pullback. -/
theorem toDerived_derivedFlatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    DerivedCategory.Q (C := Y.Modules) ⋙ derivedFlatPullback f
      = AlgebraicGeometry.Scheme.Modules.Complex.pullback f ⋙
      DerivedCategory.Q (C := X.Modules) :=
  Localization.Construction.fac _ _

/-- The factorization through the existing derived localization. -/
def derivedFlatPullbackFactors {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    DerivedCategory.Q (C := Y.Modules) ⋙ derivedFlatPullback f
      ≅ AlgebraicGeometry.Scheme.Modules.Complex.pullback f ⋙
      DerivedCategory.Q (C := X.Modules) :=
  eqToIso (toDerived_derivedFlatPullback f)

/-- Flat geometric pullback of an actual isomorphism in the derived localization. -/
def flatPullbackDerivedIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {K L : CochainComplex Y.Modules ℤ}
    (e : (DerivedCategory.Q (C := Y.Modules)).obj K ≅ (DerivedCategory.Q (C := Y.Modules)).obj L) :
    (DerivedCategory.Q (C := X.Modules)).obj ((AlgebraicGeometry.Scheme.Modules.Complex.pullback
      f).obj K) ≅
      (DerivedCategory.Q (C := X.Modules)).obj ((AlgebraicGeometry.Scheme.Modules.Complex.pullback
        f).obj L) :=
  ((derivedFlatPullbackFactors f).app K).symm ≪≫
    (derivedFlatPullback f).mapIso e ≪≫ (derivedFlatPullbackFactors f).app L

/-- Genuine flat pullback preserves the original local derived strict-model condition. -/
theorem locallyPerfect_flatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {K : CochainComplex Y.Modules ℤ} (hK : locallyPerfect Y K) :
    locallyPerfect X ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj K) := by
  intro x
  obtain ⟨U, hx, P, ⟨eP⟩⟩ := hK (f x)
  refine ⟨f ⁻¹ᵁ U, hx, ⟨(AlgebraicGeometry.Scheme.Modules.Complex.pullback (f ∣_ U)).obj P.obj,
    strictPerfect_pullback (f ∣_ U) P.property⟩, ?_⟩
  exact ⟨(DerivedCategory.Q (C := (f ⁻¹ᵁ U).toScheme.Modules)).mapIso
    ((AlgebraicGeometry.Scheme.Modules.Complex.pullbackRestrictIso f U).app K) ≪≫
    flatPullbackDerivedIso (f ∣_ U) eP⟩

/-- Actual geometric flat pullback on the full category of locally perfect complexes. -/
def perfectFlatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] : Perfect Y ⥤ Perfect X :=
  (locallyPerfect X).lift ((locallyPerfect Y).ι ⋙ AlgebraicGeometry.Scheme.Modules.Complex.pullback
    f)
    (fun K => locallyPerfect_flatPullback f K.property)

instance perfectFlatPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (perfectFlatPullback f).Additive := by unfold perfectFlatPullback; infer_instance

/-- Flat exactness for the original inherited perfect-complex exact structures. -/
def perfectExactFlatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex Y.Modules ℤ))
        (locallyPerfect Y))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
        (locallyPerfect X)) where
  toFunctor := perfectFlatPullback f
  map_conflation S hS := by
    change ((S.map (locallyPerfect Y).ι).map (AlgebraicGeometry.Scheme.Modules.Complex.pullback
      f)).ShortExact
    exact hS.map_of_exact _

/-- Geometric identity comparison on the original locally-perfect category. -/
def perfectFlatPullbackIdIso (X : Scheme.{u}) :
    perfectFlatPullback (𝟙 X) ≅ 𝟭 (Perfect X) :=
  Functor.fullyFaithfulCancelRight (locallyPerfect X).ι
    (Functor.isoWhiskerLeft (locallyPerfect X).ι (Scheme.Modules.Complex.pullbackIdIso X))

/-- Geometric composition comparison on the original locally-perfect category. -/
def perfectFlatPullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Flat f] [Flat g] :
    perfectFlatPullback (f ≫ g) ≅ perfectFlatPullback g ⋙ perfectFlatPullback f :=
  Functor.fullyFaithfulCancelRight (locallyPerfect X).ι
    (Functor.isoWhiskerLeft (locallyPerfect Z).ι (Scheme.Modules.Complex.pullbackCompIso f g))

/-- Geometric open restriction agrees with flat pullback on all locally-perfect complexes. -/
def perfectRestrictIsoFlatPullback {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    perfectRestrict j ≅ perfectFlatPullback j :=
  Functor.fullyFaithfulCancelRight (locallyPerfect X).ι
    (Functor.isoWhiskerLeft (locallyPerfect Y).ι (restrictIsoPullbackComplex j))

/-- Flat pullback commutes with restriction to an inverse-image open. -/
def perfectFlatPullbackRestrictIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (U : Y.Opens) :
    perfectFlatPullback f ⋙ perfectRestrict (f ⁻¹ᵁ U).ι ≅
      perfectRestrict U.ι ⋙ perfectFlatPullback (f ∣_ U) :=
  Functor.fullyFaithfulCancelRight (locallyPerfect (f ⁻¹ᵁ U).toScheme).ι
    (Functor.isoWhiskerLeft (locallyPerfect Y).ι
      (AlgebraicGeometry.Scheme.Modules.Complex.pullbackRestrictIso f U))

end Quillen.PerfectComplexes

end

end
