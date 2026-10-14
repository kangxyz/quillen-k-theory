/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Typed postcomposition of an original natural unit -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.SchemeSheaf

/-- Postcompose a natural unit before specializing any actual resolution functor. -/
def originalNaturalUnitPostcompose {A : Type*} [Category A] (G F : A ⥤ A)
    (η : 𝟭 A ⟶ G) : F ⟶ G ⋙ F where
  app K := F.map (η.app K)
  naturality {K C} f := by
    change F.map f ≫ F.map (η.app C) = F.map (η.app K) ≫ F.map (G.map f)
    simp only [← Functor.map_comp]
    exact congrArg F.map (η.naturality f)

/-- The actual further postcomposition of this unit. -/
def originalNaturalUnitTotalPostcompose {A : Type*} [Category A] (G F T : A ⥤ A)
    (η : 𝟭 A ⟶ G) : F ⋙ T ⟶ (G ⋙ F) ⋙ T :=
  Functor.whiskerRight (originalNaturalUnitPostcompose G F η) T

/-- Its literal component uses the original unit in its original order. -/
lemma originalNaturalUnitTotalPostcompose_app {A : Type*} [Category A]
    (G F T : A ⥤ A) (η : 𝟭 A ⟶ G) (K : A) :
    (originalNaturalUnitTotalPostcompose G F T η).app K = T.map (F.map (η.app K)) := rfl

/-- Typed weak-arrow transport before any chosen total is specialized. -/
theorem originalNaturalUnitTotalPostcompose_quasiIso {X : Scheme.{u}}
    (G F T : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules)
    (η : 𝟭 (CochainComplex.Plus X.Modules) ⟶ G)
    (hη : ∀ K, QuasiIso (η.app K).hom)
    (hF : ∀ {K C : CochainComplex.Plus X.Modules} (f : K ⟶ C),
      QuasiIso f.hom → QuasiIso (F.map f).hom)
    (hT : ∀ {K C : CochainComplex.Plus X.Modules} (f : K ⟶ C),
      QuasiIso f.hom → QuasiIso (T.map f).hom)
    (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((originalNaturalUnitTotalPostcompose G F T η).app K).hom :=
  hT (F.map (η.app K)) (hF (η.app K) (hη K))

/-- Actual weak maps compose in the original Plus category. -/
lemma originalPlusWeakComp {X : Scheme.{u}} {K C D : CochainComplex.Plus X.Modules}
    (f : K ⟶ C) (g : C ⟶ D) [QuasiIso f.hom] [QuasiIso g.hom] :
    QuasiIso (f ≫ g).hom := by
  change QuasiIso (f.hom ≫ g.hom)
  infer_instance

/-- An actual Plus isomorphism is weak on its actual underlying complex. -/
lemma originalPlusIsoWeak {X : Scheme.{u}} {K C : CochainComplex.Plus X.Modules}
    (f : K ⟶ C) [IsIso f] : QuasiIso f.hom := by
  let : IsIso f.hom := Functor.map_isIso (CochainComplex.Plus.ι X.Modules) f
  infer_instance

/-- Composition of actual natural weak transformations is weak. -/
lemma originalPlusNatTransWeakComp {X : Scheme.{u}} {D : Type*} [Category D]
    {F G H : D ⥤ CochainComplex.Plus X.Modules} (α : F ⟶ G) (β : G ⟶ H)
    (hα : ∀ K, QuasiIso (α.app K).hom) (hβ : ∀ K, QuasiIso (β.app K).hom) (K : D) :
    QuasiIso ((α ≫ β).app K).hom := by
  let := hα K
  let := hβ K
  exact originalPlusWeakComp (α.app K) (β.app K)

/-- Precomposition preserves the exact actual components of a natural weak map. -/
lemma originalPlusNatTransPrecomposeWeak {X : Scheme.{u}} {D : Type*} [Category D]
    {F G : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules}
    (α : F ⟶ G) (H : D ⥤ CochainComplex.Plus X.Modules)
    (hα : ∀ C, QuasiIso (α.app C).hom) (K : D) :
    QuasiIso ((Functor.whiskerLeft H α).app K).hom := hα (H.obj K)

/-- Pull back an original unit to the image of a typed input functor. -/
def originalNaturalUnitPrecompose {A : Type*} [Category A] (T F : A ⥤ A)
    (η : 𝟭 A ⟶ T) : F ⟶ F ⋙ T where
  app K := η.app (F.obj K)
  naturality {_K _C} f := η.naturality (F.map f)

/-- The same original unit stays weak before any outer total is applied. -/
lemma originalNaturalUnitPrecompose_quasiIso {X : Scheme.{u}}
    (T F : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules)
    (η : 𝟭 (CochainComplex.Plus X.Modules) ⟶ T)
    (hη : ∀ C, QuasiIso (η.app C).hom) (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((originalNaturalUnitPrecompose T F η).app K).hom := hη (F.obj K)

/-- Apply a proved weak-preserving functor to an actual natural weak map. -/
lemma originalPlusNatTransPostcomposeWeak {X : Scheme.{u}} {D : Type*} [Category D]
    {F G : D ⥤ CochainComplex.Plus X.Modules} (α : F ⟶ G)
    (T : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules)
    (hα : ∀ K, QuasiIso (α.app K).hom)
    (hT : ∀ {K C : CochainComplex.Plus X.Modules} (f : K ⟶ C),
      QuasiIso f.hom → QuasiIso (T.map f).hom) (K : D) :
    QuasiIso ((Functor.whiskerRight α T).app K).hom := hT (α.app K) (hα K)

end Quillen.SchemeSheaf
