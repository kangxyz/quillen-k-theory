/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedPushforwardPlus
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AcyclicPushforwardResolution

/-! # The actual bounded-below derived unit on acyclic single sheaves

The original right-derived unit is invertible when the actual integer-indexed
injective augmentation remains a quasi-isomorphism after direct image.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.SchemeSheaf
/-- The standard ambient derived category of module sheaves used by the actual unit. -/
local instance acyclicDerivedPushforwardStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- An actual module sheaf placed in degree zero in bounded-below complexes. -/
def singleZeroPlus (X : Scheme.{u}) (M : X.Modules) : CochainComplex.Plus X.Modules :=
  ⟨(CochainComplex.singleFunctor X.Modules 0).obj M, 0, inferInstance⟩

/-- The original right-derived unit is invertible for an actual acyclic resolution. -/
theorem isIso_derivedPushforwardPlusUnit_single_of_resolution {Z X : Scheme.{u}}
    (f : Z ⟶ X) (M : Z.Modules) (I : InjectiveResolution M)
    (hI : QuasiIso (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).map I.ι')) :
    IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus Z M)) := by
  let J : CochainComplex.Plus Z.Modules := ⟨I.cochainComplex, 0, inferInstance⟩
  let q : singleZeroPlus Z M ⟶ J := ObjectProperty.homMk I.ι'
  let F := Scheme.Modules.pushforward f
  have hq : IsIso (DerivedCategory.Plus.Q.map q) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso Z.Modules) q
      (show QuasiIso I.ι' from inferInstance)
  have hFq : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map q)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso X.Modules) _
      hI
  let IJ : CochainComplex (InjectiveObject Z.Modules) ℤ :=
    { X := fun n ↦ ⟨I.cochainComplex.X n, inferInstance⟩
      d := fun i j ↦ ObjectProperty.homMk (I.cochainComplex.d i j)
      shape := fun i j h ↦ by
        apply ObjectProperty.hom_ext
        exact I.cochainComplex.shape i j h
      d_comp_d' := fun i j k _ _ ↦ by
        apply ObjectProperty.hom_ext
        exact I.cochainComplex.d_comp_d i j k }
  have hIJ : IJ.IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    rw [IsZero.iff_id_eq_zero]
    apply ObjectProperty.hom_ext
    exact (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 n hn).eq_of_src _ _
  let IJplus : CochainComplex.Plus (InjectiveObject Z.Modules) := ⟨IJ, 0, hIJ⟩
  have hJ : IsIso ((derivedPushforwardPlusUnit f).app J) :=
    inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι Z.Modules).mapCochainComplexPlus.obj IJplus)))
  have hRq : IsIso ((DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f).map q) :=
    inferInstanceAs (IsIso ((derivedPushforwardPlus f).map (DerivedCategory.Plus.Q.map q)))
  have hcomp : IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus Z M) ≫
      (DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f).map q) := by
    rw [← (derivedPushforwardPlusUnit f).naturality q]
    exact inferInstanceAs
      (IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map q) ≫
        (derivedPushforwardPlusUnit f).app J))
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f).map q)

/-- An original sheaf isomorphism placed in degree zero in bounded-below complexes. -/
def singleZeroPlusIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    singleZeroPlus X M ≅ singleZeroPlus X N :=
  (CochainComplex.plus X.Modules).isoMk ((CochainComplex.singleFunctor X.Modules 0).mapIso e)

/-- Termwise direct image of a single sheaf retains the original single-complex comparison. -/
def pushforwardSingleZeroPlusIso {Z X : Scheme.{u}} (f : Z ⟶ X) (M : Z.Modules) :
    (Scheme.Modules.pushforward f).mapCochainComplexPlus.obj (singleZeroPlus Z M) ≅
      singleZeroPlus X ((Scheme.Modules.pushforward f).obj M) :=
  (CochainComplex.plus X.Modules).isoMk
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.pushforward f) (.up ℤ) 0).app M)

end Quillen.SchemeSheaf
