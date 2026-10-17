/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareFiveSimplex
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleLeftColumnNodes
public import Quillen.Waldhausen.SConstruction.Iterated.ExactCoherence

/-! Explicit model endpoints for the original binary square normalization words. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.NativeSquareModelNormalization
open BassH0Merge

/-- The binary target is the full composite of the two original normalized model maps. -/
theorem targetMap_eq_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    BinaryNormalizationSimplex.targetMap f g = normalizedMap g ≫ normalizedMap f := by
  exact modelMap_comp (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen Y)
    (boundedFlatPerfectWaldhausen X) (boundedFlatNormalizedPullback_exact g)
    (boundedFlatNormalizedPullback_exact f) (boundedFlatNormalizedPullback_obj_zero g)
    (boundedFlatNormalizedPullback_obj_zero f)

/-- The original binary total with its composite model endpoint transported explicitly. -/
def total {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (BinaryNormalizationSimplex.sourceMap f g).functor ≅
      (normalizedMap g ≫ normalizedMap f).functor :=
  BinaryNormalizationSimplex.total f g ≪≫
    eqToIso (congrArg Model.Hom.functor (targetMap_eq_comp f g))

/-- The complete right square word, with the same source equality and explicit model endpoint. -/
def rightIso {X Y Z T : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z)
    (q : X ⟶ T) (w : T ⟶ Z) (h : p ≫ v = q ≫ w) :
    (NativeSquareFiveSimplex.source p v).functor ≅
      (normalizedMap w ≫ normalizedMap q).functor :=
  NativeSquareFiveSimplex.sourceIso p v q w h ≪≫ total q w

/-- Explicit endpoint transport retains the original binary total as an isomorphism. -/
theorem total_original {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    total f g =
      (BinaryNormalizationSimplex.total f g :
        (BinaryNormalizationSimplex.sourceMap f g).functor ≅
          (normalizedMap g ≫ normalizedMap f).functor) := by
  apply Iso.ext
  rfl

/-- Explicit endpoint transport retains the complete original right-square word. -/
theorem rightIso_original {X Y Z T : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z)
    (q : X ⟶ T) (w : T ⟶ Z) (h : p ≫ v = q ≫ w) :
    rightIso p v q w h =
      (NativeSquareFiveSimplex.sourceIso p v q w h ≪≫ BinaryNormalizationSimplex.total q w :
        (NativeSquareFiveSimplex.source p v).functor ≅
          (normalizedMap w ≫ normalizedMap q).functor) := by
  rw [rightIso, total_original]

private theorem normalize_node {A B : Model.{u}} (S F F' : A ⟶ B) (e : F = F')
    (η : S.functor ≅ F.functor) :
    (⟨F, η⟩ : Σ K : A ⟶ B, S.functor ≅ K.functor) =
      ⟨F', η ≪≫ eqToIso (congrArg Model.Hom.functor e)⟩ := by
  subst F'
  simp only [eqToIso_refl, Iso.trans_refl]

/-- The fourth full square node uses the explicitly transported composite model endpoint. -/
theorem nodes_four {X Y Z T : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z)
    (q : X ⟶ T) (w : T ⟶ Z) (h : p ≫ v = q ≫ w) :
    NativeSquareFiveSimplex.nodes p v q w h 4 =
      (⟨normalizedMap w ≫ normalizedMap q, rightIso p v q w h⟩ :
        NativeSquareFiveSimplex.Node p v) := by
  change (⟨BinaryNormalizationSimplex.targetMap q w,
    NativeSquareFiveSimplex.sourceIso p v q w h ≪≫
      BinaryNormalizationSimplex.total q w⟩ : NativeSquareFiveSimplex.Node p v) = _
  simpa only [rightIso, total, Iso.trans_assoc] using
    normalize_node (NativeSquareFiveSimplex.source p v) _ _ (targetMap_eq_comp q w)
      (NativeSquareFiveSimplex.sourceIso p v q w h ≪≫ BinaryNormalizationSimplex.total q w)

/-- The second full square node retains its original total and explicit composite model endpoint. -/
theorem nodes_two {X Y Z T : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z)
    (q : X ⟶ T) (w : T ⟶ Z) (h : p ≫ v = q ≫ w) :
    NativeSquareFiveSimplex.nodes p v q w h 2 =
      (⟨normalizedMap v ≫ normalizedMap p, total p v⟩ :
        NativeSquareFiveSimplex.Node p v) := by
  exact normalize_node (NativeSquareFiveSimplex.source p v) _ _ (targetMap_eq_comp p v)
    (BinaryNormalizationSimplex.total p v)

/-- Cancellation of the original middle anchor is performed before specializing model endpoints. -/
theorem cancel_middle {C : Type*} [Category C] {A B D E F : C}
    (h : A ≅ B) (e : B ≅ D) (a : A ≅ E) (l : E ≅ D) (r : E ≅ F)
    (hh : h ≪≫ e = a ≪≫ l) : h ≪≫ (e ≪≫ l.symm ≪≫ r) = a ≪≫ r := by
  rw [← Iso.trans_assoc, hh]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]


/-- The two associators in a chart attachment can be cancelled before model specialization. -/
theorem whiskered_cancel {A B C D E : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    (J : A ⥤ B) (K : B ⥤ C) (L : C ⥤ D) (M : B ⥤ E) (N : E ⥤ D)
    (F : A ⥤ C) (G : A ⥤ D) (H : B ⥤ D)
    (ε : F ≅ J ⋙ K) (h : G ≅ F ⋙ L) (l : H ≅ K ⋙ L)
    (r : H ≅ M ⋙ N) (a : G ≅ J ⋙ H)
    (hh : h ≪≫ isoWhiskerRight ε L = a ≪≫ isoWhiskerLeft J l) :
    h ≪≫ ((isoWhiskerRight ε L ≪≫ Functor.associator J K L ≪≫
      isoWhiskerLeft J l.symm) ≪≫ isoWhiskerLeft J r ≪≫
        (Functor.associator J M N).symm) =
      (a ≪≫ isoWhiskerLeft J r) ≪≫ (Functor.associator J M N).symm := by
  have h₁ : Functor.associator J K L = Iso.refl _ := rfl
  have h₂ : Functor.associator J M N = Iso.refl _ := rfl
  simp only [h₁, h₂, Iso.refl_symm, Iso.refl_trans]
  have hz := cancel_middle h (isoWhiskerRight ε L) a (isoWhiskerLeft J l)
    (isoWhiskerLeft J r) hh
  rw [isoWhiskerLeft_symm] at hz
  simpa only [Iso.trans_assoc] using
    congrArg (fun z ↦ z ≪≫ Iso.refl ((J ⋙ M) ⋙ N)) hz

end Quillen.PerfectComplexes.NativeSquareModelNormalization
