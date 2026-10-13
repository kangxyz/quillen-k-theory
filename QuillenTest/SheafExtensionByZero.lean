/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ExtensionByZeroBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatGenerators

/-! Semantic consumers of actual extension by zero and open base change. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Quillen.SchemeSheaf

namespace QuillenTest.SheafExtensionByZero

open Quillen

/-- The original arbitrary short exact sequence survives the genuine left extension. -/
theorem original_short_exact {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (S : ShortComplex U.Modules) (hS : S.ShortExact) :
    (S.map (extensionByZero j)).ShortExact ∧
      (extensionByZero j).map S.f ≫ (extensionByZero j).map S.g = 0 := by
  exact ⟨shortExact_extensionByZero j hS, by rw [← Functor.map_comp, S.zero, Functor.map_zero]⟩

/-- The actual unit and counit, rather than an arbitrary recovery isomorphism. -/
theorem actual_adjunction_recovery {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : U.Modules) :
    (extensionByZeroRestrictAdjunction j).unit.app M ≫ (extensionByZeroRestrictIso j).hom.app M = 𝟙
      M ∧
    (extensionByZero j).map ((extensionByZeroRestrictAdjunction j).unit.app M) ≫
      (extensionByZeroRestrictAdjunction j).counit.app ((extensionByZero j).obj M) =
        𝟙 ((extensionByZero j).obj M) := by
  exact ⟨(asIso (extensionByZeroRestrictAdjunction j).unit).hom_inv_id_app M,
    (extensionByZeroRestrictAdjunction j).left_triangle_components M⟩

/-- No closedness of the point or separation condition is needed outside the open. -/
theorem outside_original_stalk {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (x : X) (hx : x ∉ Set.range j) (M : U.Modules) :
    𝟙 ((moduleStalk X x).obj ((extensionByZero j).obj M)) = 0 :=
  (IsZero.iff_id_eq_zero _).mp (isZero_extensionByZero_stalk_of_not_mem j x hx M)

/-- The actual free-generator flat cover extends to a flat sheaf with its original epic map. -/
theorem actual_flat_cover {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : U.Modules) :
    stalkwiseFlat X ((extensionByZero j).obj (flatCover M)) ∧
      Epi ((extensionByZero j).map (flatCoverπ M)) :=
  ⟨stalkwiseFlat_extensionByZero j (flatCover_stalkwiseFlat M), inferInstance⟩

/-- Actual scheme pullback, with the original base-change mate and its exact unit equation. -/
theorem actual_pullback_unit {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : U.Modules) :
    IsIso ((extensionByZeroBaseChange (pullback.fst j k) (pullback.snd j k) j k
      pullback.condition).app M) ∧
    (extensionByZeroRestrictAdjunction (pullback.snd j k)).unit.app
        ((Scheme.Modules.restrictFunctor (pullback.fst j k)).obj M) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
        ((extensionByZeroPullbackIso j k).hom.app M) =
    (extensionByZeroBaseChangeUnitIso (pullback.fst j k) (pullback.snd j k) j k
      pullback.condition).hom.app M := by
  refine ⟨?_, extensionByZeroBaseChange_unit _ _ j k pullback.condition M⟩
  change IsIso ((extensionByZeroPullbackIso j k).hom.app M)
  infer_instance

/-- Base-change counit compatibility holds on every original commuting square, before cartesianness.
  -/
theorem original_square_counits {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V)
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion a] [IsOpenImmersion b]
    [IsOpenImmersion j] [IsOpenImmersion k] (h : a ≫ j = b ≫ k) (M : X.Modules) :
    (extensionByZeroBaseChange a b j k h).app ((Scheme.Modules.restrictFunctor j).obj M) ≫
      (Scheme.Modules.restrictFunctor k).map ((extensionByZeroRestrictAdjunction j).counit.app M) =
    (extensionByZero b).map ((openSquareRestrictIso a b j k h).hom.app M) ≫
      (extensionByZeroRestrictAdjunction b).counit.app ((Scheme.Modules.restrictFunctor k).obj M) :=
  extensionByZeroBaseChange_counit a b j k h M

/-- Original composition counits retain all maps and actual scalar coherence. -/
theorem original_composite_counits {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] (M : X.Modules) :
    (extensionByZeroComp a j).hom.app ((Scheme.Modules.restrictFunctor (a ≫ j)).obj M) ≫
      (extensionByZero j).map ((extensionByZero a).map
        ((Scheme.Modules.restrictFunctorComp a j).hom.app M)) ≫
      (extensionByZero j).map ((extensionByZeroRestrictAdjunction a).counit.app
        ((Scheme.Modules.restrictFunctor j).obj M)) ≫
      (extensionByZeroRestrictAdjunction j).counit.app M =
    (extensionByZeroRestrictAdjunction (a ≫ j)).counit.app M :=
  extensionByZeroComp_hom_counit a j M

end QuillenTest.SheafExtensionByZero
