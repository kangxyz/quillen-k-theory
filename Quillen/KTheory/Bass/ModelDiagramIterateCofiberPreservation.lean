/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictDiagramIterateNull
public import Quillen.KTheory.Bass.ModelDiagramCofiberBoundary

/-!
# Original cofiber localization comparisons through every finite Bass iterate

Starting with the original stable cone descent, every actual finite iterate carries the
recursively specified original Bass null action. The equality-induced successor isomorphisms
transport its actual cone descent; they preserve stable equivalences as genuine isomorphisms.
The one-step theorem discharges all point topology and excision from the finite original Model
stages, so the induction requires only the initial geometric cone comparison. No seed
compatibility or finite-stage stabilization is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (F G K : C ⥤ Model.{w}) (a : F ⋙ prespectrumFunctor ⟶ G ⋙ prespectrumFunctor)
    (b : G ⋙ prespectrumFunctor ⟶ K ⋙ prespectrumFunctor)
    (H : DiagramNullHomotopy a b)

/-- The original stable cofiber comparison stays stable at every unchanged finite Bass stage. -/
theorem modelDiagramIterateCofiberDesc_isStableEquivalence
    (hdesc : ∀ X, IsStableEquivalence
      (mappingConeDesc (a.app X) (b.app X) (H.homotopy X))) (n : ℕ) (X : C) :
    IsStableEquivalence (mappingConeDesc (((strictDiagramIterate Q n).map a).app X)
      (((strictDiagramIterate Q n).map b).app X)
      ((strictDiagramIterateNull Q H n).homotopy X)) := by
  induction n generalizing X with
  | zero => exact hdesc X
  | succ n ih =>
    rw [strictDiagramIterateNull_succ_coneDesc]
    have he : IsStableEquivalence (strictDiagramSuccessorConeIso Q (a := a) n X).hom := by
      intro d
      infer_instance
    have hb := modelDiagramCofiberDesc_bass_isStableEquivalence Q n n F G
      ((strictDiagramIterate Q n).map a) n K ((strictDiagramIterate Q n).map b)
      (strictDiagramIterateNull Q H n).homotopy (strictDiagramIterateNull Q H n).naturality ih X
    have hk : IsStableEquivalence
        ((inv (strictDiagramSuccessorMap Q (K ⋙ prespectrumFunctor) n)).app X) := by
      intro d
      infer_instance
    exact he.comp (hb.comp hk)

/-- Actual finite-stage point HEP and growth give excision for the original iterated arrow. -/
theorem modelDiagramIterateArrow_coneFiber_isStableEquivalence (n : ℕ) (X : C) :
    IsStableEquivalence (mappingConeFiberComparison (((strictDiagramIterate Q n).map a).app X)) :=
  mappingConeFiberComparison_isStableEquivalence_of_linearGrowth _ n
    (fun m ↦ modelDiagramIterate_point_homotopyExtensionProperty Q n F X (m + n + 2))
    (fun m ↦ modelDiagramIterate_point_homotopyExtensionProperty Q n G X (m + n + 2))
    (fun m x k hk ↦ modelDiagramIterate_homotopyGroup_subsingleton_at Q n F X m k hk x)
    (fun m x k hk ↦ modelDiagramIterate_homotopyGroup_subsingleton_at Q n G X m k hk x)

/-- Every original finite-stage null descent carries its unchanged signed cone boundary. -/
theorem modelDiagramIterateCofiberDesc_connecting (n : ℕ) (X : C) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        (mappingConeDesc (((strictDiagramIterate Q n).map a).app X)
          (((strictDiagramIterate Q n).map b).app X)
          ((strictDiagramIterateNull Q H n).homotopy X)) ≫
      stableFiberConnecting (((strictDiagramIterate Q n).map b).app X) d =
    stableMappingConeConnecting (((strictDiagramIterate Q n).map a).app X)
      (modelDiagramIterateArrow_coneFiber_isStableEquivalence Q F G a n X) d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift
          (((strictDiagramIterate Q n).map b).app X) (((strictDiagramIterate Q n).map a).app X)
          ((strictDiagramIterateNull Q H n).homotopy X)) :=
  mappingConeDesc_connecting _ _ _
    (modelDiagramIterateArrow_coneFiber_isStableEquivalence Q F G a n X) d

end Quillen.KTheory.Bass
