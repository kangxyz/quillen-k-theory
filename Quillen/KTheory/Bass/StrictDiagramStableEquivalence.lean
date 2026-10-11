/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictDiagramVanishing
public import Quillen.Topology.Prespectrum.ConeLinearExcision
public import Quillen.Topology.Prespectrum.PushoutStableEquivalence
public import Quillen.Topology.Prespectrum.StrictSquareStableEquivalence

/-!
# Stable preservation for original strict Bass diagrams with proved linear growth

The actual corner growth and point HEP discharge original span and comparison cone excision.
The unchanged Bass endofunctor therefore preserves objectwise stable original transformations.
The genuine finite-iteration topology and vanishing closure propagate these inputs, so the
same original transformed arrow stays stable through every iterate. Initial hypotheses remain
explicit here and are discharged for original iterated-S model diagrams in their own owner.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C]

/-- Actual comparison rows have stable cone excision from original point HEP and linear growth. -/
theorem strictDiagramComparison_coneFiber_isStableEquivalence_of_linearGrowth
    (F : C ⥤ LoopPrespectrum.{w}) (S : Arrow (Arrow C))
    (h : ∀ X m, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m)))) (c : ℕ)
    (hπ : ∀ X n k, k < n + 2 → ∀ x : (F.obj X).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F.obj X).space (n + c + 2)) x)) :
    IsStableEquivalence (mappingConeFiberComparison
      (StrictSquare.comparison (F.mapArrow.mapArrow.obj S))) := by
  apply mappingConeFiberComparison_isStableEquivalence_of_linearGrowth _ c
  · intro n
    exact HomotopyPushout.point_homotopyExtensionProperty _ _ _
      (h S.left.left _) (h S.left.right _) (h S.right.left _)
  · exact fun n ↦ h S.right.right _
  · intro n x k hk
    exact HomotopyPushout.homotopyGroup_subsingleton _ _ _ n
      (h S.left.left _) (h S.left.right _) (h S.right.left _)
      (fun a t ht ↦ hπ S.left.left n t ht a)
      (fun b t ht ↦ hπ S.left.right n t ht b)
      (fun d t ht ↦ hπ S.right.left n t ht d) x k hk
  · exact fun n x k hk ↦ hπ S.right.right n k hk x

private theorem spanInr_coneFiber_stable (F : C ⥤ LoopPrespectrum.{w})
    (S : Arrow (Arrow C))
    (h : ∀ X m, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m)))) (c : ℕ)
    (hπ : ∀ X n k, k < n + 2 → ∀ x : (F.obj X).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F.obj X).space (n + c + 2)) x)) :
    IsStableEquivalence (mappingConeFiberComparison
      (HomotopyPushout.inr (F.map S.left.hom) (F.map S.hom.left))) := by
  apply mappingConeFiberComparison_isStableEquivalence_of_linearGrowth _ c
  · exact fun n ↦ h S.right.left _
  · intro n
    exact HomotopyPushout.point_homotopyExtensionProperty _ _ _
      (h S.left.left _) (h S.left.right _) (h S.right.left _)
  · exact fun n x k hk ↦ hπ S.right.left n k hk x
  · intro n x k hk
    exact HomotopyPushout.homotopyGroup_subsingleton _ _ _ n
      (h S.left.left _) (h S.left.right _) (h S.right.left _)
      (fun a t ht ↦ hπ S.left.left n t ht a)
      (fun b t ht ↦ hπ S.left.right n t ht b)
      (fun d t ht ↦ hπ S.right.left n t ht d) x k hk

/-- Actual Bass preserves original stable transformations under explicit initial growth. -/
theorem strictDiagramFunctor_map_isStableEquivalence_of_linearGrowth
    (Q : C ⥤ Arrow (Arrow C)) (F G : C ⥤ LoopPrespectrum.{w})
    (hF : ∀ X m, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m))))
    (hG : ∀ X m, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((G.obj X).point m))))
    (c d : ℕ)
    (hπF : ∀ X n k, k < n + 2 → ∀ x : (F.obj X).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F.obj X).space (n + c + 2)) x))
    (hπG : ∀ X n k, k < n + 2 → ∀ x : (G.obj X).space (n + d + 2),
      Subsingleton (HomotopyGroup.Pi k ((G.obj X).space (n + d + 2)) x))
    (η : F ⟶ G) (hη : ∀ X, IsStableEquivalence (η.app X)) (X : C) :
    IsStableEquivalence (((strictDiagramFunctor Q).map η).app X) := by
  let a := ((Functor.mapArrowFunctor (Arrow C) (Arrow LoopPrespectrum)).map
    ((Functor.mapArrowFunctor C LoopPrespectrum).map η)).app (Q.obj X)
  apply strictSquareLoopedConeFunctor_map_isStableEquivalence_of_excision a
    (strictDiagramComparison_coneFiber_isStableEquivalence_of_linearGrowth F (Q.obj X) hF c hπF)
    (strictDiagramComparison_coneFiber_isStableEquivalence_of_linearGrowth G (Q.obj X) hG d hπG)
    _ (hη _)
  apply HomotopyPushout.map_isStableEquivalence_of_excision _ _ _ _ _ _ _ _ _
    (fun n ↦ hF (Q.obj X).left.left _) (fun n ↦ hF (Q.obj X).left.right _)
    (fun n ↦ hF (Q.obj X).right.left _) (fun n ↦ hG (Q.obj X).left.left _)
    (fun n ↦ hG (Q.obj X).left.right _) (fun n ↦ hG (Q.obj X).right.left _)
  · exact mappingConeFiberComparison_isStableEquivalence_of_linearGrowth _ c
      (fun n ↦ hF (Q.obj X).left.left _) (fun n ↦ hF (Q.obj X).left.right _)
      (fun n x k hk ↦ hπF (Q.obj X).left.left n k hk x)
      (fun n x k hk ↦ hπF (Q.obj X).left.right n k hk x)
  · exact mappingConeFiberComparison_isStableEquivalence_of_linearGrowth _ d
      (fun n ↦ hG (Q.obj X).left.left _) (fun n ↦ hG (Q.obj X).left.right _)
      (fun n x k hk ↦ hπG (Q.obj X).left.left n k hk x)
      (fun n x k hk ↦ hπG (Q.obj X).left.right n k hk x)
  · exact spanInr_coneFiber_stable F (Q.obj X) hF c hπF
  · exact spanInr_coneFiber_stable G (Q.obj X) hG d hπG
  · exact hη _
  · exact hη _
  · exact hη _

/-- Every original iterate preserves the same stable arrow, using proved topology/growth closure. -/
theorem strictDiagramIterate_map_isStableEquivalence_of_linearGrowth
    (Q : C ⥤ Arrow (Arrow C)) (i : ℕ) (F G : C ⥤ LoopPrespectrum.{w})
    [∀ X m, T1Space ((F.obj X).space m)] [∀ X m, T1Space ((G.obj X).space m)]
    (hF : ∀ X m, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m))))
    (hG : ∀ X m, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((G.obj X).point m))))
    (c d : ℕ)
    (hπF : ∀ X n k, k < n + 2 → ∀ x : (F.obj X).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F.obj X).space (n + c + 2)) x))
    (hπG : ∀ X n k, k < n + 2 → ∀ x : (G.obj X).space (n + d + 2),
      Subsingleton (HomotopyGroup.Pi k ((G.obj X).space (n + d + 2)) x))
    (η : F ⟶ G) (hη : ∀ X, IsStableEquivalence (η.app X)) (X : C) :
    IsStableEquivalence (((strictDiagramIterate Q i).map η).app X) := by
  induction i generalizing F G c d with
  | zero => exact hη X
  | succ i ih =>
    exact ih ((strictDiagramFunctor Q).obj F) ((strictDiagramFunctor Q).obj G)
      (strictDiagramFunctor_point_homotopyExtensionProperty Q F hF)
      (strictDiagramFunctor_point_homotopyExtensionProperty Q G hG) (c + 1) (d + 1)
      (strictDiagramFunctor_homotopyGroup_subsingleton Q F hF c hπF)
      (strictDiagramFunctor_homotopyGroup_subsingleton Q G hG d hπG)
      ((strictDiagramFunctor Q).map η)
      (strictDiagramFunctor_map_isStableEquivalence_of_linearGrowth Q F G hF hG c d hπF hπG η hη)

end Quillen.KTheory.Bass
