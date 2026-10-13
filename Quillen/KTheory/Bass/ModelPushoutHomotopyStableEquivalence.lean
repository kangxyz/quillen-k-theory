/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.ModelDiagramConnectivity
public import Quillen.Topology.Prespectrum.PushoutLinearExcision
public import Quillen.Topology.Prespectrum.PushoutHomotopySquareStableEquivalence

/-!
# Whole-track pushout stable preservation at actual model-diagram Bass stages

The original stage-i and stage-j model-diagram values have all-point linear growth with common
offset max i j and literal chosen-point HEP. These proofs discharge every intermediate row in
the unchanged mapOfHomotopies factorization. Only the three original stable corner maps and the
two supplied whole tracks remain; no strict-natural transformation is required.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i j : ℕ) (F G : C ⥤ Model.{w}) (X₀ X₁ X₂ Y₀ Y₁ Y₂ : C)
variable
  (f : ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X₀ ⟶
    ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X₁)
  (g : ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X₀ ⟶
    ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X₂)
  (f' : ((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).obj Y₀ ⟶
    ((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).obj Y₁)
  (g' : ((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).obj Y₀ ⟶
    ((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).obj Y₂)
  (a : ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X₀ ⟶
    ((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).obj Y₀)
  (b : ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X₁ ⟶
    ((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).obj Y₁)
  (c : ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X₂ ⟶
    ((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).obj Y₂)
  (Hf : Homotopy (f ≫ b) (a ≫ f')) (Hg : Homotopy (g ≫ c) (a ≫ g'))

/-- The original whole-track pushout map is stable from three actual stable stage corner maps. -/
theorem modelDiagramIterate_pushoutMapOfHomotopies_isStableEquivalence
    (ha : IsStableEquivalence a) (hb : IsStableEquivalence b) (hc : IsStableEquivalence c) :
    IsStableEquivalence (HomotopyPushout.mapOfHomotopies f g f' g' a b c Hf Hg) := by
  have hF (X : C) (m : ℕ) := modelDiagramIterate_point_homotopyExtensionProperty Q i F X m
  have hG (X : C) (m : ℕ) := modelDiagramIterate_point_homotopyExtensionProperty Q j G X m
  have hπF (X : C) (n : ℕ)
      (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space
        (n + max i j + 2))
      (k : ℕ) (hk : k < n + 2) :
      Subsingleton (HomotopyGroup.Pi k
        ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space
        (n + max i j + 2)) x) :=
    modelDiagramIterate_homotopyGroup_subsingleton_of_le Q i F X _
      (by omega) k (by omega) x
  have hπG (X : C) (n : ℕ)
      (x : (((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).obj X).space
        (n + max i j + 2))
      (k : ℕ) (hk : k < n + 2) :
      Subsingleton (HomotopyGroup.Pi k
        ((((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).obj X).space
        (n + max i j + 2)) x) :=
    modelDiagramIterate_homotopyGroup_subsingleton_of_le Q j G X _
      (by omega) k (by omega) x
  apply HomotopyPushout.mapOfHomotopies_isStableEquivalence_of_excision
    f g f' g' a b c Hf Hg
    (fun n ↦ hF X₀ _) (fun n ↦ hF X₁ _) (fun n ↦ hF X₂ _)
    (fun n ↦ hG Y₀ _) (fun n ↦ hG Y₁ _) (fun n ↦ hG Y₂ _)
  · exact mappingConeFiberComparison_isStableEquivalence_of_linearGrowth f (max i j)
      (fun n ↦ hF X₀ _) (fun n ↦ hF X₁ _) (hπF X₀) (hπF X₁)
  · exact mappingConeFiberComparison_isStableEquivalence_of_linearGrowth (f ≫ b) (max i j)
      (fun n ↦ hF X₀ _) (fun n ↦ hG Y₁ _) (hπF X₀) (hπG Y₁)
  · exact mappingConeFiberComparison_isStableEquivalence_of_linearGrowth (a ≫ f') (max i j)
      (fun n ↦ hF X₀ _) (fun n ↦ hG Y₁ _) (hπF X₀) (hπG Y₁)
  · exact mappingConeFiberComparison_isStableEquivalence_of_linearGrowth f' (max i j)
      (fun n ↦ hG Y₀ _) (fun n ↦ hG Y₁ _) (hπG Y₀) (hπG Y₁)
  · exact HomotopyPushout.inr_coneFiber_isStableEquivalence_of_linearGrowth f g (max i j)
      (fun n ↦ hF X₀ _) (fun n ↦ hF X₁ _) (fun n ↦ hF X₂ _)
      (hπF X₀) (hπF X₁) (hπF X₂)
  · exact HomotopyPushout.inr_coneFiber_isStableEquivalence_of_linearGrowth
      (f ≫ b) (g ≫ c) (max i j)
      (fun n ↦ hF X₀ _) (fun n ↦ hG Y₁ _) (fun n ↦ hG Y₂ _)
      (hπF X₀) (hπG Y₁) (hπG Y₂)
  · exact HomotopyPushout.inr_coneFiber_isStableEquivalence_of_linearGrowth
      (a ≫ f') (a ≫ g') (max i j)
      (fun n ↦ hF X₀ _) (fun n ↦ hG Y₁ _) (fun n ↦ hG Y₂ _)
      (hπF X₀) (hπG Y₁) (hπG Y₂)
  · exact HomotopyPushout.inr_coneFiber_isStableEquivalence_of_linearGrowth f' g' (max i j)
      (fun n ↦ hG Y₀ _) (fun n ↦ hG Y₁ _) (fun n ↦ hG Y₂ _)
      (hπG Y₀) (hπG Y₁) (hπG Y₂)
  · exact ha
  · exact hb
  · exact hc

end Quillen.KTheory.Bass
