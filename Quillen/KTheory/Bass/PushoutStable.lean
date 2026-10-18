/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.PushoutCofiberSquare
public import Quillen.KTheory.Bass.ModelDiagramConnectivity
public import Quillen.KTheory.Bass.StrictDiagramStableEquivalence
public import Quillen.Topology.Prespectrum.PositiveLevelEquivalence
public import Quillen.Topology.Prespectrum.PushoutLinearExcision

/-!
# Stability of the actual forward Bass pushout comparison

The positive cone square reduces the actual comparison to genuine right-cone
collapses and actual Bass cofiber comparisons. All auxiliary growth and point
HEP are derived from the three original diagrams. Finite Model diagrams supply
these hypotheses without any new topological or coherence assumption.

This is an adopted independent reconstruction after workspace loss, not historical byte recovery.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass.PushoutStable
open PushoutStrength PushoutCofiberSquare
variable {C : Type u} [Category.{v} C]

private abbrev PointHEP (F : C ⥤ LoopPrespectrum.{w}) :=
  ∀ X n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point n)))

private abbrev Growth (F : C ⥤ LoopPrespectrum.{w}) (c : ℕ) :=
  ∀ X n k, k < n + 2 → ∀ x : (F.obj X).space (n + c + 2),
    Subsingleton (HomotopyGroup.Pi k ((F.obj X).space (n + c + 2)) x)

private theorem cone_hep {F G : C ⥤ LoopPrespectrum.{w}} (f : F ⟶ G)
    (hF : PointHEP F) (hG : PointHEP G) : PointHEP (mappingConeDiagram f) :=
  fun X n => ReducedMappingCone.point_homotopyExtensionProperty _ _ _
    ((f.app X).map_point n) (hF X n) (hG X n)

private theorem cone_growth {F G : C ⥤ LoopPrespectrum.{w}} (f : F ⟶ G)
    (hF : PointHEP F) (hG : PointHEP G) (c : ℕ)
    (hπF : Growth F c) (hπG : Growth G c) : Growth (mappingConeDiagram f) c := by
  intro X n k hk x
  exact ReducedMappingCone.homotopyGroup_subsingleton _ _ _ ((f.app X).map_point _)
    (hF X _) (hG X _) n (fun y t ht => hπF X n t ht y)
    (fun y t ht => hπG X n t ht y) x k hk

private theorem pushout_hep {F₀ F₁ F₂ : C ⥤ LoopPrespectrum.{w}}
    (f : F₀ ⟶ F₁) (g : F₀ ⟶ F₂)
    (h₀ : PointHEP F₀) (h₁ : PointHEP F₁) (h₂ : PointHEP F₂) :
    PointHEP (pushout f g) := fun X n =>
  HomotopyPushout.point_homotopyExtensionProperty _ _ n (h₀ X n) (h₁ X n) (h₂ X n)

private theorem pushout_growth {F₀ F₁ F₂ : C ⥤ LoopPrespectrum.{w}}
    (f : F₀ ⟶ F₁) (g : F₀ ⟶ F₂)
    (h₀ : PointHEP F₀) (h₁ : PointHEP F₁) (h₂ : PointHEP F₂) (c : ℕ)
    (hπ₀ : Growth F₀ c) (hπ₁ : Growth F₁ c) (hπ₂ : Growth F₂ c) :
    Growth (pushout f g) c := by
  intro X n k hk x
  exact HomotopyPushout.homotopyGroup_subsingleton _ _ _ n
    (h₀ X _) (h₁ X _) (h₂ X _) (fun y t ht => hπ₀ X n t ht y)
    (fun y t ht => hπ₁ X n t ht y) (fun y t ht => hπ₂ X n t ht y) x k hk

private theorem squareCone_t1 (F : C ⥤ LoopPrespectrum.{w})
    [∀ X n, T1Space ((F.obj X).space n)] (S : Arrow (Arrow C)) (n : ℕ) :
    T1Space ((mappingCone (StrictSquare.comparison (F.mapArrow.mapArrow.obj S))).space n) := by
  let T := F.mapArrow.mapArrow.obj S
  let : T1Space (T.left.left.space n) := inferInstanceAs (T1Space ((F.obj S.left.left).space n))
  let : T1Space (T.left.right.space n) := inferInstanceAs (T1Space ((F.obj S.left.right).space n))
  let : T1Space (T.right.left.space n) := inferInstanceAs (T1Space ((F.obj S.right.left).space n))
  let : T1Space (T.right.right.space n) := inferInstanceAs (T1Space ((F.obj S.right.right).space n))
  change T1Space ((mappingCone (StrictSquare.comparison T)).space n)
  infer_instance

private theorem squareCone_growth (F : C ⥤ LoopPrespectrum.{w})
    (h : PointHEP F) (c : ℕ) (hπ : Growth F c) (S : Arrow (Arrow C))
    (n : ℕ) (x : (mappingCone (StrictSquare.comparison
      (F.mapArrow.mapArrow.obj S))).space (n + c + 2)) (k : ℕ) (hk : k < n + 2) :
    Subsingleton (HomotopyGroup.Pi k ((mappingCone (StrictSquare.comparison
      (F.mapArrow.mapArrow.obj S))).space (n + c + 2)) x) :=
  ReducedMappingCone.homotopyGroup_subsingleton _ _ _
    ((StrictSquare.comparison (F.mapArrow.mapArrow.obj S)).map_point _)
    (StrictSquare.span_point_homotopyExtensionProperty _ _
      (h S.left.left _) (h S.left.right _) (h S.right.left _)) (h S.right.right _) n
    (HomotopyPushout.homotopyGroup_subsingleton _ _ _ n
      (h S.left.left _) (h S.left.right _) (h S.right.left _)
      (fun y t ht => hπ S.left.left n t ht y)
      (fun y t ht => hπ S.left.right n t ht y)
      (fun y t ht => hπ S.right.left n t ht y))
    (fun y t ht => hπ S.right.right n t ht y) x k hk

private theorem cofiber_stable (Q : C ⥤ Arrow (Arrow C))
    {F G : C ⥤ LoopPrespectrum.{w}} [∀ X n, T1Space ((F.obj X).space n)]
    [∀ X n, T1Space ((G.obj X).space n)] (f : F ⟶ G)
    (hF : PointHEP F) (hG : PointHEP G) (c : ℕ) (hπF : Growth F c) (hπG : Growth G c)
    (X : C) : IsStableEquivalence ((strictDiagramCofiberComparison Q f).app X) := by
  let : ∀ n, T1Space ((mappingCone (StrictSquare.comparison
      (F.mapArrow.mapArrow.obj (Q.obj X)))).space n) := squareCone_t1 F (Q.obj X)
  let : ∀ n, T1Space ((mappingCone (StrictSquare.comparison
      (G.mapArrow.mapArrow.obj (Q.obj X)))).space n) := squareCone_t1 G (Q.obj X)
  apply StrictSquare.loopedConeCofiberComparison_isStableEquivalence_of_linearGrowth
    (diagramSquareMap f (Q.obj X)) c
  · exact fun n => StrictSquare.cone_point_homotopyExtensionProperty _ n
      (hF (Q.obj X).left.left n) (hF (Q.obj X).left.right n)
      (hF (Q.obj X).right.left n) (hF (Q.obj X).right.right n)
  · exact fun n => StrictSquare.cone_point_homotopyExtensionProperty _ n
      (hG (Q.obj X).left.left n) (hG (Q.obj X).left.right n)
      (hG (Q.obj X).right.left n) (hG (Q.obj X).right.right n)
  · exact squareCone_growth F hF c hπF (Q.obj X)
  · exact squareCone_growth G hG c hπG (Q.obj X)

/-- Genuine original growth and topology imply stability of the unchanged forward comparison. -/
theorem comparison_isStableEquivalence_of_linearGrowth
    {F₀ F₁ F₂ : C ⥤ LoopPrespectrum.{w}}
    (f : F₀ ⟶ F₁) (g : F₀ ⟶ F₂) (Q : C ⥤ Arrow (Arrow C))
    [∀ X n, T1Space ((F₀.obj X).space n)]
    [∀ X n, T1Space ((F₁.obj X).space n)]
    [∀ X n, T1Space ((F₂.obj X).space n)]
    (h₀ : ∀ Y n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F₀.obj Y).point n))))
    (h₁ : ∀ Y n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F₁.obj Y).point n))))
    (h₂ : ∀ Y n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F₂.obj Y).point n)))) (c : ℕ)
    (hπ₀ : ∀ Y n k, k < n + 2 → ∀ x : (F₀.obj Y).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F₀.obj Y).space (n + c + 2)) x))
    (hπ₁ : ∀ Y n k, k < n + 2 → ∀ x : (F₁.obj Y).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F₁.obj Y).space (n + c + 2)) x))
    (hπ₂ : ∀ Y n k, k < n + 2 → ∀ x : (F₂.obj Y).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F₂.obj Y).space (n + c + 2)) x)) (X : C) :
    IsStableEquivalence (comparison f g Q X) := by
  let B := strictDiagramFunctor Q
  have hP := pushout_hep f g h₀ h₁ h₂
  have hπP := pushout_growth f g h₀ h₁ h₂ c hπ₀ hπ₁ hπ₂
  let : ∀ Y n, T1Space (((pushout f g).obj Y).space n) := fun Y n =>
    inferInstanceAs (T1Space ((HomotopyPushout.prespectrum (f.app Y) (g.app Y)).space n))
  have hk : ∀ Y, IsStableEquivalence ((coneCollapse f g).app Y) := fun Y =>
    isStableEquivalence_of_positiveLevel _ (fun n =>
      HomotopyPushout.rightConeCollapse_level_isWeakHomotopyEquivalence _ _ (n + 1)
        (h₀ Y _) (h₁ Y _) (h₂ Y _))
  have hBk : IsStableEquivalence ((B.map (coneCollapse f g)).app X) :=
    strictDiagramFunctor_map_isStableEquivalence_of_linearGrowth Q
      (mappingConeDiagram (right f g)) (mappingConeDiagram f)
      (cone_hep (right f g) h₂ hP) (cone_hep f h₀ h₁) c c
      (cone_growth (right f g) h₂ hP c hπ₂ hπP) (cone_growth f h₀ h₁ c hπ₀ hπ₁)
      (coneCollapse f g) hk X
  have hB₀ := strictDiagramFunctor_point_homotopyExtensionProperty Q F₀ h₀
  have hB₁ := strictDiagramFunctor_point_homotopyExtensionProperty Q F₁ h₁
  have hB₂ := strictDiagramFunctor_point_homotopyExtensionProperty Q F₂ h₂
  have hBP := strictDiagramFunctor_point_homotopyExtensionProperty Q (pushout f g) hP
  have hπB₀ := strictDiagramFunctor_homotopyGroup_subsingleton Q F₀ h₀ c hπ₀
  have hπB₁ := strictDiagramFunctor_homotopyGroup_subsingleton Q F₁ h₁ c hπ₁
  have hπB₂ := strictDiagramFunctor_homotopyGroup_subsingleton Q F₂ h₂ c hπ₂
  have hπBP := strictDiagramFunctor_homotopyGroup_subsingleton Q (pushout f g) hP c hπP
  have hk' : IsStableEquivalence
      (HomotopyPushout.rightConeCollapse ((B.map f).app X) ((B.map g).app X)) :=
    isStableEquivalence_of_positiveLevel _ (fun n =>
      HomotopyPushout.rightConeCollapse_level_isWeakHomotopyEquivalence _ _ (n + 1)
        (hB₀ X _) (hB₁ X _) (hB₂ X _))
  have hνf := cofiber_stable Q f h₀ h₁ c hπ₀ hπ₁ X
  have hνj := cofiber_stable Q (right f g) h₂ hP c hπ₂ hπP X
  have hcomp := hk'.comp hνf
  rw [← coneSquare f g Q X] at hcomp
  have hcone : IsStableEquivalence (mappingConeMap (rightSquare f g Q X)) := by
    intro d
    let := hνj d
    let := hBk d
    let : IsIso ((stableHomotopyFunctor d).map (mappingConeMap (rightSquare f g Q X)) ≫
        (stableHomotopyFunctor d).map ((strictDiagramCofiberComparison Q (right f g)).app X) ≫
          (stableHomotopyFunctor d).map ((B.map (coneCollapse f g)).app X)) := by
      simpa only [CategoryTheory.Functor.map_comp] using hcomp d
    exact IsIso.of_isIso_comp_right
      ((stableHomotopyFunctor d).map (mappingConeMap (rightSquare f g Q X)))
      ((stableHomotopyFunctor d).map ((strictDiagramCofiberComparison Q (right f g)).app X) ≫
        (stableHomotopyFunctor d).map ((B.map (coneCollapse f g)).app X))
  apply right_isStableEquivalence_of_coneMap (rightSquare f g Q X) _ _ _ hcone
  · exact HomotopyPushout.inr_coneFiber_isStableEquivalence_of_linearGrowth
      ((B.map f).app X) ((B.map g).app X) (c + 1)
      (fun n => hB₀ X _) (fun n => hB₁ X _) (fun n => hB₂ X _)
      (fun n x k hk => hπB₀ X n k hk x)
      (fun n x k hk => hπB₁ X n k hk x)
      (fun n x k hk => hπB₂ X n k hk x)
  · exact mappingConeFiberComparison_isStableEquivalence_of_linearGrowth
      ((B.map (right f g)).app X) (c + 1) (fun n => hB₂ X _) (fun n => hBP X _)
      (fun n x k hk => hπB₂ X n k hk x) (fun n x k hk => hπBP X n k hk x)
  · intro d
    change IsIso ((stableHomotopyFunctor d).map (𝟙 _))
    infer_instance

/-- All hypotheses are supplied by the original finite Model diagrams themselves. -/
theorem modelIterate_comparison_isStableEquivalence
    (Q : C ⥤ Arrow (Arrow C)) (i : ℕ) (M₀ M₁ M₂ : C ⥤ Model.{w})
    (f : (strictDiagramIterate Q i).obj (M₀ ⋙ prespectrumFunctor) ⟶
      (strictDiagramIterate Q i).obj (M₁ ⋙ prespectrumFunctor))
    (g : (strictDiagramIterate Q i).obj (M₀ ⋙ prespectrumFunctor) ⟶
      (strictDiagramIterate Q i).obj (M₂ ⋙ prespectrumFunctor)) (X : C) :
    IsStableEquivalence (comparison f g Q X) :=
  comparison_isStableEquivalence_of_linearGrowth f g Q
    (modelDiagramIterate_point_homotopyExtensionProperty Q i M₀)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i M₁)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i M₂) i
    (fun Y n k hk x => modelDiagramIterate_homotopyGroup_subsingleton_at Q i M₀ Y n k hk x)
    (fun Y n k hk x => modelDiagramIterate_homotopyGroup_subsingleton_at Q i M₁ Y n k hk x)
    (fun Y n k hk x => modelDiagramIterate_homotopyGroup_subsingleton_at Q i M₂ Y n k hk x) X

end Quillen.KTheory.Bass.PushoutStable
