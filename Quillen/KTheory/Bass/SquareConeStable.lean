/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SquareConeStrength
public import Quillen.KTheory.Bass.PushoutStable

/-!
# Actual square cone strength is stable on finite Model stages

The original natural chi is the strict cone map with rho and identity sides,
followed by the forward cofiber comparison. Every required excision, point HEP,
T1 property and linear-growth estimate is derived from genuine finite Model
stages and their actual pushout diagrams. No future stability is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass.SquareConeStable
open PushoutStrength SquareConeStrength
variable {C : Type u} [Category.{v} C]

private abbrev PointHEP (F : C ⥤ LoopPrespectrum.{w}) :=
  ∀ X n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point n)))

private abbrev Growth (F : C ⥤ LoopPrespectrum.{w}) (c : ℕ) :=
  ∀ X n k, k < n + 2 → ∀ x : (F.obj X).space (n + c + 2),
    Subsingleton (HomotopyGroup.Pi k ((F.obj X).space (n + c + 2)) x)

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

/-- Apply the original prespectrum and finite Bass iterate to an actual strict Model square. -/
def modelSquare (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (M : Arrow (Arrow (C ⥤ Model.{w}))) : Arrow (Arrow (C ⥤ LoopPrespectrum.{w})) :=
  ((Functor.whiskeringRight C Model LoopPrespectrum).obj prespectrumFunctor ⋙
    strictDiagramIterate Q i).mapArrow.mapArrow.obj M

/-- The actual natural chi is stable at every genuine finite Model stage. -/
theorem modelSquare_chi_isStableEquivalence (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (M : Arrow (Arrow (C ⥤ Model.{w}))) (X : C) :
    IsStableEquivalence ((chi (modelSquare Q i M) Q).app X) := by
  let S := modelSquare Q i M
  let B := strictDiagramFunctor Q
  have h₀ : PointHEP S.left.left :=
    modelDiagramIterate_point_homotopyExtensionProperty Q i M.left.left
  have h₁ : PointHEP S.left.right :=
    modelDiagramIterate_point_homotopyExtensionProperty Q i M.left.right
  have h₂ : PointHEP S.right.left :=
    modelDiagramIterate_point_homotopyExtensionProperty Q i M.right.left
  have h₃ : PointHEP S.right.right :=
    modelDiagramIterate_point_homotopyExtensionProperty Q i M.right.right
  have hπ₀ : Growth S.left.left i :=
    fun Y n k hk x => modelDiagramIterate_homotopyGroup_subsingleton_at
      Q i M.left.left Y n k hk x
  have hπ₁ : Growth S.left.right i :=
    fun Y n k hk x => modelDiagramIterate_homotopyGroup_subsingleton_at
      Q i M.left.right Y n k hk x
  have hπ₂ : Growth S.right.left i :=
    fun Y n k hk x => modelDiagramIterate_homotopyGroup_subsingleton_at
      Q i M.right.left Y n k hk x
  have hπ₃ : Growth S.right.right i :=
    fun Y n k hk x => modelDiagramIterate_homotopyGroup_subsingleton_at
      Q i M.right.right Y n k hk x
  let : ∀ Y n, T1Space ((S.left.left.obj Y).space n) :=
    modelDiagramIterateSpaceT1Space Q i M.left.left
  let : ∀ Y n, T1Space ((S.left.right.obj Y).space n) :=
    modelDiagramIterateSpaceT1Space Q i M.left.right
  let : ∀ Y n, T1Space ((S.right.left.obj Y).space n) :=
    modelDiagramIterateSpaceT1Space Q i M.right.left
  let : ∀ Y n, T1Space ((S.right.right.obj Y).space n) :=
    modelDiagramIterateSpaceT1Space Q i M.right.right
  have hP := pushout_hep S.left.hom S.hom.left h₀ h₁ h₂
  have hπP := pushout_growth S.left.hom S.hom.left h₀ h₁ h₂ i hπ₀ hπ₁ hπ₂
  let : ∀ Y n, T1Space (((pushout S.left.hom S.hom.left).obj Y).space n) :=
    fun Y n => inferInstanceAs
      (T1Space ((HomotopyPushout.prespectrum (S.left.hom.app Y) (S.hom.left.app Y)).space n))
  have hν := cofiber_stable Q (comparison S) hP h₃ i hπP hπ₃ X
  have hB₀ := strictDiagramFunctor_point_homotopyExtensionProperty Q S.left.left h₀
  have hB₁ := strictDiagramFunctor_point_homotopyExtensionProperty Q S.left.right h₁
  have hB₂ := strictDiagramFunctor_point_homotopyExtensionProperty Q S.right.left h₂
  have hB₃ := strictDiagramFunctor_point_homotopyExtensionProperty Q S.right.right h₃
  have hBP := strictDiagramFunctor_point_homotopyExtensionProperty Q
    (pushout S.left.hom S.hom.left) hP
  have hπB₀ := strictDiagramFunctor_homotopyGroup_subsingleton Q S.left.left h₀ i hπ₀
  have hπB₁ := strictDiagramFunctor_homotopyGroup_subsingleton Q S.left.right h₁ i hπ₁
  have hπB₂ := strictDiagramFunctor_homotopyGroup_subsingleton Q S.right.left h₂ i hπ₂
  have hπB₃ := strictDiagramFunctor_homotopyGroup_subsingleton Q S.right.right h₃ i hπ₃
  have hπBP := strictDiagramFunctor_homotopyGroup_subsingleton Q
    (pushout S.left.hom S.hom.left) hP i hπP
  have hPBS := pushout_hep (B.map S.left.hom) (B.map S.hom.left) hB₀ hB₁ hB₂
  have hπPBS := pushout_growth (B.map S.left.hom) (B.map S.hom.left)
    hB₀ hB₁ hB₂ (i + 1) hπB₀ hπB₁ hπB₂
  let sq := (ArrowDiagrams.toDiagram.map (comparisonArrow S Q)).app X
  have hsource := mappingConeFiberComparison_isStableEquivalence_of_linearGrowth
    ((comparison (bassSquare S Q)).app X) (i + 1)
    (fun _ => hPBS X _) (fun _ => hB₃ X _)
    (fun n x k hk => hπPBS X n k hk x) (fun n x k hk => hπB₃ X n k hk x)
  have htarget := mappingConeFiberComparison_isStableEquivalence_of_linearGrowth
    ((B.map (comparison S)).app X) (i + 1)
    (fun _ => hBP X _) (fun _ => hB₃ X _)
    (fun n x k hk => hπBP X n k hk x) (fun n x k hk => hπB₃ X n k hk x)
  have hρ : IsStableEquivalence sq.left :=
    PushoutStable.modelIterate_comparison_isStableEquivalence Q i
      M.left.left M.left.right M.right.left S.left.hom S.hom.left X
  have hid : IsStableEquivalence sq.right := by
    intro d
    change IsIso ((stableHomotopyFunctor d).map (𝟙 _))
    infer_instance
  have hcone := mappingConeMap_isStableEquivalence_of_excision sq hsource htarget hρ hid
  exact hcone.comp hν

end Quillen.KTheory.Bass.SquareConeStable
