/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.EndotransformationContractionNaturality

/-!
# The original contraction under both coefficient directions

These consumers keep the same zero endomorphism, two genuine coefficient maps, both comparison
times, the independent structure time and the actual degree-zero loop coordinate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Tests.GradingContractionNaturality

section TypedPrewhisker
variable {A V W : Model.{u}} (F : V ⟶ W) (P : A ⟶ V)

/-- The original prewhiskering, explicitly typed at the same composite Model arrow. -/
private def consumerPrewhiskerTyped (η : F.functor ⟶ F.functor) :
    (P ≫ F).functor ⟶ (P ≫ F).functor :=
  whiskerLeft P.functor η

/-- The typed alias is literally the original natural transformation. -/
private theorem consumerPrewhiskerTyped_eq (η : F.functor ⟶ F.functor) :
    consumerPrewhiskerTyped F P η = whiskerLeft P.functor η := rfl

/-- The original component weakness, at the explicit composite transformation type. -/
private theorem consumerPrewhiskerTyped_weak (η : F.functor ⟶ F.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X)) :
    ∀ X : A, W.waldhausen.weq ((consumerPrewhiskerTyped F P η).app X) :=
  fun X ↦ hη (P.functor.obj X)

/-- The named original zero-weakness proof uses exactly the same composite Model arrow. -/
private theorem consumerPrewhiskerTyped_zeroWeak
    (hz : ∀ X, W.waldhausen.weq
      ((modelZeroEndotransformation (V := V) (W := W) F).app X)) :
    ∀ X : A, W.waldhausen.weq
      ((modelZeroEndotransformation (V := A) (W := W) (P ≫ F)).app X) :=
  modelZeroEndotransformation_precomp_weak (V := V) (W := W) (T := A) F hz P
end TypedPrewhisker

variable {A V W T : Model.{u}} (F : V ⟶ W) (P : A ⟶ V) (Q : W ⟶ T)
  (η : F.functor ⟶ F.functor) (hη : ∀ X, W.waldhausen.weq (η.app X))
  (hz : ∀ X, W.waldhausen.weq ((modelZeroEndotransformation (V := V) (W := W) F).app X))

/-- The coefficient map carries exactly the original zero endomorphism to the chosen one. -/
theorem original_zero_component (X : V) :
    Q.functor.map ((modelZeroEndotransformation (V := V) (W := W) F).app X) =
      (modelZeroEndotransformation (V := V) (W := T) (F ≫ Q)).app X :=
  congrArg (fun α : (F ≫ Q).functor ⟶ (F ≫ Q).functor ↦ α.app X)
    (modelZeroEndotransformation_postcomp (V := V) (W := W) (T := T) F Q)

/-- Both coefficient directions retain the same two-time cancellation family. -/
private theorem original_post_on_typed_precomposite (n : ℕ) (r s : unitInterval)
    (x : (prespectrum A).space n) :
    (prespectrumEndotransformationContraction (V := A) (W := T) ((P ≫ F) ≫ Q)
      (whiskerRight (consumerPrewhiskerTyped F P η) Q.functor)
      (fun X ↦ Q.exact.weak _ (consumerPrewhiskerTyped_weak F P η hη X))
      (modelZeroEndotransformation_postcomp_weak (V := A) (W := W) (T := T) (P ≫ F)
        (fun X ↦ hz (P.functor.obj X)) Q)).level n (r, (s, x)) =
      (prespectrumMap (V := W) (W := T) Q).map n
        ((prespectrumEndotransformationContraction (V := A) (W := W) (P ≫ F)
          (consumerPrewhiskerTyped F P η) (consumerPrewhiskerTyped_weak F P η hη)
          (consumerPrewhiskerTyped_zeroWeak F P hz)).level n (r, (s, x))) := by
  exact prespectrumEndotransformationContraction_postcomp_level
    (V := A) (W := W) (T := T) (P ≫ F)
    (consumerPrewhiskerTyped F P η) (consumerPrewhiskerTyped_weak F P η hη)
    (consumerPrewhiskerTyped_zeroWeak F P hz) Q
    (modelZeroEndotransformation_postcomp_weak (V := A) (W := W) (T := T) (P ≫ F)
      (fun X ↦ hz (P.functor.obj X)) Q) n r s x

/-- Postwhiskering preserves the checked literal identity of the original typed prewhisker. -/
private theorem consumerPostPrewhiskerTyped_eq :
    whiskerRight (consumerPrewhiskerTyped F P η) Q.functor =
      whiskerRight (whiskerLeft P.functor η) Q.functor :=
  congrArg (fun τ : (P ≫ F).functor ⟶ (P ≫ F).functor ↦ whiskerRight τ Q.functor)
    (consumerPrewhiskerTyped_eq F P η)

/-- The exact typed prewhisker and named zero proof have the original point value. -/
private theorem consumerContractionPreTyped_eq (n : ℕ) (r s : unitInterval)
    (x : (prespectrum A).space n) :
    (prespectrumEndotransformationContraction (V := A) (W := W) (P ≫ F)
      (consumerPrewhiskerTyped F P η) (consumerPrewhiskerTyped_weak F P η hη)
      (consumerPrewhiskerTyped_zeroWeak F P hz)).level n (r, (s, x)) =
      (prespectrumEndotransformationContraction (V := A) (W := W) (P ≫ F)
        (whiskerLeft P.functor η) (fun X : A ↦ hη (P.functor.obj X))
        (fun X : A ↦ hz (P.functor.obj X))).level n (r, (s, x)) :=
  prespectrumEndotransformationContraction_level_eq_of_heq
    (V := A) (W := W) (F := P ≫ F) (F' := P ≫ F) rfl
    (consumerPrewhiskerTyped F P η) (whiskerLeft P.functor η)
    (consumerPrewhiskerTyped_weak F P η hη) (fun X : A ↦ hη (P.functor.obj X))
    (consumerPrewhiskerTyped_zeroWeak F P hz) (fun X : A ↦ hz (P.functor.obj X))
    (heq_of_eq (consumerPrewhiskerTyped_eq F P η)) n r s x

/-- The exact postwhiskered typed prewhisker retains the old two-sided point value. -/
private theorem consumerContractionPostPreTyped_eq (n : ℕ) (r s : unitInterval)
    (x : (prespectrum A).space n) :
    (prespectrumEndotransformationContraction (V := A) (W := T) ((P ≫ F) ≫ Q)
      (whiskerRight (consumerPrewhiskerTyped F P η) Q.functor)
      (fun X : A ↦ Q.exact.weak _ (consumerPrewhiskerTyped_weak F P η hη X))
      (modelZeroEndotransformation_postcomp_weak (V := A) (W := W) (T := T) (P ≫ F)
        (fun X : A ↦ hz (P.functor.obj X)) Q)).level n (r, (s, x)) =
      (prespectrumEndotransformationContraction (V := A) (W := T) ((P ≫ F) ≫ Q)
        (whiskerRight (whiskerLeft P.functor η) Q.functor)
        (fun X : A ↦ Q.exact.weak _ (hη (P.functor.obj X)))
        (modelZeroEndotransformation_postcomp_weak (V := A) (W := W) (T := T) (P ≫ F)
          (fun X : A ↦ hz (P.functor.obj X)) Q)).level n (r, (s, x)) :=
  prespectrumEndotransformationContraction_level_eq_of_heq
    (V := A) (W := T) (F := (P ≫ F) ≫ Q) (F' := (P ≫ F) ≫ Q) rfl
    (whiskerRight (consumerPrewhiskerTyped F P η) Q.functor)
    (whiskerRight (whiskerLeft P.functor η) Q.functor)
    (fun X : A ↦ Q.exact.weak _ (consumerPrewhiskerTyped_weak F P η hη X))
    (fun X : A ↦ Q.exact.weak _ (hη (P.functor.obj X)))
    (modelZeroEndotransformation_postcomp_weak (V := A) (W := W) (T := T) (P ≫ F)
      (fun X : A ↦ hz (P.functor.obj X)) Q)
    (modelZeroEndotransformation_postcomp_weak (V := A) (W := W) (T := T) (P ≫ F)
      (fun X : A ↦ hz (P.functor.obj X)) Q)
    (heq_of_eq (consumerPostPrewhiskerTyped_eq F P Q η)) n r s x

/-- Both coefficient directions retain the same two-time cancellation family. -/
theorem original_two_sided_coefficients (n : ℕ) (r s : unitInterval)
    (x : (prespectrum A).space n) :
    (prespectrumEndotransformationContraction (V := A) (W := T) ((P ≫ F) ≫ Q)
      (whiskerRight (whiskerLeft P.functor η) Q.functor)
      (fun X ↦ Q.exact.weak _ (hη (P.functor.obj X)))
      (modelZeroEndotransformation_postcomp_weak (V := A) (W := W) (T := T) (P ≫ F)
        (fun X ↦ hz (P.functor.obj X)) Q)).level n (r, (s, x)) =
      (prespectrumMap (V := W) (W := T) Q).map n
        ((prespectrumEndotransformationContraction (V := V) (W := W) F η hη hz).level n
          (r, (s, (prespectrumMap (V := A) (W := V) P).map n x))) := by
  calc
    _ = (prespectrumEndotransformationContraction (V := A) (W := T) ((P ≫ F) ≫ Q)
        (whiskerRight (consumerPrewhiskerTyped F P η) Q.functor)
        (fun X : A ↦ Q.exact.weak _ (consumerPrewhiskerTyped_weak F P η hη X))
        (modelZeroEndotransformation_postcomp_weak (V := A) (W := W) (T := T) (P ≫ F)
          (fun X : A ↦ hz (P.functor.obj X)) Q)).level n (r, (s, x)) :=
      (consumerContractionPostPreTyped_eq F P Q η hη hz n r s x).symm
    _ = (prespectrumMap (V := W) (W := T) Q).map n
        ((prespectrumEndotransformationContraction (V := A) (W := W) (P ≫ F)
          (consumerPrewhiskerTyped F P η) (consumerPrewhiskerTyped_weak F P η hη)
          (consumerPrewhiskerTyped_zeroWeak F P hz)).level n (r, (s, x))) :=
      original_post_on_typed_precomposite F P Q η hη hz n r s x
    _ = (prespectrumMap (V := W) (W := T) Q).map n
        ((prespectrumEndotransformationContraction (V := A) (W := W) (P ≫ F)
          (whiskerLeft P.functor η) (fun X : A ↦ hη (P.functor.obj X))
          (fun X : A ↦ hz (P.functor.obj X))).level n (r, (s, x))) :=
      congrArg (fun y : (prespectrum W).space n ↦
        (prespectrumMap (V := W) (W := T) Q).map n y)
        (consumerContractionPreTyped_eq F P η hη hz n r s x)
    _ = _ := congrArg (fun y : (prespectrum W).space n ↦
      (prespectrumMap (V := W) (W := T) Q).map n y)
      (prespectrumEndotransformationContraction_precomp_level
        (V := V) (W := W) (T := A) F η hη hz P n r s x)

/-- The same two-sided family preserves the independent original structure coordinate. -/
theorem original_structure_time (n : ℕ) (r s t : unitInterval)
    (x : (prespectrum A).space n) :
    (prespectrumEndotransformationContraction (V := A) (W := T) ((P ≫ F) ≫ Q)
      (whiskerRight (whiskerLeft P.functor η) Q.functor)
      (fun X ↦ Q.exact.weak _ (hη (P.functor.obj X)))
      (modelZeroEndotransformation_postcomp_weak (V := A) (W := W) (T := T) (P ≫ F)
        (fun X ↦ hz (P.functor.obj X)) Q)).level (n + 1)
        (r, (s, (prespectrum A).structureMap n x t)) =
      (prespectrum T).structureMap n ((prespectrumMap (V := W) (W := T) Q).map n
        ((prespectrumEndotransformationContraction (V := V) (W := W) F η hη hz).level n
          (r, (s, (prespectrumMap (V := A) (W := V) P).map n x)))) t := by
  rw [(prespectrumEndotransformationContraction (V := A) (W := T) ((P ≫ F) ≫ Q)
    (whiskerRight (whiskerLeft P.functor η) Q.functor)
    (fun X ↦ Q.exact.weak _ (hη (P.functor.obj X)))
    (modelZeroEndotransformation_postcomp_weak (V := A) (W := W) (T := T) (P ≫ F)
      (fun X ↦ hz (P.functor.obj X)) Q)).comm]
  rw [original_two_sided_coefficients F P Q η hη hz]

/-- Degree zero retains the actual based loop and its independent parameter. -/
theorem original_internal_loop_time (r s q : unitInterval)
    (γ : Path (stagePoint 0 A) (stagePoint 0 A)) :
    (show Path (stagePoint 0 T) (stagePoint 0 T) from
      (prespectrumEndotransformationContraction (V := A) (W := T) ((P ≫ F) ≫ Q)
        (whiskerRight (whiskerLeft P.functor η) Q.functor)
        (fun X ↦ Q.exact.weak _ (hη (P.functor.obj X)))
        (modelZeroEndotransformation_postcomp_weak (V := A) (W := W) (T := T) (P ≫ F)
          (fun X ↦ hz (P.functor.obj X)) Q)).level 0 (r, (s, γ))) q =
      SSet.toTop.map ((stages 0).map Q)
        ((show Path (stagePoint 0 W) (stagePoint 0 W) from
          (prespectrumEndotransformationContraction (V := V) (W := W) F η hη hz).level 0
            (r, (s, (prespectrumMap (V := A) (W := V) P).map 0 γ))) q) :=
  congrArg (fun p : Path (stagePoint 0 T) (stagePoint 0 T) ↦ p q)
    (original_two_sided_coefficients F P Q η hη hz 0 r s γ)

section CoefficientSquare
variable {M N M' N' : Model.{u}} (f : M ⟶ N) (g : M' ⟶ N')
  (a : M ⟶ M') (b : N ⟶ N') (h : f ≫ b = a ≫ g)
  (α : f.functor ⟶ f.functor) (β : g.functor ⟶ g.functor)
  (hα : ∀ X, N.waldhausen.weq (α.app X))
  (hβ : ∀ X, N'.waldhausen.weq (β.app X))
  (hzf : ∀ X, N.waldhausen.weq ((modelZeroEndotransformation (V := M) (W := N) f).app X))
  (hzg : ∀ X, N'.waldhausen.weq ((modelZeroEndotransformation (V := M') (W := N') g).app X))
  (hs : whiskerRight α b.functor =
    eqToHom (congrArg Model.Hom.functor h) ≫ whiskerLeft a.functor β ≫
      eqToHom (congrArg Model.Hom.functor h.symm))

include h hs

/-- An actual strict scalar square preserves the third, independent structure parameter. -/
theorem original_strict_square_structure_time (n : ℕ) (r s t : unitInterval)
    (x : (prespectrum M).space n) :
    (prespectrum N').structureMap n ((prespectrumMap (V := N) (W := N') b).map n
      ((prespectrumEndotransformationContraction (V := M) (W := N) f α hα hzf).level n (r,
        (s, x)))) t =
      (prespectrumEndotransformationContraction (V := M') (W := N') g β hβ hzg).level (n + 1)
        (r, (s, (prespectrum M').structureMap n ((prespectrumMap (V := M)
          (W := M') a).map n x) t)) := by
  rw [(prespectrumEndotransformationContraction (V := M') (W := N') g β hβ hzg).comm]
  exact congrArg (fun y ↦ (prespectrum N').structureMap n y t)
    (prespectrumEndotransformationContraction_naturality
      (V := M) (W := N) (T := M') (U := N') f g a b h α β hα hβ hzf hzg hs
      n r s x)

/-- The strict scalar square retains the same degree-zero loop parameter and both times. -/
theorem original_strict_square_internal_loop_time (r s q : unitInterval)
    (γ : Path (stagePoint 0 M) (stagePoint 0 M)) :
    SSet.toTop.map ((stages 0).map b)
      ((show Path (stagePoint 0 N) (stagePoint 0 N) from
        (prespectrumEndotransformationContraction (V := M) (W := N) f α hα hzf).level 0 (r,
          (s, γ))) q) =
      (show Path (stagePoint 0 N') (stagePoint 0 N') from
        (prespectrumEndotransformationContraction (V := M') (W := N') g β hβ hzg).level 0
          (r, (s, (prespectrumMap (V := M) (W := M') a).map 0 γ))) q :=
  congrArg (fun p : Path (stagePoint 0 N') (stagePoint 0 N') ↦ p q)
    (prespectrumEndotransformationContraction_naturality
      (V := M) (W := N) (T := M') (U := N') f g a b h α β hα hβ hzf hzg hs
      0 r s γ)

end CoefficientSquare

end Quillen.Tests.GradingContractionNaturality
