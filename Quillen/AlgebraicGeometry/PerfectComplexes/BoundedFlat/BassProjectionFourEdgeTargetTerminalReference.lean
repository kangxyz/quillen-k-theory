/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSourceRows

/-!
# The exact target reference of the H0 outer row

The reference from the original H0 diagram to the target overlap is the normalized target
vertex of that same diagram. Both source projection equality and the original outer square
are retained before the final binary normalization.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open BassH0Merge CommonReferenceNerve CoefficientBassSeedTargetH0Reference
open CoefficientBassSeedTargetReferenceTransport

private theorem cancel_terminal_iso {C : Type*} [Category C] {X Y Z W : C}
    (a : X ≅ Y) (b : Z ≅ W) (e : Z ≅ X) :
    (a ≪≫ Iso.refl _) ≪≫ (b.symm ≪≫ e ≪≫ a).symm = e.symm ≪≫ b := by
  simp only [Iso.trans_refl, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc,
    Iso.self_symm_id_assoc]

private theorem terminal_word {A B C D : Scheme.{u}}
    (r s : C ⟶ A) (t : D ⟶ B) (a : B ⟶ A) (c : D ⟶ C)
    (h : s = r) (e : t ≫ a = c ≫ s) :
    (BinaryNormalizationSimplex.total c r ≪≫
      isoWhiskerRight
        (eqToIso (congrArg (fun g ↦ (normalizedMap g).functor) h.symm))
        (normalizedMap c).functor) ≪≫
      ((BinaryNormalizationSimplex.total t a).symm ≪≫
        eqToIso (congrArg (fun g ↦ (normalizedMap g).functor) e) ≪≫
        BinaryNormalizationSimplex.total c s).symm =
      eqToIso (congrArg (fun g ↦ (normalizedMap g).functor)
        ((congrArg (fun g ↦ c ≫ g) h.symm).trans e.symm)) ≪≫
        BinaryNormalizationSimplex.total t a := by
  subst r
  simp only [eqToIso_refl, isoWhiskerRight_refl]
  exact cancel_terminal_iso (BinaryNormalizationSimplex.total c s)
    (BinaryNormalizationSimplex.total t a)
    (eqToIso (congrArg (fun g ↦ (normalizedMap g).functor) e))

private theorem whole_terminal_word {V A B C D : Type*}
    [Category V] [Category A] [Category B] [Category C] [Category D]
    (E : V ⥤ A) (U : A ⥤ B) (S₀ : A ⥤ C) (S₁ : B ⥤ D) (L : C ⥤ D)
    (H : A ⥤ D) (G : V ⥤ C) (τ : E ⋙ S₀ ≅ G)
    (hp : U ⋙ S₁ ≅ S₀ ⋙ L) (hh : H ≅ S₀ ⋙ L) :
    ((Functor.associator E U S₁ ≪≫ isoWhiskerLeft E hp ≪≫
        (Functor.associator E S₀ L).symm ≪≫ isoWhiskerRight τ L) ≪≫
      (isoWhiskerLeft E hh ≪≫ (Functor.associator E S₀ L).symm ≪≫
        isoWhiskerRight τ L).symm).symm =
      isoWhiskerLeft E (hh ≪≫ hp.symm) ≪≫ (Functor.associator E U S₁).symm := by
  simp only [Iso.trans_symm, Iso.symm_symm_eq, isoWhiskerLeft_trans,
    ← isoWhiskerLeft_symm, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.symm_self_id_assoc]

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)

/-- The H0 target anchor retains the two actual original projection comparisons. -/
def terminalBaseAnchor : (BassH0Diagram.reference P f).functor ≅
    (normalizedMap (coefficientMap P f) ≫ BassProjectionPath.source P b).functor :=
  h0ProjectionIso P f ≪≫ (projectionIso P f).symm

/-- Its normal form is the original outer equality followed by the target binary total. -/
theorem terminalBaseAnchor_normal :
    terminalBaseAnchor P f =
      eqToIso (congrArg (fun g ↦ (normalizedMap g).functor)
        ((congrArg (fun g ↦ coefficientMap P ((laurentUnderFunctor R).map f) ≫ g)
          (laurentPlus_projection P a).symm).trans (projection_square P f).symm)) ≪≫
        BinaryNormalizationSimplex.total
          (laurentPlus P b ≫ polynomialProjection P b) (coefficientMap P f) := by
  exact terminal_word (laurentProjection P a) (laurentPlus P a ≫ polynomialProjection P a)
    (laurentPlus P b ≫ polynomialProjection P b) (coefficientMap P f)
    (coefficientMap P ((laurentUnderFunctor R).map f))
    (laurentPlus_projection P a) (projection_square P f)

/-- The whole reference of the actual target node is precisely the public target anchor. -/
theorem terminal_normal_node :
    BassH0Diagram.plusNodes P f 15 =
      (⟨normalizedMap (coefficientMap P f) ≫ BassProjectionPath.source P b,
        terminalBaseAnchor P f⟩ : CommonReferenceNerve.Node (BassH0Diagram.reference P f)) := by
  apply Sigma.ext (ProjectionReference.target_normal_map
    (polynomialProjection P a) (laurentPlus P a)
    (polynomialProjection P b) (laurentPlus P b)
    (coefficientMap P f) (coefficientMap P ((polynomialUnderFunctor R).map f))
    (coefficientMap P ((laurentUnderFunctor R).map f))
    (coefficientMap_naturality P (polynomialUnderCoefficient R) f)
    (coefficientMap_naturality P (underToLaurent R) f)
    (laurentProjection P a) (laurentPlus_projection P a))
  apply heq_of_eq
  exact (ProjectionReference.target_normal_reference
    (polynomialProjection P a) (laurentPlus P a)
    (polynomialProjection P b) (laurentPlus P b)
    (coefficientMap P f) (coefficientMap P ((polynomialUnderFunctor R).map f))
    (coefficientMap P ((laurentUnderFunctor R).map f))
    (coefficientMap_naturality P (polynomialUnderCoefficient R) f)
    (coefficientMap_naturality P (underToLaurent R) f)
    (laurentProjection P a) (laurentPlus_projection P a)).trans
      (terminalBaseAnchor_normal P f).symm

variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (τ : (WholeReference.reference P a E).functor ≅ G.functor)

/-- The same whole terminal anchor is the inverse of the existing target reference bridge. -/
theorem targetReferenceIso_symm :
    (targetReferenceIso P f E G τ).symm =
      isoWhiskerLeft E.functor (terminalBaseAnchor P f) ≪≫
        (Functor.associator E.functor (normalizedMap (coefficientMap P f)).functor
          (BassProjectionPath.source P b).functor).symm := by
  exact whole_terminal_word E.functor (normalizedMap (coefficientMap P f)).functor
    (BassProjectionPath.source P a).functor (BassProjectionPath.source P b).functor
    (CoefficientBassSeedTargetChartAttachment.L P f).functor
    (BassH0Diagram.reference P f).functor G.functor τ
    (projectionIso P f) (h0ProjectionIso P f)

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
