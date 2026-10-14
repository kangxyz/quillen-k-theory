/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeBinaryComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SplitTripleParameters
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexTriangleSourceTransport

/-! The genuine scheme-associativity source transport in the first right binary face. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u v w z
namespace Quillen.Waldhausen.IteratedS
/-- Equality of the first weak transformation preserves the entire specified triangle. -/
theorem transformationComposition_congr_first {V W : Model.{u}} {F G H : V ⟶ W}
    (η η' : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hη' : ∀ A, W.waldhausen.weq (η'.app A))
    (hθ : ∀ A, W.waldhausen.weq (θ.app A)) (e : η = η')
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (r, (s, x)) =
      (prespectrumTransformationCompositionHomotopy η' θ hη' hθ).level n (r, (s, x)) := by
  subst η'
  rfl
end Quillen.Waldhausen.IteratedS

namespace CategoryTheory

theorem whiskering_eqToHom {A : Type u} {B : Type v} {C : Type w} {D : Type z}
    [Category A] [Category B] [Category C] [Category D]
    (L : A ⥤ B) (R : C ⥤ D) {F G : B ⥤ C} (e : F = G) :
    whiskerLeft L (whiskerRight (eqToHom e) R) =
      eqToHom (congrArg (fun H ↦ L ⋙ H ⋙ R) e) := by
  subst G
  ext A
  simp
end CategoryTheory

namespace Quillen.PerfectComplexes.SplitTripleSimplex
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

private theorem source_functor_eq :
    (NormalizedTripleSimplex.sourceMap f g h).functor =
      (BinaryNormalizationSimplex.sourceMap (f ≫ g) h).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (Category.assoc f g h).symm)

private theorem rightFirst_hom :
    (rightFirstGeometric f g h).hom =
      eqToHom (source_functor_eq f g h) ≫
        (BinaryNormalizationSimplex.first (f ≫ g) h).hom := by
  unfold rightFirstGeometric BinaryNormalizationSimplex.first
  simp only [isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.trans_hom, eqToIso.hom,
    whiskerRight_comp, whiskerLeft_comp, whiskering_eqToHom]

/-- The entire first right native binary face retains the genuine source association equality. -/
theorem rightFirst_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (rightFirstParameter (r, s), x) =
      (boundedFlatNormalizedCompTrackComparison (f ≫ g) h).level n (r, (s, x)) := by
  refine (rightFirstParameter_lift f g h n r s x).trans ?_
  trans (prespectrumTransformationCompositionHomotopy
    (eqToHom (source_functor_eq f g h) ≫
      (BinaryNormalizationSimplex.first (f ≫ g) h).hom)
    (BinaryNormalizationSimplex.second (f ≫ g) h).hom
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
      inferInstance)).level n (r, (s, x))
  · exact transformationComposition_congr_first _ _ _ _ _ _ (rightFirst_hom f g h) n r s x
  refine (transformationComposition_source_transport
    (F := NormalizedTripleSimplex.sourceMap f g h)
    (F' := BinaryNormalizationSimplex.sourceMap (f ≫ g) h)
    (G := BinaryNormalizationSimplex.intermediateMap (f ≫ g) h)
    (H := BinaryNormalizationSimplex.targetMap (f ≫ g) h)
    (source_functor_eq f g h)
    (BinaryNormalizationSimplex.first (f ≫ g) h).hom
    (BinaryNormalizationSimplex.second (f ≫ g) h).hom
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    n r s x).trans ?_
  exact (BinaryNormalizationSimplex.native_apply (f ≫ g) h n r s x).symm

end Quillen.PerfectComplexes.SplitTripleSimplex
