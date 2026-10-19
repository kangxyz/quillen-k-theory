/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationComposition
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexIsomorphism
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexTriangleWhiskering

/-!
# A common simplex for three actual coefficient evaluation cuts

For three actual joint coefficient arrows, the four evaluation cuts form one exact,
zero-preserving Model simplex. Its last triangular face is the actual postcomposed
binary evaluation route. The long edge is identified using the original categorical
pasting equation, including the original raw composition isomorphism.

All finite simplex, input-loop and spectrum-structure coordinates are retained by the
existing iterated-S realization. This is a finite categorical comparison producer;
it does not construct a source-null square or a second Bass-cone comparison.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientSectionEvaluationCutSimplex
variable {R : CommRingCat.{u}} {i j k l : Index R}
  (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)

/-- Evaluation after the complete strict section composite. -/
def first : boundedFlatCoefficientSectionModel i ⟶
    modelOf (boundedFlatPerfectWaldhausen (space l)) :=
  boundedFlatCoefficientSectionModelMap ((f ≫ g) ≫ h) ≫
    boundedFlatCoefficientSectionEvaluationModelMap l

/-- Move evaluation across only the final coefficient arrow. -/
def second : boundedFlatCoefficientSectionModel i ⟶
    modelOf (boundedFlatPerfectWaldhausen (space l)) :=
  (boundedFlatCoefficientSectionModelMap (f ≫ g) ≫
    boundedFlatCoefficientSectionEvaluationModelMap k) ≫
      boundedFlatCoefficientOriginalModelMap h

/-- Move evaluation across the last two coefficient arrows. -/
def third : boundedFlatCoefficientSectionModel i ⟶
    modelOf (boundedFlatPerfectWaldhausen (space l)) :=
  ((boundedFlatCoefficientSectionModelMap f ≫
    boundedFlatCoefficientSectionEvaluationModelMap j) ≫
      boundedFlatCoefficientOriginalModelMap g) ≫ boundedFlatCoefficientOriginalModelMap h

/-- Source evaluation followed by all three original normalized raw pullbacks. -/
def last : boundedFlatCoefficientSectionModel i ⟶
    modelOf (boundedFlatPerfectWaldhausen (space l)) :=
  ((boundedFlatCoefficientSectionEvaluationModelMap i ≫
    boundedFlatCoefficientOriginalModelMap f) ≫
      boundedFlatCoefficientOriginalModelMap g) ≫ boundedFlatCoefficientOriginalModelMap h

/-- The first cut retains strict source transport and the actual final evaluation isomorphism. -/
def firstIso : (first f g h).functor ≅ (second f g h).functor :=
  boundedFlatCoefficientSectionModelFirstRouteIso (f ≫ g) h

/-- The middle cut is the original binary first route, postcomposed by the last raw pullback. -/
def middleIso : (second f g h).functor ≅ (third f g h).functor :=
  isoWhiskerRight (boundedFlatCoefficientSectionModelFirstRouteIso f g)
    (boundedFlatCoefficientOriginalModelMap h).functor

/-- The last cut is the original first evaluation isomorphism with both raw whiskers retained. -/
def lastIso : (third f g h).functor ≅ (last f g h).functor :=
  isoWhiskerRight (boundedFlatCoefficientSectionModelSecondRouteIso f g)
    (boundedFlatCoefficientOriginalModelMap h).functor

/-- All four original zero-preserving vertices, in their fixed cut order. -/
def vertices : Fin 4 → (boundedFlatCoefficientSectionModel i ⟶
    modelOf (boundedFlatPerfectWaldhausen (space l))) :=
  ![first f g h, second f g h, third f g h, last f g h]

/-- The original adjacent evaluation isomorphisms determine every reference anchor. -/
def anchors : ∀ a, (first f g h).functor ≅ (vertices f g h a).functor :=
  Fin.cases (Iso.refl _) (Fin.cases (firstIso f g h)
    (Fin.cases (firstIso f g h ≪≫ middleIso f g h)
      (Fin.cases (firstIso f g h ≪≫ middleIso f g h ≪≫ lastIso f g h)
        (fun a ↦ Fin.elim0 a))))

/-- One genuine functor carries the three actual evaluation cuts simultaneously. -/
def simplex : ModelSimplex (boundedFlatCoefficientSectionModel i)
    (modelOf (boundedFlatPerfectWaldhausen (space l))) 3 :=
  ModelSimplex.ofIsos (first f g h) (vertices f g h) (anchors f g h)

/-- The leading face is the original first and middle evaluation-cut triangle. -/
theorem first_face :
    (simplex f g h).face (SimplexCategory.δ 3) =
      ModelSimplex.triangle (firstIso f g h).hom (middleIso f g h).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen (space l)).smallModel.weq_iso _ inferInstance)
        (fun _ ↦ (boundedFlatPerfectWaldhausen (space l)).smallModel.weq_iso _ inferInstance) := by
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · rfl

/-- The trailing face is the original middle and final evaluation-cut triangle. -/
theorem last_face :
    (simplex f g h).face (SimplexCategory.δ 0) =
      ModelSimplex.triangle (middleIso f g h).hom (lastIso f g h).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen (space l)).smallModel.weq_iso _ inferInstance)
        (fun _ ↦ (boundedFlatPerfectWaldhausen (space l)).smallModel.weq_iso _ inferInstance) := by
  apply ModelSimplex.ofIsos_face_triangle
  · rfl
  · exact Category.assoc _ _ _

/-- The first shortcut face retains the composite of the first two actual cuts. -/
theorem skip_first_face :
    (simplex f g h).face (SimplexCategory.δ 1) =
      ModelSimplex.triangle (firstIso f g h ≪≫ middleIso f g h).hom (lastIso f g h).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen (space l)).smallModel.weq_iso _ inferInstance)
        (fun _ ↦ (boundedFlatPerfectWaldhausen (space l)).smallModel.weq_iso _ inferInstance) := by
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact Category.assoc _ _ _

/-- The second shortcut face retains the composite of the final two actual cuts. -/
theorem skip_last_face :
    (simplex f g h).face (SimplexCategory.δ 2) =
      ModelSimplex.triangle (firstIso f g h).hom (middleIso f g h ≪≫ lastIso f g h).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen (space l)).smallModel.weq_iso _ inferInstance)
        (fun _ ↦ (boundedFlatPerfectWaldhausen (space l)).smallModel.weq_iso _ inferInstance) := by
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · rfl

/-- The whole trailing face is the postcomposition of the actual original binary route. -/
theorem last_face_postcomp :
    (simplex f g h).face (SimplexCategory.δ 0) =
      (ModelSimplex.triangle
        (F := boundedFlatCoefficientSectionModelMap (f ≫ g) ≫
          boundedFlatCoefficientSectionEvaluationModelMap k)
        (G := (boundedFlatCoefficientSectionModelMap f ≫
          boundedFlatCoefficientSectionEvaluationModelMap j) ≫
            boundedFlatCoefficientOriginalModelMap g)
        (H := (boundedFlatCoefficientSectionEvaluationModelMap i ≫
          boundedFlatCoefficientOriginalModelMap f) ≫ boundedFlatCoefficientOriginalModelMap g)
        (boundedFlatCoefficientSectionModelFirstRouteIso f g).hom
        (boundedFlatCoefficientSectionModelSecondRouteIso f g).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)
        (fun _ ↦ (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _
          inferInstance)).postcomp
          (boundedFlatCoefficientOriginalModelMap h) := by
  rw [last_face, ModelSimplex.triangle_postcomp]
  rfl

/-- The long trailing edge keeps the original evaluation and the raw composition isomorphism. -/
theorem trailing_pasting :
    (middleIso f g h).hom ≫ (lastIso f g h).hom =
      whiskerRight ((boundedFlatCoefficientSectionEvaluationIso (f ≫ g)).hom ≫
        (boundedFlatCoefficientSectionModelTargetIso f g).hom)
        (boundedFlatCoefficientOriginalModelMap h).functor := by
  rw [boundedFlatCoefficientSectionModelPasting_hom]
  exact (whiskerRight_comp _ _ _).symm

/-- The raw three-arrow comparison retains both original binary composition isomorphisms. -/
def rawCompositionIso :
    ((boundedFlatCoefficientSectionEvaluationModelMap i) ≫
      boundedFlatCoefficientOriginalModelMap ((f ≫ g) ≫ h)).functor ≅
        (last f g h).functor :=
  boundedFlatCoefficientSectionModelTargetIso (f ≫ g) h ≪≫
    isoWhiskerRight (boundedFlatCoefficientSectionModelTargetIso f g)
      (boundedFlatCoefficientOriginalModelMap h).functor

/-- The long edge is the original evaluation followed by the full raw composition word. -/
theorem whole_pasting :
    (boundedFlatCoefficientSectionEvaluationIso ((f ≫ g) ≫ h)).hom ≫
      (rawCompositionIso f g h).hom =
        (firstIso f g h).hom ≫ (middleIso f g h).hom ≫ (lastIso f g h).hom := by
  change (boundedFlatCoefficientSectionEvaluationIso ((f ≫ g) ≫ h)).hom ≫
    ((boundedFlatCoefficientSectionModelTargetIso (f ≫ g) h).hom ≫
      whiskerRight (boundedFlatCoefficientSectionModelTargetIso f g).hom
        (boundedFlatCoefficientOriginalModelMap h).functor) = _
  rw [← Category.assoc, boundedFlatCoefficientSectionModelPasting_hom]
  change ((firstIso f g h).hom ≫
    whiskerRight (boundedFlatCoefficientSectionEvaluationIso (f ≫ g)).hom
      (boundedFlatCoefficientOriginalModelMap h).functor) ≫
    whiskerRight (boundedFlatCoefficientSectionModelTargetIso f g).hom
      (boundedFlatCoefficientOriginalModelMap h).functor = _
  rw [Category.assoc, ← whiskerRight_comp, boundedFlatCoefficientSectionModelPasting_hom,
    whiskerRight_comp]
  rfl

/-- Every native level receives the same full original three-cut simplex parameter. -/
def family (n : ℕ) := prespectrumSimplexFamily (simplex f g h) n

/-- The actual binary comparison fills the whole trailing face with its original two clocks. -/
theorem family_last_composition (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedFlatCoefficientSectionModel i)).space n) :
    family f g h n
      (StdSimplex.map (SimplexCategory.δ 0).toOrderHom
        (Quillen.TheoremB.compositionTriangleHomotopy (r, s)), x) =
      ((prespectrumTransformationCompositionHomotopy
        (F := boundedFlatCoefficientSectionModelMap (f ≫ g) ≫
          boundedFlatCoefficientSectionEvaluationModelMap k)
        (G := (boundedFlatCoefficientSectionModelMap f ≫
          boundedFlatCoefficientSectionEvaluationModelMap j) ≫
            boundedFlatCoefficientOriginalModelMap g)
        (H := (boundedFlatCoefficientSectionEvaluationModelMap i ≫
          boundedFlatCoefficientOriginalModelMap f) ≫ boundedFlatCoefficientOriginalModelMap g)
        (boundedFlatCoefficientSectionModelFirstRouteIso f g).hom
        (boundedFlatCoefficientSectionModelSecondRouteIso f g).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)
        (fun _ ↦ (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _
          inferInstance)).postcomp
          (prespectrumMap (boundedFlatCoefficientOriginalModelMap h))).level n (r, (s, x)) := by
  change prespectrumSimplexFamily _ _ _ = _
  rw [prespectrumSimplexFamily_face, last_face, prespectrumSimplexFamily_triangle]
  exact transformationComposition_postcomp _ _ _ _ _ _ _ _ _

/-- The simplex preserves the actual native point for every coefficient parameter. -/
theorem family_point (n : ℕ) (z : StdSimplex ℝ (Fin 4)) :
    family f g h n (z, (prespectrum (boundedFlatCoefficientSectionModel i)).point n) =
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space l)))).point n :=
  prespectrumSimplexFamily_point _ _ _

/-- The original spectrum-structure time is independent of the complete cut parameter. -/
theorem family_structure (n : ℕ) (z : StdSimplex ℝ (Fin 4))
    (x : (prespectrum (boundedFlatCoefficientSectionModel i)).space n) (t : unitInterval) :
    family f g h (n + 1)
        (z, (prespectrum (boundedFlatCoefficientSectionModel i)).structureMap n x t) =
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space l)))).structureMap n
        (family f g h n (z, x)) t :=
  prespectrumSimplexFamily_structure _ _ _ _ _

end Quillen.PerfectComplexes.CoefficientSectionEvaluationCutSimplex
