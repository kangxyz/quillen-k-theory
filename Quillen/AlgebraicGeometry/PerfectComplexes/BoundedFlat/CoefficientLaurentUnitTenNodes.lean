/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitComparisonSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNodeTransport
public import Quillen.Waldhausen.SConstruction.Iterated.ModelReferenceReanchor
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexPathEmbedding

/-!
# Ten actual reference nodes for the two Laurent unit comparisons

The original coefficient-unit equality and scheme-square equality identify two complete
reference nodes. Both six-node families then occur as whole ordered faces. The lower and
unit-shifted binary paths C0/C1 and D0/D1 remain distinct paths with distinct reference nodes.
This owner does not construct the final intertwining or the higher mixed comparison.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientLaurentUnitTenNodes
open CoefficientLaurentUnitComparisonSimplex

private def sourceAt {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modelOf (boundedFlatPerfectWaldhausen Y) ⟶ modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact f)
    (boundedFlatNormalizedPullback_obj_zero f)

private def unitAt {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    (sourceAt f).functor ≅ (sourceAt f).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    ((boundedFlatPullbackNormalizationIso f).symm ≪≫ boundedFlatPerfectPullbackUnitIso f r ≪≫
      boundedFlatPullbackNormalizationIso f) AsSmall.up)

private theorem unit_transport {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (r : (Γ(X, ⊤))ˣ) :
    unitAt f r ≪≫ eqToIso (congrArg (fun q ↦ (sourceAt q).functor) h) =
      eqToIso (congrArg (fun q ↦ (sourceAt q).functor) h) ≪≫ unitAt g r := by
  subst g
  simp only [eqToIso_refl, Iso.trans_refl, Iso.refl_trans]

private theorem source_unit_node_eq {V W : Model.{u}} {F G : V ⟶ W}
    (h : F.functor = G.functor) (α : F.functor ≅ F.functor)
    (β : G.functor ≅ G.functor)
    (he : α ≪≫ eqToIso h = eqToIso h ≪≫ β) :
    (⟨F, α⟩ : Σ H : V ⟶ W, F.functor ≅ H.functor) = ⟨G, eqToIso h ≪≫ β⟩ := by
  apply ModelSimplex.reference_node_eq h
  exact congrArg Iso.hom he

private theorem precomp_simplex_nodes {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(X, ⊤))ˣ) :
    ModelSimplex.ofIsos (BinaryNormalizationSimplex.sourceMap f g)
      (fun i ↦ (UnitTrackPrecompSimplex.nodes f g r i).1)
      (fun i ↦ (UnitTrackPrecompSimplex.nodes f g r i).2) =
        UnitTrackPrecompSimplex.simplex f g r := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The original old composite is the common reference, without choosing a new anchor. -/
abbrev source := BinaryNormalizationSimplex.sourceMap
  (coefficientMap P ((laurentUnderFunctor R).map u)) (laurentProjection P a)

/-- The precise original scheme-square equality identifies the two reference functors. -/
theorem source_eq : (source P u).functor =
    (BinaryNormalizationSimplex.sourceMap (laurentProjection P b)
      (coefficientMap P u)).functor :=
  congrArg (fun q ↦ (sourceAt q).functor)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (laurentUnderCoefficient R) u)

/-- This equality-induced isomorphism is the only reanchoring used on the new family. -/
def sourceIso := eqToIso (source_eq P u)

/-- A model-map node with an isomorphism from the original Laurent unit reference. -/
abbrev Node := Σ F : modelOf (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
    modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj b))),
    (source P u).functor ≅ F.functor

/-- All six original old nodes retain their actual reference isomorphisms. -/
def oldNodes := UnitTrackPostcompSimplex.nodes
  (coefficientMap P ((laurentUnderFunctor R).map u)) (laurentProjection P a)
  (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
    (laurentGlobalUnit a.right))

/-- All six original new nodes, before applying the actual source equality. -/
def newNativeNodes := UnitTrackPrecompSimplex.nodes
  (laurentProjection P b) (coefficientMap P u)
  (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
    (laurentGlobalUnit b.right))

/-- Reanchoring retains the full new node, including its original reference isomorphism. -/
def newNodes : Fin 6 → Node P u :=
  ModelSimplex.reanchorNodes (sourceIso P u) (newNativeNodes P u)

/-- The common source is an equality of complete dependent nodes. -/
theorem source_node_join : oldNodes P u 0 = newNodes P u 0 := by
  apply ModelSimplex.reference_node_eq (source_eq P u)
  change (𝟙 _) ≫ eqToHom (source_eq P u) = (sourceIso P u ≪≫ Iso.refl _).hom
  simp only [sourceIso, Iso.trans_hom, Iso.refl_hom, eqToIso.hom,
    Category.id_comp, Category.comp_id]

/-- The actual unit equality and scheme-square transport commute on full source references. -/
theorem source_unit_reference :
    UnitTrackPostcompSimplex.sourceUnit
        (coefficientMap P ((laurentUnderFunctor R).map u)) (laurentProjection P a)
        (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
          (laurentGlobalUnit a.right)) ≪≫ sourceIso P u =
      sourceIso P u ≪≫ UnitTrackPrecompSimplex.sourceUnit
        (laurentProjection P b) (coefficientMap P u)
        (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
          (laurentGlobalUnit b.right)) := by
  change unitAt _ (Units.map
      (coefficientMap P ((laurentUnderFunctor R).map u)).appTop.hom.toMonoidHom
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
        (laurentGlobalUnit a.right))) ≪≫
      eqToIso (congrArg (fun q ↦ (sourceAt q).functor)
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
          (laurentUnderCoefficient R) u)) =
    eqToIso (congrArg (fun q ↦ (sourceAt q).functor)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (laurentUnderCoefficient R) u)) ≪≫ unitAt _ _
  rw [boundedFlatCoefficientLaurentUnit_coefficient]
  exact unit_transport (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
    (laurentUnderCoefficient R) u) _

/-- The unit-shifted source also joins as a full dependent reference node. -/
theorem source_unit_node_join : oldNodes P u 3 = newNodes P u 3 :=
  source_unit_node_eq (source_eq P u) _ _ (source_unit_reference P u)

/-- Ten representatives retain both raw normalization intermediates and every shifted reference. -/
def nodes : Fin 10 → Node P u :=
  ![oldNodes P u 0, oldNodes P u 1, oldNodes P u 2, newNodes P u 1, newNodes P u 2,
    oldNodes P u 3, oldNodes P u 4, oldNodes P u 5, newNodes P u 4, newNodes P u 5]

/-- The complete old six-node order embeds in the common ten-node order. -/
def oldFace : ⦋5⦌ ⟶ ⦋9⦌ := SimplexCategory.Hom.mk ⟨![0, 1, 2, 5, 6, 7], by decide⟩

/-- The complete new six-node order embeds separately in that same order. -/
def newFace : ⦋5⦌ ⟶ ⦋9⦌ := SimplexCategory.Hom.mk ⟨![0, 3, 4, 5, 8, 9], by decide⟩

/-- The old embedding keeps all six exact nodes. -/
theorem old_nodes (i : Fin 6) : nodes P u (oldFace.toOrderHom i) = oldNodes P u i := by
  fin_cases i <;> rfl

/-- The new embedding uses only the two proved complete-node joins. -/
theorem new_nodes (i : Fin 6) : nodes P u (newFace.toOrderHom i) = newNodes P u i := by
  fin_cases i
  · exact source_node_join P u
  · rfl
  · rfl
  · exact source_unit_node_join P u
  · rfl
  · rfl

/-- The actual ten-node common-reference simplex. -/
def simplex : ModelSimplex (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
    (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj b)))) 9 :=
  ModelSimplex.ofIsos (source P u) (fun i ↦ (nodes P u i).1) (fun i ↦ (nodes P u i).2)

/-- Reanchoring preserves the entire original new six-node diagram. -/
theorem new_reference : ModelSimplex.ofIsos (source P u)
    (fun i ↦ (newNodes P u i).1) (fun i ↦ (newNodes P u i).2) = newSimplex P u :=
  (ModelSimplex.reanchorSimplex_eq (sourceIso P u) (newNativeNodes P u)).trans
    (precomp_simplex_nodes (laurentProjection P b) (coefficientMap P u)
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
        (laurentGlobalUnit b.right)))

/-- The full old diagram, rather than just its endpoint maps, is an ordered face. -/
theorem old_face : (simplex P u).face oldFace = oldSimplex P u := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (old_nodes P u)

/-- The full reanchored new diagram is the other ordered face. -/
theorem new_face : (simplex P u).face newFace = newSimplex P u := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (new_nodes P u)).trans (new_reference P u)

/-- Lower old binary route; its unit-shifted copy has different reference nodes. -/
abbrev C0 := binaryPath (k := 9) 0 1 2
/-- Unit-shifted old binary route. -/
abbrev C1 := binaryPath (k := 9) 5 6 7
/-- Lower new binary route. -/
abbrev D0 := binaryPath (k := 9) 0 3 4
/-- Unit-shifted new binary route, kept separately from D0. -/
abbrev D1 := binaryPath (k := 9) 5 8 9
/-- Common source-unit edge between the two distinct source references. -/
abbrev U := edge (k := 9) 0 5
/-- Actual old terminal-unit edge. -/
abbrev V := edge (k := 9) 2 7
/-- Actual new terminal-unit edge. -/
abbrev W := edge (k := 9) 4 9

/-- The original five-piece old parameter, with its two binary routes kept distinct. -/
def oldParameter : (C0.trans V).Homotopy (U.trans C1) :=
  Path.Homotopy.mapOfPaths (embed oldFace) UnitPrismParameters.parameter _ _
    (map_trans_values _ _ _ _ _ (map_binaryPath oldFace 0 1 2) (map_edge oldFace 2 5))
    (map_trans_values _ _ _ _ _ (map_edge oldFace 0 3) (map_binaryPath oldFace 3 4 5))

/-- The original five-piece new parameter, with its own lower and shifted binary routes. -/
def newParameter : (D0.trans W).Homotopy (U.trans D1) :=
  Path.Homotopy.mapOfPaths (embed newFace) UnitPrismParameters.parameter _ _
    (map_trans_values _ _ _ _ _ (map_binaryPath newFace 0 1 2) (map_edge newFace 2 5))
    (map_trans_values _ _ _ _ _ (map_edge newFace 0 3) (map_binaryPath newFace 3 4 5))

/-- The whole existing oldComparison is the old face of the common family. -/
theorem old_comparison_lift : HomotopyLift (simplex P u) oldParameter
    (CoefficientLaurentUnitTrack.oldComparison P u) := by
  intro n r s x
  change prespectrumSimplexFamily (simplex P u) n
    (StdSimplex.map oldFace.toOrderHom (UnitPrismParameters.parameter (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, old_face]
  exact CoefficientLaurentUnitComparisonSimplex.old_comparison_lift P u n r s x

/-- The whole existing newComparison retains its actual transport in the other face. -/
theorem new_comparison_lift : HomotopyLift (simplex P u) newParameter
    (CoefficientLaurentUnitTrack.newComparison P u) := by
  intro n r s x
  change prespectrumSimplexFamily (simplex P u) n
    (StdSimplex.map newFace.toOrderHom (UnitPrismParameters.parameter (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, new_face]
  exact CoefficientLaurentUnitComparisonSimplex.new_comparison_lift P u n r s x

/-- C0 realizes the actual old composition track. -/
theorem C0_native : PathLift (simplex P u) C0
    (CoefficientLaurentUnitTrack.oldComposition P u) :=
  PathLift.trans_left _ (HomotopyLift.source _ (old_comparison_lift P u))

/-- C1 realizes that same native track through its distinct shifted reference nodes. -/
theorem C1_native : PathLift (simplex P u) C1
    (CoefficientLaurentUnitTrack.oldComposition P u) :=
  PathLift.trans_right _ (HomotopyLift.target _ (old_comparison_lift P u))

/-- D0 realizes the actual new composition, including its original endpoint cast. -/
theorem D0_native : PathLift (simplex P u) D0
    (CoefficientLaurentUnitTrack.newComposition P u) :=
  PathLift.trans_left _ (HomotopyLift.source _ (new_comparison_lift P u))

/-- D1 retains its distinct shifted references and the same original new native track. -/
theorem D1_native : PathLift (simplex P u) D1
    (CoefficientLaurentUnitTrack.newComposition P u) :=
  PathLift.trans_right _ (HomotopyLift.target _ (new_comparison_lift P u))

end Quillen.PerfectComplexes.CoefficientLaurentUnitTenNodes
