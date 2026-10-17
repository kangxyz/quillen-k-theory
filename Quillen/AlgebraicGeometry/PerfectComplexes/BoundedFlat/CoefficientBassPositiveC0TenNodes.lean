/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0UnitStrip
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitTenNodes

/-!
# Original W-edge joins for the positive C0 carrier

The two original TenNodes W edges retain indices 4 and 9, their equality-induced source
anchors, and the actual commonUnit. Full dependent nodes are joined before taking whole
edge parameters. No seed subdivision, tip, or original parameter is replaced.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open Quillen.FunctorIdentityAutomorphism
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC0TenNodes
open BassH0Merge CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierRails CoefficientBassPositiveC0UnitStrip
open LaurentUnitReferenceSpecialization

/-- The actual ordered target-unit edge, distinct from the old V edge 2 to 7. -/
def wFace : ⦋1⦌ ⟶ ⦋9⦌ := SimplexCategory.Hom.mk ⟨![4, 9], by decide⟩

/-- Reanchoring a shifted full node uses only the supplied reference intertwining. -/
private theorem anchor_shift {V T : Model.{u}} {F H : V ⟶ T}
    (ρ : F.functor ≅ H.functor) (τ : F.functor ≅ F.functor)
    (ε : 𝟭 T ≅ 𝟭 T) (N M : Node H)
    (hM : M = (⟨N.1, N.2 ≪≫ onFunctor N.1.functor ε⟩ : Node H))
    (hτ : τ ≪≫ (anchorNode ρ N).2 =
      (anchorNode ρ N).2 ≪≫ onFunctor (anchorNode ρ N).1.functor ε) :
    anchorNode τ (anchorNode ρ N) = anchorNode ρ M := by
  rw [hM]
  exact congrArg (fun η : F.functor ≅ N.1.functor ↦ (⟨N.1, η⟩ : Node F))
    (hτ.trans (Iso.trans_assoc ρ N.2 (onFunctor N.1.functor ε)))

/-- Precomposition of a shifted full node retains the complete middle reference. -/
private theorem preReference_shift {V U T : Model.{u}} {F : V ⟶ T} {H : U ⟶ T}
    (L : V ⟶ U) (ρ : F.functor ≅ (L ≫ H).functor)
    (τ : F.functor ≅ F.functor) (ε : 𝟭 T ≅ 𝟭 T) (N M : Node H)
    (hM : M = (⟨N.1, N.2 ≪≫ onFunctor N.1.functor ε⟩ : Node H))
    (hτ : τ ≪≫ (preReferenceNode F L ρ N).2 =
      (preReferenceNode F L ρ N).2 ≪≫
        onFunctor (preReferenceNode F L ρ N).1.functor ε) :
    anchorNode τ (preReferenceNode F L ρ N) = preReferenceNode F L ρ M := by
  have hw : isoWhiskerLeft L.functor (onFunctor N.1.functor ε) =
      onFunctor (L ≫ N.1).functor ε := by
    apply Iso.ext
    ext X
    rfl
  rw [hM]
  unfold preReferenceNode anchorNode
  dsimp only
  rw [isoWhiskerLeft_trans, hw]
  exact congrArg (fun η : F.functor ≅ (L ≫ N.1).functor ↦
    (⟨L ≫ N.1, η⟩ : Node F))
    (hτ.trans (Iso.trans_assoc ρ (isoWhiskerLeft L.functor N.2)
      (onFunctor (L ≫ N.1).functor ε)))

/-- The original W parameter is precisely the ordered face, at unchanged time. -/
private theorem w_parameter {V T : Model.{u}} (F : V ⟶ T)
    (N : Fin 10 → Node F) (t : I) :
    parameter F N (CoefficientLaurentUnitTenNodes.W t) =
      parameter F (fun i ↦ N (wFace.toOrderHom i)) (edge (k := 1) 0 1 t) := by
  rw [show CoefficientLaurentUnitTenNodes.W t =
      StdSimplex.map wFace.toOrderHom (edge (k := 1) 0 1 t) from
    (map_edge wFace 0 1 t).symm]
  exact parameter_face F N wFace (edge (k := 1) 0 1 t)

variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- Original target projection node, including the actual naturality equality anchor. -/
theorem projection_start_ten {d e : Under R} (w : d ⟶ e) :
    BassH0Diagram.nodes P w (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex 0))) =
      CoefficientLaurentUnitTenNodes.nodes P w 4 := by
  rw [BassH0Diagram.plus_nodes]
  have h := ProjectionReference.target_normal_node
    (polynomialProjection P d) (laurentPlus P d)
    (polynomialProjection P e) (laurentPlus P e)
    (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (coefficientMap_naturality P (polynomialUnderCoefficient R) w)
    (coefficientMap_naturality P (underToLaurent R) w)
    (laurentProjection P d) (laurentProjection P e)
    (laurentPlus_projection P d) (laurentPlus_projection P e)
  refine h.trans ?_
  change (⟨_, CoefficientLaurentUnitTenNodes.sourceIso P w ≪≫
    BinaryNormalizationSimplex.total (laurentProjection P e) (coefficientMap P w)⟩ :
    CoefficientLaurentUnitTenNodes.Node P w) =
    ⟨_, CoefficientLaurentUnitTenNodes.sourceIso P w ≪≫
      (BinaryNormalizationSimplex.first (laurentProjection P e) (coefficientMap P w) ≪≫
        BinaryNormalizationSimplex.second (laurentProjection P e) (coefficientMap P w))⟩
  rw [show BinaryNormalizationSimplex.first (laurentProjection P e) (coefficientMap P w) ≪≫
      BinaryNormalizationSimplex.second (laurentProjection P e) (coefficientMap P w) =
      BinaryNormalizationSimplex.total (laurentProjection P e) (coefficientMap P w) from
    Iso.ext (BinaryNormalizationSimplex.small_composite_hom
      (laurentProjection P e) (coefficientMap P w))]

/-- The original precomposition final unit is the actual Laurent target action. -/
theorem ten_finalUnit_action {d e : Under R} (w : d ⟶ e) :
    UnitTrackPrecompSimplex.finalUnit (laurentProjection P e) (coefficientMap P w)
      (laurentUnit P e) =
    onFunctor (BinaryNormalizationSimplex.targetMap
      (laurentProjection P e) (coefficientMap P w)).functor (smallUnit P e) := by
  unfold UnitTrackPrecompSimplex.finalUnit UnitTrackPrecompSimplex.finalUnitIso
  rw [GlobalUnitReferenceNaturality.normalizedUnit_eq_onFunctor]
  have h : isoWhiskerLeft (boundedFlatNormalizedPullback (coefficientMap P w))
      (onFunctor (boundedFlatNormalizedPullback (laurentProjection P e))
        (boundedFlatPerfectGlobalUnitIso _ (laurentUnit P e))) =
      onFunctor (boundedFlatNormalizedPullback (coefficientMap P w) ⋙
        boundedFlatNormalizedPullback (laurentProjection P e))
        (boundedFlatPerfectGlobalUnitIso _ (laurentUnit P e)) := by
    apply Iso.ext
    ext X
    rfl
  rw [h]
  exact GlobalUnitReferenceNaturality.small_onFunctor _ _

/-- Node 9 keeps the complete lower reference followed by the original target unit. -/
theorem ten_shift {d e : Under R} (w : d ⟶ e) :
    CoefficientLaurentUnitTenNodes.nodes P w 9 =
      (⟨(CoefficientLaurentUnitTenNodes.nodes P w 4).1,
        (CoefficientLaurentUnitTenNodes.nodes P w 4).2 ≪≫
          onFunctor (CoefficientLaurentUnitTenNodes.nodes P w 4).1.functor
            (smallUnit P e)⟩ : CoefficientLaurentUnitTenNodes.Node P w) := by
  change (⟨_, CoefficientLaurentUnitTenNodes.sourceIso P w ≪≫
    ((BinaryNormalizationSimplex.first (laurentProjection P e) (coefficientMap P w) ≪≫
      BinaryNormalizationSimplex.second (laurentProjection P e) (coefficientMap P w)) ≪≫
      UnitTrackPrecompSimplex.finalUnit _ _ (laurentUnit P e))⟩ :
      CoefficientLaurentUnitTenNodes.Node P w) = _
  rw [ten_finalUnit_action, ← Iso.trans_assoc]
  rfl

variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The direct-composite W edge in the original common reference. -/
def sourceTenNodes (i : Fin 10) : Node (laurentReference P p q) :=
  anchorNode (eqToIso (BassH0Merge.reference_eq P p q))
    (CoefficientLaurentUnitTenNodes.nodes P (p ≫ q) i)

/-- The q W edge after the original p model and original H1 middle anchor. -/
def targetTenNodes (i : Fin 10) : Node (laurentReference P p q) :=
  preReferenceNode (laurentReference P p q) (BassH1Components.coefficientMapModel P p)
    (BassH1References.middleIso P p q) (CoefficientLaurentUnitTenNodes.nodes P q i)

/-- Full lower source join; no attachment or native evaluation is cancelled. -/
theorem source_lower : sourceProjectionNodes P p q 0 = sourceTenNodes P p q 4 :=
  congrArg (anchorNode (eqToIso (BassH0Merge.reference_eq P p q)))
    (projection_start_ten P (p ≫ q))

/-- Full lower target join, preserving precomposition and the H1 middle reference. -/
theorem target_lower : targetProjectionNodes P p q 0 = targetTenNodes P p q 4 :=
  congrArg (preReferenceNode (laurentReference P p q)
    (BassH1Components.coefficientMapModel P p) (BassH1References.middleIso P p q))
    (projection_start_ten P q)

/-- The actual common unit transports through the whole direct-composite endpoint reference. -/
theorem source_upper :
    anchorNode (commonUnit P p q) (sourceTenNodes P p q 4) = sourceTenNodes P p q 9 :=
  anchor_shift.{u + 1} (eqToIso (BassH0Merge.reference_eq P p q)) (commonUnit P p q)
    (smallUnit P c) (CoefficientLaurentUnitTenNodes.nodes P (p ≫ q) 4)
    (CoefficientLaurentUnitTenNodes.nodes P (p ≫ q) 9) (ten_shift P (p ≫ q))
    (common_reference P p q (sourceTenNodes P p q 4))

/-- The actual common unit transports through the pre-p q endpoint reference as well. -/
theorem target_upper :
    anchorNode (commonUnit P p q) (targetTenNodes P p q 4) = targetTenNodes P p q 9 :=
  preReference_shift.{u + 1} (BassH1Components.coefficientMapModel P p)
    (BassH1References.middleIso P p q) (commonUnit P p q) (smallUnit P c)
    (CoefficientLaurentUnitTenNodes.nodes P q 4) (CoefficientLaurentUnitTenNodes.nodes P q 9)
    (ten_shift P q) (common_reference P p q (targetTenNodes P p q 4))

/-- Both full nodes of the original direct-composite W edge. -/
theorem source_nodes (j : Fin 2) :
    sourceUnitNodes P p q j = sourceTenNodes P p q (wFace.toOrderHom j) := by
  fin_cases j
  · exact source_lower P p q
  · exact (congrArg (anchorNode (commonUnit P p q)) (source_lower P p q)).trans
      (source_upper P p q)

/-- Both full nodes of the original q-pre-p W edge. -/
theorem target_nodes (j : Fin 2) :
    targetUnitNodes P p q j = targetTenNodes P p q (wFace.toOrderHom j) := by
  fin_cases j
  · exact target_lower P p q
  · exact (congrArg (anchorNode (commonUnit P p q)) (target_lower P p q)).trans
      (target_upper P p q)

/-- Whole original W rail at unchanged unit time and original direct-composite anchor. -/
theorem source_rail (t : I) :
    unitProductParameter P p q (0, t) =
      mapParameter (anchorNode (eqToIso (BassH0Merge.reference_eq P p q)))
        (parameter (CoefficientLaurentUnitTenNodes.source P (p ≫ q))
          (CoefficientLaurentUnitTenNodes.nodes P (p ≫ q))
          (CoefficientLaurentUnitTenNodes.W t)) := by
  rw [unitProduct_source, mapParameter_parameter]
  rw [w_parameter]
  exact congrArg (fun N : Fin 2 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (edge (k := 1) 0 1 t))
    (funext (source_nodes P p q))

/-- Whole original W rail at unchanged unit time, after precisely the original p and anchor. -/
theorem target_rail (t : I) :
    unitProductParameter P p q (1, t) =
      mapParameter (preReferenceNode (laurentReference P p q)
        (BassH1Components.coefficientMapModel P p) (BassH1References.middleIso P p q))
        (parameter (CoefficientLaurentUnitTenNodes.source P q)
          (CoefficientLaurentUnitTenNodes.nodes P q) (CoefficientLaurentUnitTenNodes.W t)) := by
  rw [unitProduct_target, mapParameter_parameter]
  rw [w_parameter]
  exact congrArg (fun N : Fin 2 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (edge (k := 1) 0 1 t))
    (funext (target_nodes P p q))

/-- Equality of the original arrow transports full anchored nodes, including its references. -/
private theorem anchored_ten_congr {d e : Under R} (w w' : d ⟶ e) (h : w = w')
    (F : modelOf (boundedFlatPerfectWaldhausen (space (op P, d))) ⟶
      modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj e))))
    (ε : F.functor = (CoefficientLaurentUnitTenNodes.source P w).functor)
    (ε' : F.functor = (CoefficientLaurentUnitTenNodes.source P w').functor) (i : Fin 10) :
    anchorNode (eqToIso ε) (CoefficientLaurentUnitTenNodes.nodes P w i) =
      anchorNode (eqToIso ε') (CoefficientLaurentUnitTenNodes.nodes P w' i) := by
  subst w'
  rfl

/-- The actual p;q=l equality, retained as an explicit source-reference transport. -/
theorem actualSourceReferenceEq (d : Under R) :
    (laurentReference P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d)).functor =
      (CoefficientLaurentUnitTenNodes.source P ((laurentUnderCoefficient R).app d)).functor :=
  (BassH0Merge.reference_eq P ((polynomialUnderCoefficient R).app d)
    ((underToLaurent R).app d)).trans
      (congrArg (fun w ↦ (CoefficientLaurentUnitTenNodes.source P w).functor)
        (polynomialUnderCoefficient_toLaurent R d))

/-- Both full actual direct-l nodes, rather than silently replacing the composite by l. -/
theorem actual_source_nodes (d : Under R) (j : Fin 2) :
    sourceUnitNodes P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) j =
      anchorNode (eqToIso (actualSourceReferenceEq P d))
        (CoefficientLaurentUnitTenNodes.nodes P ((laurentUnderCoefficient R).app d)
          (wFace.toOrderHom j)) :=
  (source_nodes P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) j).trans
    (anchored_ten_congr P _ _ (polynomialUnderCoefficient_toLaurent R d) _ _ _ _)

/-- Whole original direct-l W edge after that exact source cast, at every unit time. -/
theorem actual_source_rail (d : Under R) (t : I) :
    unitProductParameter P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) (0, t) =
      mapParameter (anchorNode (eqToIso (actualSourceReferenceEq P d)))
        (parameter (CoefficientLaurentUnitTenNodes.source P ((laurentUnderCoefficient R).app d))
          (CoefficientLaurentUnitTenNodes.nodes P ((laurentUnderCoefficient R).app d))
          (CoefficientLaurentUnitTenNodes.W t)) := by
  rw [unitProduct_source, mapParameter_parameter, w_parameter]
  exact congrArg (fun N : Fin 2 → Node
      (laurentReference P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)) ↦
    parameter _ N (edge (k := 1) 0 1 t)) (funext (actual_source_nodes P d))

end Quillen.PerfectComplexes.CoefficientBassPositiveC0TenNodes
