/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialRectangle
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputLowerNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompLowerFamily

/-!
# The six original Laurent triple rows under polynomial chart restriction

The actual input and postcomposition lower nodes are identified with the full binary
rows in each of the three original split triples. The chart at the source, the fixed
polynomial target reference, and the middle and last source isomorphisms are retained.
The resulting parameter identities apply before native evaluation and keep the binary clock.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleLowerFaces
open CommonReferenceNerve BassH0Merge BassH1Join
open CoefficientBassRaw1PolynomialTripleAnchor

section Triple
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The original entire split triple, with its own Laurent source reference. -/
def tripleNodes (i : Fin 8) : Node (laurentReference P p q w) :=
  ⟨SplitTripleSimplex.vertices (laurentArrow P w) (laurentArrow P q) (laurentArrow P p) i,
    SplitTripleSimplex.references (laurentArrow P w) (laurentArrow P q) (laurentArrow P p) i⟩

/-- The exact node operation on the actual input cap's height-zero face. -/
def inputNode (N : Node (CoefficientBassLaurentCompositionCarrier.reference P q w)) :
    Node (polynomialReference P p q w ≫ normalizedMap (chart P β d)) :=
  CommonReferenceProduct.reanchor (inputLowerIso P β p q w)
    (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β p q w).symm
      (CommonReferenceProduct.node
        (CoefficientBassRaw1ChartCompositionProduct.reference P β p q w)
        (CoefficientBassRaw1ChartCompositionProduct.chartReference P β p)
        (CoefficientBassLaurentCompositionCarrier.reference P q w) (Iso.refl _)
        (CoefficientBassRaw1ChartCompositionProduct.chartNodes P β p 2) N))

/-- The exact node operation on the actual postcomposition cap's height-zero face. -/
def postcompNodeLower
    (N : Node (CoefficientBassLaurentCompositionCarrier.reference P p q)) :
    Node (polynomialReference P p q w ≫ normalizedMap (chart P β d)) :=
  CommonReferenceProduct.reanchor (postcompLowerIso P β p q w)
    (postcompNode (normalizedMap (laurentArrow P w))
      (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q)
        (precompNode (BassMWholeNerve.coefficientModel P (β.app a)) N)))

/-- The input cap's whole binary row is the original right row of the split triple. -/
theorem input_node_row (i : Fin 3) :
    inputNode P β p q w (CoefficientBassLaurentCompositionCarrier.nodes P q w i) =
      CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
        (precompNode (normalizedMap (chart P β a))
          (tripleNodes P p q w (rightIndex i))) := by
  rw [inputNode, input_lower_node]
  apply congrArg (fun N ↦ CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
    (precompNode (normalizedMap (chart P β a)) N))
  symm
  simpa only [tripleRightNode, rightRowReference, Iso.refl_trans,
    preBinaryNodes, CommonReferenceProduct.reanchor, precompNode, tripleNodes] using
    (triple_right_row (laurentReference P p q w)
        (laurentArrow P w) (laurentArrow P q) (laurentArrow P p) (Iso.refl _) i)

/-- The postcomposition cap's whole binary row is the original left split-triple column. -/
theorem postcomp_node_row (i : Fin 3) :
    postcompNodeLower P β p q w (CoefficientBassLaurentCompositionCarrier.nodes P p q i) =
      CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
        (precompNode (normalizedMap (chart P β a))
          (tripleNodes P p q w (leftIndex i))) := by
  rw [postcompNodeLower, postcomp_lower_node]
  apply congrArg (fun N ↦ CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
    (precompNode (normalizedMap (chart P β a)) N))
  symm
  simpa only [Iso.refl_trans, postReferenceNode,
    BinaryNormalizationSimplex.total, NormalizedTripleSimplex.leftFirst,
    CommonReferenceProduct.reanchor, postcompNode, tripleNodes] using
    (triple_left_column_iso (laurentReference P p q w)
        (laurentArrow P w) (laurentArrow P q) (laurentArrow P p) (Iso.refl _) i)
/-- The row-node operation is exactly the actual input lower family before sheet inclusion. -/
theorem input_node_family (r : I) :
    mapParameter (inputNode P β p q w)
      (CoefficientBassLaurentCompositionCarrier.family P q w r) =
    mapParameter (CommonReferenceProduct.reanchor (inputLowerIso P β p q w))
      (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β p q w).symm)
        (CoefficientBassRaw1ChartCompositionProduct.family P β p q w (r, 0))) := by
  have h := input_lower_family P β p q w r
  refine Eq.trans ?_ h.symm
  exact congrArg (fun g ↦ mapParameter g
    (CoefficientBassLaurentCompositionCarrier.family P q w r))
    (funext (input_lower_node P β p q w))

/-- The row-node operation is exactly the postcomposition lower family before sheet inclusion. -/
theorem postcomp_node_family (r : I) :
    mapParameter (postcompNodeLower P β p q w)
      (CoefficientBassLaurentCompositionCarrier.family P p q r) =
    mapParameter (CommonReferenceProduct.reanchor (postcompLowerIso P β p q w))
      (mapParameter (postcompNode (normalizedMap (laurentArrow P w)))
        (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q (r, 0))) := by
  have h := postcomp_lower_family P p q w β r
  refine Eq.trans ?_ h.symm
  exact congrArg (fun g ↦ mapParameter g
    (CoefficientBassLaurentCompositionCarrier.family P p q r))
    (funext (postcomp_lower_node P β p q w))

end Triple

private theorem transport_node {U V W : Model.{u}} (A : U ⟶ V)
    {F G : V ⟶ W} {K T : U ⟶ W}
    (ε : (A ≫ F).functor ≅ K.functor) (ρ : F.functor ≅ G.functor)
    (η : (A ≫ G).functor ≅ T.functor) (N : Node G) :
    CommonReferenceProduct.reanchor
      (ε.symm ≪≫ isoWhiskerLeft A.functor ρ ≪≫ η)
      (CommonReferenceProduct.reanchor η.symm (precompNode A N)) =
    CommonReferenceProduct.reanchor ε.symm
      (precompNode A (CommonReferenceProduct.reanchor ρ N)) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [CommonReferenceProduct.reanchor, precompNode, Iso.trans_assoc,
    Iso.self_symm_id_assoc, isoWhiskerLeft_trans]

private theorem parameter_row {V₀ W₀ V₁ W₁ V₂ W₂ : Model.{u}}
    {F : V₀ ⟶ W₀} {G : V₁ ⟶ W₁} {H : V₂ ⟶ W₂}
    (f : Node F → Node G) (g : Node G → Node H)
    (N : Fin 3 → Node F) (M : Fin 18 → Node H) (ι : ⦋2⦌ ⟶ ⦋17⦌)
    (h : ∀ i, g (f (N i)) = M (ι.toOrderHom i)) (x : StdSimplex ℝ (Fin 3)) :
    mapParameter g (mapParameter f (parameter F N x)) =
      parameter H M (StdSimplex.map ι.toOrderHom x) := by
  rw [mapParameter_parameter, mapParameter_parameter, parameter_face]
  exact congrArg (fun K ↦ parameter H K x) (funext h)

private theorem iso_refl_cancel {C : Type*} [Category* C] {X Y : C} (e : X ≅ Y) :
    e.symm ≪≫ Iso.refl X ≪≫ e = Iso.refl Y := by
  simp

private def totalChartIso {A B C D : Scheme.{u}} (s : C ⟶ A) (t : D ⟶ B)
    (p : B ⟶ A) (l : D ⟶ C) (h : l ≫ s = t ≫ p) :
    (normalizedMap s ≫ normalizedMap l).functor ≅
      (normalizedMap p ≫ normalizedMap t).functor :=
  (BinaryNormalizationSimplex.total l s).symm ≪≫
    NativeSquareFiveSimplex.sourceIso l s t p h ≪≫ BinaryNormalizationSimplex.total t p

private theorem totalChartIso_congr {A B C D : Scheme.{u}} (s : C ⟶ A) (t : D ⟶ B)
    (p p' : B ⟶ A) (l l' : D ⟶ C)
    (h : l ≫ s = t ≫ p) (h' : l' ≫ s = t ≫ p') (hp : p = p') (hl : l = l') :
    (totalChartIso s t p l h).symm ≪≫
        isoWhiskerLeft (normalizedMap s).functor
          (eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) hl)) ≪≫
      totalChartIso s t p' l' h' =
    isoWhiskerRight (eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) hp))
      (normalizedMap t).functor := by
  subst p'
  subst l'
  simp only [eqToIso_refl, isoWhiskerLeft_refl, isoWhiskerRight_refl]
  exact iso_refl_cancel (totalChartIso s t p l h)

private theorem middle_anchor_eq {A B C B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (q' : C' ⟶ B') (b : B' ⟶ B) (c : C' ⟶ C)
    (hq : c ≫ q = q' ≫ b) :
    DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq =
      eqToIso (congrArg (fun k ↦ (normalizedMap k).functor)
        (DoubleSquareTrack.middle_eq p q q' b c hq).symm) :=
  BassReferenceMerge.smallIso_eqToIso _

private theorem last_anchor_eq {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b) :
    DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq =
      eqToIso (congrArg (fun k ↦ (normalizedMap k).functor)
        ((DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm.trans
          (Category.assoc q' p' a))) :=
  BassReferenceMerge.smallIso_eqToIso _

section Rectangle
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

/-- The target reference of every lower row is the same original polynomial triple and chart. -/
abbrev targetReference := CoefficientBassRaw1PolynomialReference.polynomialReference P α f ≫
  CoefficientBassRaw1PolynomialReference.chartMap P β (b := b)

/-- The fixed Laurent18 nodes, first restricted through the source chart, then reanchored. -/
def nodes (i : Fin 18) : Node (targetReference P α β f) :=
  CommonReferenceProduct.reanchor (CoefficientBassRaw1PolynomialReference.referenceIso P α β f).symm
    (CoefficientBassRaw1LaurentChartRestriction.nodes P α β f i)

/-- The middle triple retains the original chart-square transport. -/
abbrev middleAnchor := DoubleSquareCommonSimplex.middleSourceIso
  (CoefficientBassLaurentProjectionScalar.p P (a := a))
  (CoefficientBassLaurentProjectionScalar.q P α (a := a))
  (CoefficientBassLaurentProjectionScalar.q' P α (b := b))
  (CoefficientBassLaurentProjectionScalar.bMap P f)
  (CoefficientBassLaurentProjectionScalar.cMap P f)
  (CoefficientBassLaurentProjectionScalar.chart_square P α f)

/-- The last triple retains both original square transports and association. -/
abbrev lastAnchor := DoubleSquareCommonSimplex.lastSourceIso
  (CoefficientBassLaurentProjectionScalar.p P (a := a))
  (CoefficientBassLaurentProjectionScalar.q P α (a := a))
  (CoefficientBassLaurentProjectionScalar.p' P (b := b))
  (CoefficientBassLaurentProjectionScalar.q' P α (b := b))
  (CoefficientBassLaurentProjectionScalar.aMap P f)
  (CoefficientBassLaurentProjectionScalar.bMap P f)
  (CoefficientBassLaurentProjectionScalar.cMap P f)
  (CoefficientBassLaurentProjectionScalar.polynomial_square P f)
  (CoefficientBassLaurentProjectionScalar.chart_square P α f)

/-- The first full split triple is retained in the fixed Laurent18 reference. -/
theorem first_nodes (i : Fin 8) :
    CoefficientBassLaurentProjectionScalar.nodes P α f
      (DoubleSquareMergedSimplex.firstFace.toOrderHom i) =
    CommonReferenceProduct.reanchor (Iso.refl _) (tripleNodes P ((polynomialUnderCoefficient
        R).app a) (α.app a) ((laurentUnderFunctor R).map f) i) := by
  have h := (DoubleSquareMergedSimplex.first_nodes (CoefficientBassLaurentProjectionScalar.p P (a
      := a))
    (CoefficientBassLaurentProjectionScalar.q P α (a := a))
    (CoefficientBassLaurentProjectionScalar.p' P (b := b))
    (CoefficientBassLaurentProjectionScalar.q' P α (b := b))
    (CoefficientBassLaurentProjectionScalar.aMap P f)
    (CoefficientBassLaurentProjectionScalar.bMap P f)
    (CoefficientBassLaurentProjectionScalar.cMap P f)
    (CoefficientBassLaurentProjectionScalar.polynomial_square P f)
    (CoefficientBassLaurentProjectionScalar.chart_square P α f) i).trans
    (DoubleSquareCommonSimplex.first_nodes (CoefficientBassLaurentProjectionScalar.p P (a := a))
    (CoefficientBassLaurentProjectionScalar.q P α (a := a))
    (CoefficientBassLaurentProjectionScalar.p' P (b := b))
    (CoefficientBassLaurentProjectionScalar.q' P α (b := b))
    (CoefficientBassLaurentProjectionScalar.aMap P f)
    (CoefficientBassLaurentProjectionScalar.bMap P f)
    (CoefficientBassLaurentProjectionScalar.cMap P f)
    (CoefficientBassLaurentProjectionScalar.polynomial_square P f)
    (CoefficientBassLaurentProjectionScalar.chart_square P α f) i)
  simpa only [CoefficientBassLaurentProjectionScalar.nodes, CommonReferenceProduct.reanchor,
    tripleNodes, Iso.refl_trans] using h

/-- The literal first-triple reference transport into the common polynomial target. -/
def firstTransport :=
  (CoefficientBassRaw1PolynomialReference.referenceIso P α β f).symm ≪≫
    isoWhiskerLeft (normalizedMap (chart P β a)).functor (Iso.refl _) ≪≫
      referenceIso P β ((polynomialUnderCoefficient R).app a) (α.app a) ((laurentUnderFunctor
          R).map f)

/-- The actual input lower row of the first triple has its exact Laurent18 nodes. -/
theorem first_input_nodes (i : Fin 3) :
    CommonReferenceProduct.reanchor (firstTransport P α β f)
      (inputNode P β ((polynomialUnderCoefficient R).app a) (α.app a) ((laurentUnderFunctor R).map
          f)
        (CoefficientBassLaurentCompositionCarrier.nodes P (α.app a) ((laurentUnderFunctor R).map
            f) i)) =
    nodes P α β f (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) := by
  rw [input_node_row]
  dsimp only [firstTransport, nodes, CoefficientBassRaw1LaurentChartRestriction.nodes]
  rw [first_nodes]
  exact transport_node (normalizedMap (chart P β a))
    (CoefficientBassRaw1PolynomialReference.referenceIso P α β f)
    (Iso.refl _) (referenceIso P β ((polynomialUnderCoefficient R).app a) (α.app a)
        ((laurentUnderFunctor R).map f)) _

/-- The actual postcomp lower row of the first triple has its exact Laurent18 nodes. -/
theorem first_postcomp_nodes (i : Fin 3) :
    CommonReferenceProduct.reanchor (firstTransport P α β f)
      (postcompNodeLower P β ((polynomialUnderCoefficient R).app a) (α.app a)
          ((laurentUnderFunctor R).map f)
        (CoefficientBassLaurentCompositionCarrier.nodes P ((polynomialUnderCoefficient R).app a)
            (α.app a) i)) =
    nodes P α β f (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) := by
  rw [postcomp_node_row]
  dsimp only [firstTransport, nodes, CoefficientBassRaw1LaurentChartRestriction.nodes]
  rw [first_nodes]
  exact transport_node (normalizedMap (chart P β a))
    (CoefficientBassRaw1PolynomialReference.referenceIso P α β f)
    (Iso.refl _) (referenceIso P β ((polynomialUnderCoefficient R).app a) (α.app a)
        ((laurentUnderFunctor R).map f)) _

/-- The middle full split triple is retained in the fixed Laurent18 reference. -/
theorem middle_nodes (i : Fin 8) :
    CoefficientBassLaurentProjectionScalar.nodes P α f
      (DoubleSquareMergedSimplex.middleFace.toOrderHom i) =
    CommonReferenceProduct.reanchor (middleAnchor P α f) (tripleNodes P
        ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f) (α.app b) i) :=
        by
  have h := (DoubleSquareMergedSimplex.middle_nodes (CoefficientBassLaurentProjectionScalar.p P (a
      := a))
    (CoefficientBassLaurentProjectionScalar.q P α (a := a))
    (CoefficientBassLaurentProjectionScalar.p' P (b := b))
    (CoefficientBassLaurentProjectionScalar.q' P α (b := b))
    (CoefficientBassLaurentProjectionScalar.aMap P f)
    (CoefficientBassLaurentProjectionScalar.bMap P f)
    (CoefficientBassLaurentProjectionScalar.cMap P f)
    (CoefficientBassLaurentProjectionScalar.polynomial_square P f)
    (CoefficientBassLaurentProjectionScalar.chart_square P α f) i).trans
    (DoubleSquareCommonSimplex.middle_nodes (CoefficientBassLaurentProjectionScalar.p P (a := a))
    (CoefficientBassLaurentProjectionScalar.q P α (a := a))
    (CoefficientBassLaurentProjectionScalar.p' P (b := b))
    (CoefficientBassLaurentProjectionScalar.q' P α (b := b))
    (CoefficientBassLaurentProjectionScalar.aMap P f)
    (CoefficientBassLaurentProjectionScalar.bMap P f)
    (CoefficientBassLaurentProjectionScalar.cMap P f)
    (CoefficientBassLaurentProjectionScalar.polynomial_square P f)
    (CoefficientBassLaurentProjectionScalar.chart_square P α f) i)
  simpa only [CoefficientBassLaurentProjectionScalar.nodes, CommonReferenceProduct.reanchor,
    tripleNodes, Iso.refl_trans] using h

/-- The literal middle-triple reference transport into the common polynomial target. -/
def middleTransport :=
  (CoefficientBassRaw1PolynomialReference.referenceIso P α β f).symm ≪≫
    isoWhiskerLeft (normalizedMap (chart P β a)).functor (middleAnchor P α f) ≪≫
      referenceIso P β ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f)
          (α.app b)

/-- The actual input lower row of the middle triple has its exact Laurent18 nodes. -/
theorem middle_input_nodes (i : Fin 3) :
    CommonReferenceProduct.reanchor (middleTransport P α β f)
      (inputNode P β ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f)
          (α.app b)
        (CoefficientBassLaurentCompositionCarrier.nodes P ((polynomialUnderFunctor R).map f)
            (α.app b) i)) =
    nodes P α β f (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) := by
  rw [input_node_row]
  dsimp only [middleTransport, nodes, CoefficientBassRaw1LaurentChartRestriction.nodes]
  rw [middle_nodes]
  exact transport_node (normalizedMap (chart P β a))
    (CoefficientBassRaw1PolynomialReference.referenceIso P α β f)
    (middleAnchor P α f) (referenceIso P β ((polynomialUnderCoefficient R).app a)
        ((polynomialUnderFunctor R).map f) (α.app b)) _

/-- The actual postcomp lower row of the middle triple has its exact Laurent18 nodes. -/
theorem middle_postcomp_nodes (i : Fin 3) :
    CommonReferenceProduct.reanchor (middleTransport P α β f)
      (postcompNodeLower P β ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor
          R).map f) (α.app b)
        (CoefficientBassLaurentCompositionCarrier.nodes P ((polynomialUnderCoefficient R).app a)
            ((polynomialUnderFunctor R).map f) i)) =
    nodes P α β f (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) := by
  rw [postcomp_node_row]
  dsimp only [middleTransport, nodes, CoefficientBassRaw1LaurentChartRestriction.nodes]
  rw [middle_nodes]
  exact transport_node (normalizedMap (chart P β a))
    (CoefficientBassRaw1PolynomialReference.referenceIso P α β f)
    (middleAnchor P α f) (referenceIso P β ((polynomialUnderCoefficient R).app a)
        ((polynomialUnderFunctor R).map f) (α.app b)) _

/-- The last full split triple is retained in the fixed Laurent18 reference. -/
theorem last_nodes (i : Fin 8) :
    CoefficientBassLaurentProjectionScalar.nodes P α f
      (DoubleSquareMergedSimplex.lastFace.toOrderHom i) =
    CommonReferenceProduct.reanchor (lastAnchor P α f) (tripleNodes P (f)
        ((polynomialUnderCoefficient R).app b) (α.app b) i) := by
  have h := (DoubleSquareMergedSimplex.last_nodes (CoefficientBassLaurentProjectionScalar.p P (a
      := a))
    (CoefficientBassLaurentProjectionScalar.q P α (a := a))
    (CoefficientBassLaurentProjectionScalar.p' P (b := b))
    (CoefficientBassLaurentProjectionScalar.q' P α (b := b))
    (CoefficientBassLaurentProjectionScalar.aMap P f)
    (CoefficientBassLaurentProjectionScalar.bMap P f)
    (CoefficientBassLaurentProjectionScalar.cMap P f)
    (CoefficientBassLaurentProjectionScalar.polynomial_square P f)
    (CoefficientBassLaurentProjectionScalar.chart_square P α f) i).trans
    (DoubleSquareCommonSimplex.last_nodes (CoefficientBassLaurentProjectionScalar.p P (a := a))
    (CoefficientBassLaurentProjectionScalar.q P α (a := a))
    (CoefficientBassLaurentProjectionScalar.p' P (b := b))
    (CoefficientBassLaurentProjectionScalar.q' P α (b := b))
    (CoefficientBassLaurentProjectionScalar.aMap P f)
    (CoefficientBassLaurentProjectionScalar.bMap P f)
    (CoefficientBassLaurentProjectionScalar.cMap P f)
    (CoefficientBassLaurentProjectionScalar.polynomial_square P f)
    (CoefficientBassLaurentProjectionScalar.chart_square P α f) i)
  simpa only [CoefficientBassLaurentProjectionScalar.nodes, CommonReferenceProduct.reanchor,
    tripleNodes, Iso.refl_trans] using h

/-- The literal last-triple reference transport into the common polynomial target. -/
def lastTransport :=
  (CoefficientBassRaw1PolynomialReference.referenceIso P α β f).symm ≪≫
    isoWhiskerLeft (normalizedMap (chart P β a)).functor (lastAnchor P α f) ≪≫
      referenceIso P β (f) ((polynomialUnderCoefficient R).app b) (α.app b)

/-- The actual input lower row of the last triple has its exact Laurent18 nodes. -/
theorem last_input_nodes (i : Fin 3) :
    CommonReferenceProduct.reanchor (lastTransport P α β f)
      (inputNode P β (f) ((polynomialUnderCoefficient R).app b) (α.app b)
        (CoefficientBassLaurentCompositionCarrier.nodes P ((polynomialUnderCoefficient R).app b)
            (α.app b) i)) =
    nodes P α β f (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) := by
  rw [input_node_row]
  dsimp only [lastTransport, nodes, CoefficientBassRaw1LaurentChartRestriction.nodes]
  rw [last_nodes]
  exact transport_node (normalizedMap (chart P β a))
    (CoefficientBassRaw1PolynomialReference.referenceIso P α β f)
    (lastAnchor P α f) (referenceIso P β (f) ((polynomialUnderCoefficient R).app b) (α.app b)) _

/-- The actual postcomp lower row of the last triple has its exact Laurent18 nodes. -/
theorem last_postcomp_nodes (i : Fin 3) :
    CommonReferenceProduct.reanchor (lastTransport P α β f)
      (postcompNodeLower P β (f) ((polynomialUnderCoefficient R).app b) (α.app b)
        (CoefficientBassLaurentCompositionCarrier.nodes P (f) ((polynomialUnderCoefficient R).app
            b) i)) =
    nodes P α β f (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) := by
  rw [postcomp_node_row]
  dsimp only [lastTransport, nodes, CoefficientBassRaw1LaurentChartRestriction.nodes]
  rw [last_nodes]
  exact transport_node (normalizedMap (chart P β a))
    (CoefficientBassRaw1PolynomialReference.referenceIso P α β f)
    (lastAnchor P α f) (referenceIso P β (f) ((polynomialUnderCoefficient R).app b) (α.app b)) _

/-- The original ordered right binary row of the split triple. -/
def rightBinaryFace : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨rightIndex, by decide⟩

/-- The original ordered left binary column of the split triple. -/
def leftBinaryFace : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨leftIndex, by decide⟩


/-- Every point of the first input lower row has its unchanged Laurent18 parameter. -/
theorem first_input_parameter (x : StdSimplex ℝ (Fin 3)) :
    mapParameter (CommonReferenceProduct.reanchor (firstTransport P α β f))
      (mapParameter (inputNode P β ((polynomialUnderCoefficient R).app a) (α.app a)
          ((laurentUnderFunctor R).map f))
        (parameter (CoefficientBassLaurentCompositionCarrier.reference P (α.app a)
            ((laurentUnderFunctor R).map f))
          (CoefficientBassLaurentCompositionCarrier.nodes P (α.app a) ((laurentUnderFunctor R).map
              f)) x)) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (fun i ↦ DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) x)
          := by
  exact parameter_row (inputNode P β ((polynomialUnderCoefficient R).app a) (α.app a)
      ((laurentUnderFunctor R).map f))
    (CommonReferenceProduct.reanchor (firstTransport P α β f))
    (CoefficientBassLaurentCompositionCarrier.nodes P (α.app a) ((laurentUnderFunctor R).map f))
        (nodes P α β f)
    (rightBinaryFace ≫ DoubleSquareMergedSimplex.firstFace)
    (first_input_nodes P α β f) x

/-- Every point of the first postcomp lower row has its unchanged Laurent18 parameter. -/
theorem first_postcomp_parameter (x : StdSimplex ℝ (Fin 3)) :
    mapParameter (CommonReferenceProduct.reanchor (firstTransport P α β f))
      (mapParameter (postcompNodeLower P β ((polynomialUnderCoefficient R).app a) (α.app a)
          ((laurentUnderFunctor R).map f))
        (parameter (CoefficientBassLaurentCompositionCarrier.reference P
            ((polynomialUnderCoefficient R).app a) (α.app a))
          (CoefficientBassLaurentCompositionCarrier.nodes P ((polynomialUnderCoefficient R).app a)
              (α.app a)) x)) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (fun i ↦ DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) x) :=
          by
  rw [mapParameter_parameter, mapParameter_parameter]
  have h := parameter_face (targetReference P α β f) (nodes P α β f)
    (leftBinaryFace ≫ DoubleSquareMergedSimplex.firstFace) x
  exact (congrArg (fun N ↦ parameter (targetReference P α β f) N x)
    (funext (first_postcomp_nodes P α β f))).trans h.symm

/-- Every point of the middle input lower row has its unchanged Laurent18 parameter. -/
theorem middle_input_parameter (x : StdSimplex ℝ (Fin 3)) :
    mapParameter (CommonReferenceProduct.reanchor (middleTransport P α β f))
      (mapParameter (inputNode P β ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor
          R).map f) (α.app b))
        (parameter (CoefficientBassLaurentCompositionCarrier.reference P ((polynomialUnderFunctor
            R).map f) (α.app b))
          (CoefficientBassLaurentCompositionCarrier.nodes P ((polynomialUnderFunctor R).map f)
              (α.app b)) x)) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (fun i ↦ DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) x)
          := by
  exact parameter_row (inputNode P β ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b))
    (CommonReferenceProduct.reanchor (middleTransport P α β f))
    (CoefficientBassLaurentCompositionCarrier.nodes P ((polynomialUnderFunctor R).map f) (α.app
        b)) (nodes P α β f)
    (rightBinaryFace ≫ DoubleSquareMergedSimplex.middleFace)
    (middle_input_nodes P α β f) x

/-- Every point of the middle postcomp lower row has its unchanged Laurent18 parameter. -/
theorem middle_postcomp_parameter (x : StdSimplex ℝ (Fin 3)) :
    mapParameter (CommonReferenceProduct.reanchor (middleTransport P α β f))
      (mapParameter (postcompNodeLower P β ((polynomialUnderCoefficient R).app a)
          ((polynomialUnderFunctor R).map f) (α.app b))
        (parameter (CoefficientBassLaurentCompositionCarrier.reference P
            ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f))
          (CoefficientBassLaurentCompositionCarrier.nodes P ((polynomialUnderCoefficient R).app a)
              ((polynomialUnderFunctor R).map f)) x)) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (fun i ↦ DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) x)
          := by
  exact parameter_row (postcompNodeLower P β ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b))
    (CommonReferenceProduct.reanchor (middleTransport P α β f))
    (CoefficientBassLaurentCompositionCarrier.nodes P ((polynomialUnderCoefficient R).app a)
        ((polynomialUnderFunctor R).map f)) (nodes P α β f)
    (leftBinaryFace ≫ DoubleSquareMergedSimplex.middleFace)
    (middle_postcomp_nodes P α β f) x

/-- Every point of the last input lower row has its unchanged Laurent18 parameter. -/
theorem last_input_parameter (x : StdSimplex ℝ (Fin 3)) :
    mapParameter (CommonReferenceProduct.reanchor (lastTransport P α β f))
      (mapParameter (inputNode P β (f) ((polynomialUnderCoefficient R).app b) (α.app b))
        (parameter (CoefficientBassLaurentCompositionCarrier.reference P
            ((polynomialUnderCoefficient R).app b) (α.app b))
          (CoefficientBassLaurentCompositionCarrier.nodes P ((polynomialUnderCoefficient R).app b)
              (α.app b)) x)) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (fun i ↦ DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) x) :=
          by
  exact parameter_row (inputNode P β f ((polynomialUnderCoefficient R).app b) (α.app b))
    (CommonReferenceProduct.reanchor (lastTransport P α β f))
    (CoefficientBassLaurentCompositionCarrier.nodes P ((polynomialUnderCoefficient R).app b)
      (α.app b)) (nodes P α β f)
    (rightBinaryFace ≫ DoubleSquareMergedSimplex.lastFace)
    (last_input_nodes P α β f) x

/-- Every point of the last postcomp lower row has its unchanged Laurent18 parameter. -/
theorem last_postcomp_parameter (x : StdSimplex ℝ (Fin 3)) :
    mapParameter (CommonReferenceProduct.reanchor (lastTransport P α β f))
      (mapParameter (postcompNodeLower P β (f) ((polynomialUnderCoefficient R).app b) (α.app b))
        (parameter (CoefficientBassLaurentCompositionCarrier.reference P (f)
            ((polynomialUnderCoefficient R).app b))
          (CoefficientBassLaurentCompositionCarrier.nodes P (f) ((polynomialUnderCoefficient
              R).app b)) x)) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (fun i ↦ DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) x) := by
  exact parameter_row (postcompNodeLower P β (f) ((polynomialUnderCoefficient R).app b) (α.app b))
    (CommonReferenceProduct.reanchor (lastTransport P α β f))
    (CoefficientBassLaurentCompositionCarrier.nodes P (f) ((polynomialUnderCoefficient R).app b))
        (nodes P α β f)
    (leftBinaryFace ≫ DoubleSquareMergedSimplex.lastFace)
    (last_postcomp_nodes P α β f) x


/-- The first lower transport is the identity of the original polynomial target reference. -/
theorem first_transport : firstTransport P α β f = Iso.refl _ :=
  iso_refl_cancel (CoefficientBassRaw1PolynomialReference.referenceIso P α β f)

/-- The middle Laurent chart transport is exactly the original polynomial anchor whiskering. -/
theorem middle_transport : middleTransport P α β f =
    isoWhiskerRight (CoefficientBassRaw1PolynomialRectangle.middleAnchor P α f)
      (CoefficientBassRaw1PolynomialReference.chartMap P β (b := b)).functor := by
  dsimp only [middleTransport, middleAnchor,
    CoefficientBassRaw1PolynomialRectangle.middleAnchor]
  rw [middle_anchor_eq, middle_anchor_eq]
  exact totalChartIso_congr
    (CoefficientBassRaw1PolynomialReference.sourceChart P β (a := a))
    (CoefficientBassRaw1PolynomialReference.targetChart P β (b := b))
    (CoefficientBassRaw1PolynomialReference.polynomialTotal P α f)
    (polynomialTotal P ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f)
        (α.app b))
    (CoefficientBassRaw1PolynomialReference.laurentTotal P α f)
    (laurentTotal P ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f)
        (α.app b))
    (CoefficientBassRaw1PolynomialReference.total_naturality P α β f)
    (total_naturality P β ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map
        f) (α.app b))
    ((DoubleSquareTrack.middle_eq
      (CoefficientBassRaw1PolynomialReference.first P (a := a))
          (CoefficientBassRaw1PolynomialReference.second P α (a := a))
          (CoefficientBassRaw1PolynomialReference.second P α (a := b))
      (CoefficientBassRaw1PolynomialRectangle.bMap P f)
          (CoefficientBassRaw1PolynomialReference.last P f)
          (CoefficientBassRaw1PolynomialRectangle.chart_square P α f)).symm)
    ((DoubleSquareTrack.middle_eq
      (CoefficientBassLaurentProjectionScalar.p P (a := a))
          (CoefficientBassLaurentProjectionScalar.q P α (a := a))
          (CoefficientBassLaurentProjectionScalar.q' P α (b := b))
      (CoefficientBassLaurentProjectionScalar.bMap P f)
          (CoefficientBassLaurentProjectionScalar.cMap P f)
          (CoefficientBassLaurentProjectionScalar.chart_square P α f)).symm)

/-- The last Laurent chart transport is exactly the original polynomial anchor whiskering. -/
theorem last_transport : lastTransport P α β f =
    isoWhiskerRight (CoefficientBassRaw1PolynomialRectangle.lastAnchor P α f)
      (CoefficientBassRaw1PolynomialReference.chartMap P β (b := b)).functor := by
  dsimp only [lastTransport, lastAnchor,
    CoefficientBassRaw1PolynomialRectangle.lastAnchor]
  rw [last_anchor_eq, last_anchor_eq]
  exact totalChartIso_congr
    (CoefficientBassRaw1PolynomialReference.sourceChart P β (a := a))
    (CoefficientBassRaw1PolynomialReference.targetChart P β (b := b))
    (CoefficientBassRaw1PolynomialReference.polynomialTotal P α f)
    (polynomialTotal P (f) ((polynomialUnderCoefficient R).app b) (α.app b))
    (CoefficientBassRaw1PolynomialReference.laurentTotal P α f)
    (laurentTotal P (f) ((polynomialUnderCoefficient R).app b) (α.app b))
    (CoefficientBassRaw1PolynomialReference.total_naturality P α β f)
    (total_naturality P β (f) ((polynomialUnderCoefficient R).app b) (α.app b))
    (((DoubleSquareTrack.total_eq
      (CoefficientBassRaw1PolynomialReference.first P (a := a))
          (CoefficientBassRaw1PolynomialReference.second P α (a := a))
          (CoefficientBassRaw1PolynomialReference.first P (a := b))
          (CoefficientBassRaw1PolynomialReference.second P α (a := b))
      (CoefficientBassRaw1PolynomialRectangle.aMap P f)
          (CoefficientBassRaw1PolynomialRectangle.bMap P f)
          (CoefficientBassRaw1PolynomialReference.last P f)
      (CoefficientBassRaw1PolynomialRectangle.polynomial_square P f)
          (CoefficientBassRaw1PolynomialRectangle.chart_square P α f)).symm.trans (Category.assoc
          (CoefficientBassRaw1PolynomialReference.second P α (a := b))
          (CoefficientBassRaw1PolynomialReference.first P (a := b))
          (CoefficientBassRaw1PolynomialRectangle.aMap P f))))
    (((DoubleSquareTrack.total_eq
      (CoefficientBassLaurentProjectionScalar.p P (a := a))
          (CoefficientBassLaurentProjectionScalar.q P α (a := a))
          (CoefficientBassLaurentProjectionScalar.p' P (b := b))
          (CoefficientBassLaurentProjectionScalar.q' P α (b := b))
      (CoefficientBassLaurentProjectionScalar.aMap P f)
          (CoefficientBassLaurentProjectionScalar.bMap P f)
          (CoefficientBassLaurentProjectionScalar.cMap P f)
      (CoefficientBassLaurentProjectionScalar.polynomial_square P f)
          (CoefficientBassLaurentProjectionScalar.chart_square P α f)).symm.trans (Category.assoc
          (CoefficientBassLaurentProjectionScalar.q' P α (b := b))
          (CoefficientBassLaurentProjectionScalar.p' P (b := b))
          (CoefficientBassLaurentProjectionScalar.aMap P f))))



/-- The first input lower family retains the complete original binary clock. -/
theorem first_input_family (r : I) :
    mapParameter (CommonReferenceProduct.reanchor (firstTransport P α β f))
      (mapParameter (inputNode P β ((polynomialUnderCoefficient R).app a) (α.app a)
          ((laurentUnderFunctor R).map f))
        (CoefficientBassLaurentCompositionCarrier.family P (α.app a) ((laurentUnderFunctor R).map
            f) r)) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (fun i ↦ DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))
        (binaryPath (k := 2) 0 1 2 r)) :=
  first_input_parameter P α β f (binaryPath (k := 2) 0 1 2 r)

/-- The first postcomp lower family retains the complete original binary clock. -/
theorem first_postcomp_family (r : I) :
    mapParameter (CommonReferenceProduct.reanchor (firstTransport P α β f))
      (mapParameter (postcompNodeLower P β ((polynomialUnderCoefficient R).app a) (α.app a)
          ((laurentUnderFunctor R).map f))
        (CoefficientBassLaurentCompositionCarrier.family P ((polynomialUnderCoefficient R).app a)
            (α.app a) r)) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (fun i ↦ DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i))
        (binaryPath (k := 2) 0 1 2 r)) :=
  first_postcomp_parameter P α β f (binaryPath (k := 2) 0 1 2 r)

/-- The middle input lower family retains the complete original binary clock. -/
theorem middle_input_family (r : I) :
    mapParameter (CommonReferenceProduct.reanchor (middleTransport P α β f))
      (mapParameter (inputNode P β ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor
          R).map f) (α.app b))
        (CoefficientBassLaurentCompositionCarrier.family P ((polynomialUnderFunctor R).map f)
            (α.app b) r)) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (fun i ↦ DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))
        (binaryPath (k := 2) 0 1 2 r)) :=
  middle_input_parameter P α β f (binaryPath (k := 2) 0 1 2 r)

/-- The middle postcomp lower family retains the complete original binary clock. -/
theorem middle_postcomp_family (r : I) :
    mapParameter (CommonReferenceProduct.reanchor (middleTransport P α β f))
      (mapParameter (postcompNodeLower P β ((polynomialUnderCoefficient R).app a)
          ((polynomialUnderFunctor R).map f) (α.app b))
        (CoefficientBassLaurentCompositionCarrier.family P ((polynomialUnderCoefficient R).app a)
            ((polynomialUnderFunctor R).map f) r)) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (fun i ↦ DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i))
        (binaryPath (k := 2) 0 1 2 r)) :=
  middle_postcomp_parameter P α β f (binaryPath (k := 2) 0 1 2 r)

/-- The last input lower family retains the complete original binary clock. -/
theorem last_input_family (r : I) :
    mapParameter (CommonReferenceProduct.reanchor (lastTransport P α β f))
      (mapParameter (inputNode P β (f) ((polynomialUnderCoefficient R).app b) (α.app b))
        (CoefficientBassLaurentCompositionCarrier.family P ((polynomialUnderCoefficient R).app b)
            (α.app b) r)) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (fun i ↦ DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))
        (binaryPath (k := 2) 0 1 2 r)) :=
  last_input_parameter P α β f (binaryPath (k := 2) 0 1 2 r)

/-- The last postcomp lower family retains the complete original binary clock. -/
theorem last_postcomp_family (r : I) :
    mapParameter (CommonReferenceProduct.reanchor (lastTransport P α β f))
      (mapParameter (postcompNodeLower P β (f) ((polynomialUnderCoefficient R).app b) (α.app b))
        (CoefficientBassLaurentCompositionCarrier.family P (f) ((polynomialUnderCoefficient R).app
            b) r)) =
    parameter (targetReference P α β f) (nodes P α β f)
      (StdSimplex.map (fun i ↦ DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i))
        (binaryPath (k := 2) 0 1 2 r)) :=
  last_postcomp_parameter P α β f (binaryPath (k := 2) 0 1 2 r)

end Rectangle
end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleLowerFaces
