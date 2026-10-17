/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialRadialCaps

/-!
# The two original total-pair caps in a polynomial triple sheet

Full source-reference normalization places the corrected caps for `(p ≫ q, w)` and
`(p, q ≫ w)` in the original triple sheet. Every transport is induced by the polynomial
or Laurent functor's composition equality, retaining the original cap and both clocks.
The lower faces are identified on complete reference nodes before realization.
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialRadialCaps
open CommonReferenceNerve BassH0Merge BassReferenceMerge
open CoefficientBassRaw1PolynomialTripleAnchor CoefficientBassRaw1PolynomialTripleLowerFaces

private theorem reanchor_eq_trans {V W : Model.{u}} {F G H : V ⟶ W}
    (h : F.functor = G.functor) (h' : G.functor = H.functor)
    (h'' : F.functor = H.functor) (N : Node H) :
    CommonReferenceProduct.reanchor (eqToIso h'') N =
      CommonReferenceProduct.reanchor (eqToIso h)
        (CommonReferenceProduct.reanchor (eqToIso h') N) := by
  rcases N with ⟨K, ρ⟩
  exact congrArg (fun e ↦ (⟨K, e⟩ : Node F))
    ((congrArg (fun e ↦ e ≪≫ ρ) (eqToIso_trans h h').symm).trans (Iso.trans_assoc _ _ _))

private theorem binary_nodes_congr {X Y Z : Scheme.{u}} (f f' : X ⟶ Y) (g g' : Y ⟶ Z)
    (hf : f = f') (hg : g = g') (i : Fin 3) :
    CommonReferenceProduct.reanchor
      (eqToIso (congrArg (fun k ↦ (normalizedMap k).functor)
        (congrArg₂ (fun x y ↦ x ≫ y) hf hg))) (binaryNodes f' g' i) =
      binaryNodes f g i := by
  subst f'
  subst g'
  rcases binaryNodes f g i with ⟨K, ρ⟩
  simp only [CommonReferenceProduct.reanchor, eqToIso_refl, Iso.refl_trans]

private theorem right_binary_nodes {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ T) (i : Fin 3) :
    CommonReferenceProduct.reanchor
      (eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) (Category.assoc f g h).symm))
      (binaryNodes (f ≫ g) h i) =
    (⟨SplitTripleSimplex.vertices f g h (rightIndex i),
      SplitTripleSimplex.references f g h (rightIndex i)⟩ :
        Node (NormalizedTripleSimplex.sourceMap f g h)) := by
  fin_cases i
  · symm
    apply ModelSimplex.reference_node_eq
      (congrArg (fun k ↦ (normalizedMap k).functor) (Category.assoc f g h).symm)
    change (Iso.refl (NormalizedTripleSimplex.sourceMap f g h).functor).hom ≫
      eqToHom _ = (eqToIso _ ≪≫ Iso.refl _).hom
    simp
  · apply Sigma.ext rfl
    apply heq_of_eq
    exact (congrArg (fun e ↦ e ≪≫ BinaryNormalizationSimplex.first (f ≫ g) h)
      (smallIso_eqToIso (congrArg boundedFlatNormalizedPullback
        (Category.assoc f g h).symm))).symm.trans (smallIso_trans _ _).symm
  · apply Sigma.ext rfl
    apply heq_of_eq
    exact (congrArg (fun e ↦ e ≪≫ BinaryNormalizationSimplex.total (f ≫ g) h)
      (smallIso_eqToIso (congrArg boundedFlatNormalizedPullback
        (Category.assoc f g h).symm))).symm.trans (smallIso_trans _ _).symm

private def chartLowerIso {A B C D : Scheme.{u}} (s : C ⟶ A) (t : D ⟶ B)
    (p : B ⟶ A) (l : D ⟶ C) (h : t ≫ p = l ≫ s) :=
  (BinaryNormalizationSimplex.total t p).symm ≪≫
    eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) h) ≪≫
      BinaryNormalizationSimplex.total l s

private theorem chartLowerIso_congr {A B C D : Scheme.{u}} (s : C ⟶ A) (t : D ⟶ B)
    (p p' : B ⟶ A) (l l' : D ⟶ C)
    (h : t ≫ p = l ≫ s) (h' : t ≫ p' = l' ≫ s) (hp : p = p') (hl : l = l') :
    isoWhiskerRight (eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) hp))
        (normalizedMap t).functor ≪≫ chartLowerIso s t p' l' h' =
      chartLowerIso s t p l h ≪≫ isoWhiskerLeft (normalizedMap s).functor
        (eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) hl)) := by
  subst p'
  subst l'
  simp only [eqToIso_refl, isoWhiskerLeft_refl, isoWhiskerRight_refl,
    Iso.refl_trans]
  exact (Iso.trans_refl (chartLowerIso s t p l h)).symm

private theorem chart_inverse {A B C D : Scheme.{u}} (s : C ⟶ A) (t : D ⟶ B)
    (p : B ⟶ A) (l : D ⟶ C) (h : l ≫ s = t ≫ p) :
    ((BinaryNormalizationSimplex.total l s).symm ≪≫
      eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) h) ≪≫
        BinaryNormalizationSimplex.total t p).symm = chartLowerIso s t p l h.symm := by
  apply Iso.ext
  simp only [chartLowerIso, Iso.trans_inv, Iso.symm_hom, Iso.trans_hom, Iso.symm_inv,
    eqToIso.inv, eqToIso.hom]
  exact Category.assoc _ _ _

private theorem normalized_node {U V W : Model.{u}} (A : U ⟶ V)
    {F G : V ⟶ W} {T S : U ⟶ W}
    (δ : T.functor ≅ S.functor) (e : S.functor ≅ (A ≫ F).functor)
    (e' : T.functor ≅ (A ≫ G).functor) (ρ₀ : G.functor ≅ F.functor)
    (h : δ ≪≫ e = e' ≪≫ isoWhiskerLeft A.functor ρ₀) (N : Node F) :
    CommonReferenceProduct.reanchor δ (CommonReferenceProduct.reanchor e (precompNode A N)) =
      CommonReferenceProduct.reanchor e'
        (precompNode A (CommonReferenceProduct.reanchor ρ₀ N)) := by
  rcases N with ⟨K, ρ⟩
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change δ ≪≫ e ≪≫ isoWhiskerLeft A.functor ρ =
    e' ≪≫ isoWhiskerLeft A.functor (ρ₀ ≪≫ ρ)
  rw [isoWhiskerLeft_trans, ← Iso.trans_assoc, h, Iso.trans_assoc]

section Triple
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The complete left radial Laurent row is unchanged after its actual total transport. -/
theorem left_nodes (i : Fin 3) :
    CommonReferenceProduct.reanchor (leftLaurentIso P p q w)
      (CoefficientBassLaurentCompositionCarrier.nodes P (p ≫ q) w i) =
      tripleNodes P p q w (leftIndex i) := by
  have h := binary_nodes_congr (laurentArrow P w) (laurentArrow P w)
    (laurentArrow P q ≫ laurentArrow P p) (laurentArrow P (p ≫ q)) rfl
    (by simp only [laurentArrow, Functor.map_comp, coefficientMap_comp]) i
  refine h.trans ?_
  fin_cases i <;> rfl

/-- The complete right radial Laurent row retains the original association transport. -/
theorem right_nodes (i : Fin 3) :
    CommonReferenceProduct.reanchor (rightLaurentIso P p q w)
      (CoefficientBassLaurentCompositionCarrier.nodes P p (q ≫ w) i) =
      tripleNodes P p q w (rightIndex i) := by
  have h := binary_nodes_congr (laurentArrow P w ≫ laurentArrow P q)
    (laurentArrow P (q ≫ w)) (laurentArrow P p) (laurentArrow P p)
    (by simp only [laurentArrow, Functor.map_comp, coefficientMap_comp]) rfl i
  have hh := congrArg (CommonReferenceProduct.reanchor
    (eqToIso (congrArg (fun k ↦ (normalizedMap k).functor)
      (Category.assoc (laurentArrow P w) (laurentArrow P q) (laurentArrow P p)).symm))) h
  refine Eq.trans ?_ (hh.trans (right_binary_nodes (laurentArrow P w) (laurentArrow P q)
    (laurentArrow P p) i))
  exact reanchor_eq_trans _ _ _ _


private theorem pair_chartLowerIso {e f g : Under R} (k : e ⟶ f) (l : f ⟶ g) :
    CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β k l =
    chartLowerIso (chart P β e) (chart P β g)
      (polynomialArrow P l ≫ polynomialArrow P k) (laurentArrow P l ≫ laurentArrow P k)
      (CoefficientBassRaw1PolynomialLowerNormalization.pair_naturality P β k l) := by
  rw [CoefficientBassRaw1PolynomialLowerNormalization.lowerAnchor_normalized, smallIso_eqToIso]
  rfl

private theorem triple_chartLowerIso : (referenceIso P β p q w).symm =
    chartLowerIso (chart P β a) (chart P β d) (polynomialTotal P p q w)
      (laurentTotal P p q w) (total_naturality P β p q w).symm := by
  exact chart_inverse (chart P β a) (chart P β d) (polynomialTotal P p q w)
    (laurentTotal P p q w) (total_naturality P β p q w)

/-- Complete polynomial normalization commutes with the original left radial chart anchor. -/
theorem left_anchor :
    isoWhiskerRight (leftPolynomialIso P p q w) (normalizedMap (chart P β d)).functor ≪≫
      CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β (p ≫ q) w =
    (referenceIso P β p q w).symm ≪≫
      isoWhiskerLeft (normalizedMap (chart P β a)).functor (leftLaurentIso P p q w) := by
  rw [pair_chartLowerIso, triple_chartLowerIso]
  exact chartLowerIso_congr _ _ _ _ _ _ _ _ (leftPolynomialEq P p q w) (leftLaurentEq P p q w)

/-- Complete polynomial normalization commutes with the original right radial chart anchor. -/
theorem right_anchor :
    isoWhiskerRight (rightPolynomialIso P p q w) (normalizedMap (chart P β d)).functor ≪≫
      CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p (q ≫ w) =
    (referenceIso P β p q w).symm ≪≫
      isoWhiskerLeft (normalizedMap (chart P β a)).functor (rightLaurentIso P p q w) := by
  rw [pair_chartLowerIso, triple_chartLowerIso]
  exact chartLowerIso_congr _ _ _ _ _ _ _ _ (rightPolynomialEq P p q w) (rightLaurentEq P p q w)

/-- Every complete left radial lower node is the source-chart restriction of its triple node. -/
theorem left_lower_nodes (i : Fin 3) :
    CommonReferenceProduct.reanchor
      (isoWhiskerRight (leftPolynomialIso P p q w) (normalizedMap (chart P β d)).functor)
      (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β (p ≫ q) w)
        (precompNode (normalizedMap (chart P β a))
          (CoefficientBassLaurentCompositionCarrier.nodes P (p ≫ q) w i))) =
    CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
      (precompNode (normalizedMap (chart P β a)) (tripleNodes P p q w (leftIndex i))) := by
  exact (normalized_node (normalizedMap (chart P β a)) _ _ _ _
    (left_anchor P β p q w) _).trans
    (congrArg (fun N ↦ CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
      (precompNode (normalizedMap (chart P β a)) N)) (left_nodes P p q w i))

/-- Every complete right radial lower node retains its original triple association. -/
theorem right_lower_nodes (i : Fin 3) :
    CommonReferenceProduct.reanchor
      (isoWhiskerRight (rightPolynomialIso P p q w) (normalizedMap (chart P β d)).functor)
      (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p (q ≫ w))
        (precompNode (normalizedMap (chart P β a))
          (CoefficientBassLaurentCompositionCarrier.nodes P p (q ≫ w) i))) =
    CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
      (precompNode (normalizedMap (chart P β a)) (tripleNodes P p q w (rightIndex i))) := by
  exact (normalized_node (normalizedMap (chart P β a)) _ _ _ _
    (right_anchor P β p q w) _).trans
    (congrArg (fun N ↦ CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
      (precompNode (normalizedMap (chart P β a)) N)) (right_nodes P p q w i))

/-- The entire left radial binary parameter is retained before sheet inclusion. -/
theorem left_lower_parameter (x : StdSimplex ℝ (Fin 3)) :
    mapParameter (CommonReferenceProduct.reanchor
      (isoWhiskerRight (leftPolynomialIso P p q w) (normalizedMap (chart P β d)).functor))
      (mapParameter (fun N ↦ CommonReferenceProduct.reanchor
        (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β (p ≫ q) w)
        (precompNode (normalizedMap (chart P β a)) N))
        (parameter (CoefficientBassLaurentCompositionCarrier.reference P (p ≫ q) w)
          (CoefficientBassLaurentCompositionCarrier.nodes P (p ≫ q) w) x)) =
    parameter (polynomialReference P p q w ≫ normalizedMap (chart P β d))
      (fun i ↦ CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
        (precompNode (normalizedMap (chart P β a)) (tripleNodes P p q w (leftIndex i)))) x := by
  rw [mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun N ↦ parameter _ N x) (funext (left_lower_nodes P β p q w))

/-- The entire right radial binary parameter is retained before sheet inclusion. -/
theorem right_lower_parameter (x : StdSimplex ℝ (Fin 3)) :
    mapParameter (CommonReferenceProduct.reanchor
      (isoWhiskerRight (rightPolynomialIso P p q w) (normalizedMap (chart P β d)).functor))
      (mapParameter (fun N ↦ CommonReferenceProduct.reanchor
        (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p (q ≫ w))
        (precompNode (normalizedMap (chart P β a)) N))
        (parameter (CoefficientBassLaurentCompositionCarrier.reference P p (q ≫ w))
          (CoefficientBassLaurentCompositionCarrier.nodes P p (q ≫ w)) x)) =
    parameter (polynomialReference P p q w ≫ normalizedMap (chart P β d))
      (fun i ↦ CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
        (precompNode (normalizedMap (chart P β a)) (tripleNodes P p q w (rightIndex i)))) x := by
  rw [mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun N ↦ parameter _ N x) (funext (right_lower_nodes P β p q w))

/-- The actual corrected left radial cap has the original complete Laurent binary lower face. -/
theorem left_lower (r : I) :
    left P β p q w (r, 0) =
      CoefficientBassRaw1PolynomialCapLowerFaces.tripleLaurent P β p q w
        (parameter (polynomialReference P p q w ≫ normalizedMap (chart P β d))
          (fun i ↦ CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
            (precompNode (normalizedMap (chart P β a)) (tripleNodes P p q w (leftIndex i))))
          (binaryPath (k := 2) 0 1 2 r)) := by
  change leftMap P β p q w
    (CoefficientBassRaw1PolynomialPairCone.corrected P β (p ≫ q) w (r, 0)) = _
  rw [CoefficientBassRaw1PolynomialPairCone.corrected_left]
  change CoefficientBassPolynomialSheetNormalization.map _ _ _ _ _ _
    (SSet.toTop.map (CommonReferenceNerve.CutOpenCarrier.left₀ _ _ _ _)
      (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β (p ≫ q) w (r, 0))) = _
  rw [CoefficientBassPolynomialSheetNormalization.map_laurent,
    CoefficientBassRaw1PolynomialLowerAttachment.sheetFamily_lower]
  have hn : CoefficientBassPolynomialSheetNormalization.laurentIso
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P (p ≫ q) w)
      (polynomialReference P p q w) (normalizedMap (chart P β d))
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β (p ≫ q) w) (Iso.refl _)
      (leftPolynomialIso P p q w) =
      isoWhiskerRight (leftPolynomialIso P p q w) (normalizedMap (chart P β d)).functor :=
    Iso.trans_refl _
  rw [hn]
  exact congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.tripleLaurent P β p q w)
    (left_lower_parameter P β p q w (binaryPath (k := 2) 0 1 2 r))

/-- The actual corrected right radial cap has the original complete Laurent binary lower face. -/
theorem right_lower (r : I) :
    right P β p q w (r, 0) =
      CoefficientBassRaw1PolynomialCapLowerFaces.tripleLaurent P β p q w
        (parameter (polynomialReference P p q w ≫ normalizedMap (chart P β d))
          (fun i ↦ CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
            (precompNode (normalizedMap (chart P β a)) (tripleNodes P p q w (rightIndex i))))
          (binaryPath (k := 2) 0 1 2 r)) := by
  change rightMap P β p q w
    (CoefficientBassRaw1PolynomialPairCone.corrected P β p (q ≫ w) (r, 0)) = _
  rw [CoefficientBassRaw1PolynomialPairCone.corrected_left]
  change CoefficientBassPolynomialSheetNormalization.map _ _ _ _ _ _
    (SSet.toTop.map (CommonReferenceNerve.CutOpenCarrier.left₀ _ _ _ _)
      (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p (q ≫ w) (r, 0))) = _
  rw [CoefficientBassPolynomialSheetNormalization.map_laurent,
    CoefficientBassRaw1PolynomialLowerAttachment.sheetFamily_lower]
  have hn : CoefficientBassPolynomialSheetNormalization.laurentIso
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p (q ≫ w))
      (polynomialReference P p q w) (normalizedMap (chart P β d))
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p (q ≫ w)) (Iso.refl _)
      (rightPolynomialIso P p q w) =
      isoWhiskerRight (rightPolynomialIso P p q w) (normalizedMap (chart P β d)).functor :=
    Iso.trans_refl _
  rw [hn]
  exact congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.tripleLaurent P β p q w)
    (right_lower_parameter P β p q w (binaryPath (k := 2) 0 1 2 r))

/-- The full left radial sheet normalization preserves arbitrary native inputs in every degree. -/
theorem leftMap_native (n : ℕ)
    (z : CoefficientBassRaw1PolynomialPairCone.carrier P β (p ≫ q) w)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w β n (leftMap P β p q w z) x =
      CoefficientBassRaw1PolynomialPairCone.evaluate P β (p ≫ q) w n z x :=
  CoefficientBassPolynomialSheetNormalization.map_native
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P (p ≫ q) w)
    (polynomialReference P p q w) (normalizedMap (chart P β d))
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β (p ≫ q) w)
    (Iso.refl _) (leftPolynomialIso P p q w) n z x

/-- The full right radial sheet normalization preserves arbitrary native inputs in every degree. -/
theorem rightMap_native (n : ℕ)
    (z : CoefficientBassRaw1PolynomialPairCone.carrier P β p (q ≫ w))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w β n (rightMap P β p q w z) x =
      CoefficientBassRaw1PolynomialPairCone.evaluate P β p (q ≫ w) n z x :=
  CoefficientBassPolynomialSheetNormalization.map_native
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p (q ≫ w))
    (polynomialReference P p q w) (normalizedMap (chart P β d))
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p (q ≫ w))
    (Iso.refl _) (rightPolynomialIso P p q w) n z x

end Triple
end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialRadialCaps
