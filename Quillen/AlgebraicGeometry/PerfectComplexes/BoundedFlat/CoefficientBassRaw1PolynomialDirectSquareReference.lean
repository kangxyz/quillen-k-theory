/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairEndpointReferences

/-! The complete direct chart square under the original coefficient-composition equalities. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialDirectSquareReference
open CommonReferenceNerve BassH0Merge CoefficientBassRaw1PolynomialPairEndpointReferences

private theorem square_nodes_congr {X Y Z T : Scheme.{u}}
    (l l' : X ⟶ Y) (s : Y ⟶ Z) (t : X ⟶ T) (p p' : T ⟶ Z)
    (h : l ≫ s = t ≫ p) (h' : l' ≫ s = t ≫ p')
    (hl : l = l') (hp : p = p') (i : Fin 5) :
    CommonReferenceProduct.reanchor
      (eqToIso (congrArg (fun k ↦ (normalizedMap (k ≫ s)).functor) hl))
      (NativeSquareFiveSimplex.nodes l' s t p' h' i) =
      NativeSquareFiveSimplex.nodes l s t p h i := by
  subst l'
  subst p'
  rcases NativeSquareFiveSimplex.nodes l s t p h i with ⟨F, η⟩
  simp only [CommonReferenceProduct.reanchor, eqToIso_refl, Iso.refl_trans]

/-- The complete terminal normalization of an original commuting chart square. -/
def terminalAnchor {X Y Z T : Scheme.{u}}
    (l : X ⟶ Y) (s : Y ⟶ Z) (t : X ⟶ T) (p : T ⟶ Z)
    (h : l ≫ s = t ≫ p) :=
  (BinaryNormalizationSimplex.total t p).symm ≪≫
    (NativeSquareFiveSimplex.sourceIso l s t p h).symm

private theorem terminalAnchor_congr {X Y Z T : Scheme.{u}}
    (l l' : X ⟶ Y) (s : Y ⟶ Z) (t : X ⟶ T) (p p' : T ⟶ Z)
    (h : l ≫ s = t ≫ p) (h' : l' ≫ s = t ≫ p')
    (hl : l = l') (hp : p = p') :
    isoWhiskerRight (eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) hp))
        (normalizedMap t).functor ≪≫ terminalAnchor l' s t p' h' =
      terminalAnchor l s t p h ≪≫
        eqToIso (congrArg (fun k ↦ (normalizedMap (k ≫ s)).functor) hl) := by
  subst l'
  subst p'
  simp only [eqToIso_refl, isoWhiskerRight_refl, Iso.refl_trans, Iso.trans_refl]

private theorem eqToIso_reverse {C : Type*} [Category C] {X Y : C} (h : X = Y) :
    (eqToIso h).symm = eqToIso h.symm := by
  subst Y
  rfl

private theorem reanchor_comp {V W : Model.{u}} {F G H : V ⟶ W}
    (η : F.functor ≅ G.functor) (θ : G.functor ≅ H.functor) (N : Node H) :
    CommonReferenceProduct.reanchor (η ≪≫ θ) N =
      CommonReferenceProduct.reanchor η (CommonReferenceProduct.reanchor θ N) := by
  rcases N with ⟨K, ρ⟩
  simp only [CommonReferenceProduct.reanchor, Iso.trans_assoc]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The actual Laurent composite equality retains the original two arrows. -/
theorem laurent_eq : lq P q ≫ lp P p =
    coefficientMap P ((laurentUnderFunctor R).map (p ≫ q)) := by
  simp only [Functor.map_comp, coefficientMap_comp]

/-- The actual polynomial composite equality retains the original two arrows. -/
theorem polynomial_eq : pq P q ≫ pp P p =
    coefficientMap P ((polynomialUnderFunctor R).map (p ≫ q)) := by
  simp only [Functor.map_comp, coefficientMap_comp]

/-- The direct square is exactly the original chart square of the composite arrow. -/
abbrev directSource := NativeSquareFiveSimplex.source
  (coefficientMap P ((laurentUnderFunctor R).map (p ≫ q))) (ca P β (a := a))

/-- The source transport records only the proven full Laurent composite equality. -/
def sourceIso :
    (NativeSquareFiveSimplex.source (lq P q ≫ lp P p) (ca P β (a := a))).functor ≅
      (directSource P β p q).functor :=
  eqToIso (congrArg (fun k ↦ (normalizedMap (k ≫ ca P β (a := a))).functor)
    (laurent_eq P p q))

/-- Every complete node of the original composite square is retained. -/
def directNodes := NativeSquareFiveSimplex.nodes
  (coefficientMap P ((laurentUnderFunctor R).map (p ≫ q))) (ca P β (a := a))
  (cc P β (c := c)) (coefficientMap P ((polynomialUnderFunctor R).map (p ≫ q)))
  (coefficientMap_naturality P β (p ≫ q))

/-- The full direct row agrees after its literal source equality transport. -/
theorem direct_nodes (i : Fin 5) :
    CommonReferenceProduct.reanchor (sourceIso P β p q) (directNodes P β p q i) =
      NativeSquareFiveSimplex.nodes (lq P q ≫ lp P p) (ca P β (a := a))
        (cc P β (c := c)) (pq P q ≫ pp P p)
        (DoubleSquareTrack.total_eq (pp P p) (pq P q) (lp P p) (lq P q)
          (ca P β (a := a)) (cb P β (b := b)) (cc P β (c := c))
          (coefficientMap_naturality P β p).symm
          (coefficientMap_naturality P β q).symm) i :=
  square_nodes_congr _ _ _ _ _ _ _ _ (laurent_eq P p q) (polynomial_eq P p q) i


/-- The actual direct action is normalized by its complete terminal-square anchor. -/
def directAnchor :
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q).functor ≅
      (directSource P β p q).functor :=
  isoWhiskerRight
    (eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) (polynomial_eq P p q)))
    (normalizedMap (cc P β (c := c))).functor ≪≫
      terminalAnchor (coefficientMap P ((laurentUnderFunctor R).map (p ≫ q)))
        (ca P β (a := a)) (cc P β (c := c))
        (coefficientMap P ((polynomialUnderFunctor R).map (p ≫ q)))
        (coefficientMap_naturality P β (p ≫ q))

/-- The outer row's complete anchor is the same terminal normalization word. -/
theorem outer_anchor_word :
    terminalAnchor (lq P q ≫ lp P p) (ca P β (a := a))
      (cc P β (c := c)) (pq P q ≫ pp P p)
      (DoubleSquareTrack.total_eq (pp P p) (pq P q) (lp P p) (lq P q)
    (ca P β (a := a)) (cb P β (b := b)) (cc P β (c := c))
    (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm) =
    CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q ≪≫
      CoefficientMovingSquareRows.outerAnchor (pp P p) (pq P q) (lp P p) (lq P q)
    (ca P β (a := a)) (cb P β (b := b)) (cc P β (c := c))
    (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm := by
  dsimp only [terminalAnchor, NativeSquareFiveSimplex.sourceIso]
  rw [eqToIso_reverse]
  rfl

/-- The full direct-action anchor matches the fixed original outer row before evaluation. -/
theorem direct_anchor : directAnchor P β p q =
    (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q ≪≫
      CoefficientMovingSquareRows.outerAnchor (pp P p) (pq P q) (lp P p) (lq P q)
    (ca P β (a := a)) (cb P β (b := b)) (cc P β (c := c))
    (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm) ≪≫
      sourceIso P β p q := by
  have h := terminalAnchor_congr (lq P q ≫ lp P p)
    (coefficientMap P ((laurentUnderFunctor R).map (p ≫ q)))
    (ca P β (a := a)) (cc P β (c := c)) (pq P q ≫ pp P p)
    (coefficientMap P ((polynomialUnderFunctor R).map (p ≫ q)))
    (DoubleSquareTrack.total_eq (pp P p) (pq P q) (lp P p) (lq P q)
    (ca P β (a := a)) (cb P β (b := b)) (cc P β (c := c))
    (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm)
    (coefficientMap_naturality P β (p ≫ q)) (laurent_eq P p q) (polynomial_eq P p q)
  rw [outer_anchor_word P β p q] at h
  exact h


/-- The normalized direct chart action retains the entire original outer five-node row. -/
theorem normalized_direct_nodes (i : Fin 5) :
    CommonReferenceProduct.reanchor (directAnchor P β p q) (directNodes P β p q i) =
      CoefficientBassRaw1PolynomialPairEndpointReferences.outerNodes P β p q i := by
  rw [direct_anchor]
  simp only [reanchor_comp]
  rw [direct_nodes]
  rfl

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialDirectSquareReference
