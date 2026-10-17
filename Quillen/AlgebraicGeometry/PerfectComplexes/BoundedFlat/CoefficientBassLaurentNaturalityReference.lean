/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentCompositionReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentNaturalityCarrier

/-! Full equality transport at the prescribed Laurent naturality square. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassLaurentNaturalityReference
open BassReferenceMerge BassMWholeNerve
private theorem eqToIso_chain {C : Type*} [Category C] {A B C' D : C}
    (h₁ : A = B) (h₂ : B = D) (h₃ : A = C') (h₄ : C' = D) :
    eqToIso h₁ ≪≫ eqToIso h₂ = eqToIso h₃ ≪≫ eqToIso h₄ := by
  rw [eqToIso_trans, eqToIso_trans]

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)
  {M N : Under R ⥤ Under R} (α : M ⟶ N)

/-- The coefficient reference for composition along `α.app a` followed by `N.map u`. -/
abbrev reference := CoefficientBassLaurentCompositionReference.reference P (α.app a) (N.map u)

/-- The reference isomorphism induced by the reversed naturality equality for `α` and `u`. -/
def referenceIso : (reference P u α).functor ≅
    (CoefficientBassLaurentCompositionReference.reference P (M.map u) (α.app b)).functor :=
  eqToIso (congrArg (fun k ↦ (coefficientModel P ((laurentUnderFunctor R).map k)).functor)
    (α.naturality u).symm)

/-- All equality casts form the same complete reference route, before native evaluation. -/
theorem anchor_square :
    CoefficientBassLaurentCompositionReference.anchor P (α.app a) (N.map u) ≪≫
      NativeSquareFiveSimplex.sourceIso
        (CoefficientBassLaurentNaturalityCarrier.first P u (N := N))
        (CoefficientBassLaurentNaturalityCarrier.second P α)
        (CoefficientBassLaurentNaturalityCarrier.third P α)
        (CoefficientBassLaurentNaturalityCarrier.fourth P u (M := M))
        (CoefficientBassLaurentNaturalityCarrier.square P u α) =
    referenceIso P u α ≪≫
      CoefficientBassLaurentCompositionReference.anchor P (M.map u) (α.app b) := by
  unfold CoefficientBassLaurentCompositionReference.anchor
  rw [smallIso_eqToIso, smallIso_eqToIso]
  exact eqToIso_chain _ _ _ _

private theorem append_iso {C : Type*} [Category C] {A B B' D E : C}
    {f : A ≅ B} {g : B ≅ D} {f' : A ≅ B'} {g' : B' ≅ D}
    (h : f ≪≫ g = f' ≪≫ g') (t : D ≅ E) :
    f ≪≫ (g ≪≫ t) = f' ≪≫ (g' ≪≫ t) := by
  rw [← Iso.trans_assoc, h, Iso.trans_assoc]

/-- The five Laurent naturality nodes reanchored in the coefficient composition reference. -/
def nodes (i : Fin 5) : CommonReferenceNerve.Node (reference P u α) :=
  CommonReferenceProduct.reanchor
    (CoefficientBassLaurentCompositionReference.anchor P (α.app a) (N.map u))
    (CoefficientBassLaurentNaturalityCarrier.nodes P u α i)

theorem node_two : nodes P u α 2 =
    ⟨coefficientModel P ((laurentUnderFunctor R).map (α.app a)) ≫
      coefficientModel P ((laurentUnderFunctor R).map (N.map u)),
      laurentCompositionIso P (α.app a) (N.map u)⟩ := by
  calc
    _ = CoefficientBassLaurentCompositionReference.nodes P (α.app a) (N.map u) 2 := rfl
    _ = _ := CoefficientBassLaurentCompositionReference.node_two P (α.app a) (N.map u)

theorem node_four : nodes P u α 4 =
    CommonReferenceProduct.reanchor (referenceIso P u α)
      (⟨coefficientModel P ((laurentUnderFunctor R).map (M.map u)) ≫
        coefficientModel P ((laurentUnderFunctor R).map (α.app b)),
        laurentCompositionIso P (M.map u) (α.app b)⟩) := by
  have hi := append_iso (anchor_square P u α)
    (BinaryNormalizationSimplex.total
      (CoefficientBassLaurentNaturalityCarrier.third P α)
      (CoefficientBassLaurentNaturalityCarrier.fourth P u (M := M)))
  have hn : nodes P u α 4 =
      CommonReferenceProduct.reanchor (referenceIso P u α)
        (CoefficientBassLaurentCompositionReference.nodes P (M.map u) (α.app b) 2) :=
    congrArg (fun ρ : (reference P u α).functor ≅
      (BinaryNormalizationSimplex.targetMap
        (CoefficientBassLaurentNaturalityCarrier.third P α)
        (CoefficientBassLaurentNaturalityCarrier.fourth P u (M := M))).functor ↦
      (⟨_, ρ⟩ : CommonReferenceNerve.Node (reference P u α))) hi
  exact hn.trans (congrArg (CommonReferenceProduct.reanchor (referenceIso P u α))
    (CoefficientBassLaurentCompositionReference.node_two P (M.map u) (α.app b)))

/-- The Laurent naturality interval family reanchored in the coefficient composition reference. -/
def family : C(I, |nerve (Codiscrete (CommonReferenceNerve.Node (reference P u α)))|) :=
  (CommonReferenceNerve.mapParameter (CommonReferenceProduct.reanchor
    (CoefficientBassLaurentCompositionReference.anchor P (α.app a) (N.map u)))).comp
      (CoefficientBassLaurentNaturalityCarrier.family P u α)

theorem family_parameter (t : I) : family P u α t =
    CommonReferenceNerve.parameter (reference P u α) (nodes P u α)
      (NativeSquareFiveSimplex.parameter t) :=
  CommonReferenceNerve.mapParameter_parameter (CommonReferenceProduct.reanchor
    (CoefficientBassLaurentCompositionReference.anchor P (α.app a) (N.map u)))
      (CoefficientBassLaurentNaturalityCarrier.nodes P u α) (NativeSquareFiveSimplex.parameter t)

theorem family_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj (M.obj a))))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (reference P u α)
      (family P u α) n (t, x) =
    (CoefficientBassLaurentProjectionRoutes.naturalitySquare P u α).level n (t, x) := by
  have h0 := CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (reference P u α) (family P u α) n t x
  have h1 := CommonReferenceNerve.pointwise_reanchor
    (CoefficientBassLaurentCompositionReference.anchor P (α.app a) (N.map u)) n
      (CoefficientBassLaurentNaturalityCarrier.family P u α t) x
  have h2 := CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (CoefficientBassLaurentNaturalityCarrier.reference P u α)
    (CoefficientBassLaurentNaturalityCarrier.family P u α) n t x
  exact h0.symm.trans (h1.trans (h2.trans
    (CoefficientBassLaurentNaturalityCarrier.family_native P u α n t x)))

end Quillen.PerfectComplexes.CoefficientBassLaurentNaturalityReference
