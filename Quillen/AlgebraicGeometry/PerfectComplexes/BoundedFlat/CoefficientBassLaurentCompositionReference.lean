/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentCompositionCarrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveCompositionReferences
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! Canonical full-reference endpoints of the original Laurent composition paths. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassLaurentCompositionReference
open BassReferenceMerge BassMWholeNerve BassH0Merge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original coefficient reference for the Laurent extension of the composite `p ≫ q`. -/
abbrev reference := coefficientModel P ((laurentUnderFunctor R).map (p ≫ q))

/-- The full normalization isomorphism from the composite Laurent reference to the binary source. -/
def anchor : (reference P p q).functor ≅
    (CoefficientBassLaurentCompositionCarrier.reference P p q).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (laurentComposition_total P p q)))

/-- The three binary-normalization nodes reanchored in the original composite Laurent reference. -/
def nodes (i : Fin 3) : CommonReferenceNerve.Node (reference P p q) :=
  ⟨(CoefficientBassLaurentCompositionCarrier.nodes P p q i).1,
    anchor P p q ≪≫ (CoefficientBassLaurentCompositionCarrier.nodes P p q i).2⟩

theorem node_zero : nodes P p q 0 = ⟨reference P p q, Iso.refl _⟩ := by
  let e := congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (laurentComposition_total P p q))
  symm
  apply ModelSimplex.reference_node_eq e (Iso.refl _) (anchor P p q ≪≫ Iso.refl _)
  have he : anchor P p q = eqToIso e := smallIso_eqToIso _
  rw [he]
  simp only [Iso.refl_hom, Category.id_comp, Iso.trans_refl]
  exact (eqToIso.hom e).symm

theorem node_two : nodes P p q 2 =
    ⟨coefficientModel P ((laurentUnderFunctor R).map p) ≫
      coefficientModel P ((laurentUnderFunctor R).map q), laurentCompositionIso P p q⟩ := by
  have e : (BinaryNormalizationSimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map q))
      (coefficientMap P ((laurentUnderFunctor R).map p))).functor =
      (coefficientModel P ((laurentUnderFunctor R).map p) ≫
        coefficientModel P ((laurentUnderFunctor R).map q)).functor := rfl
  apply ModelSimplex.reference_node_eq e
  change (anchor P p q ≪≫ BinaryNormalizationSimplex.total
    (coefficientMap P ((laurentUnderFunctor R).map q))
    (coefficientMap P ((laurentUnderFunctor R).map p))).hom ≫ 𝟙 _ =
      (laurentCompositionIso P p q).hom
  rw [Category.comp_id]
  have h := smallIso_trans
    (eqToIso (congrArg boundedFlatNormalizedPullback (laurentComposition_total P p q)))
    (boundedFlatNormalizedPullbackCompIso
      (coefficientMap P ((laurentUnderFunctor R).map q))
      (coefficientMap P ((laurentUnderFunctor R).map p)))
  exact congrArg Iso.hom h.symm

/-- The unchanged binary clock is placed in its canonical complete coefficient reference. -/
def family : C(I, |nerve (Codiscrete (CommonReferenceNerve.Node (reference P p q)))|) :=
  (CommonReferenceNerve.mapParameter (CommonReferenceProduct.reanchor (anchor P p q))).comp
    (CoefficientBassLaurentCompositionCarrier.family P p q)

theorem family_parameter (t : I) : family P p q t =
    CommonReferenceNerve.parameter (reference P p q) (nodes P p q)
      (binaryPath (k := 2) 0 1 2 t) :=
  CommonReferenceNerve.mapParameter_parameter (CommonReferenceProduct.reanchor (anchor P p q))
    (CoefficientBassLaurentCompositionCarrier.nodes P p q) (binaryPath (k := 2) 0 1 2 t)

theorem family_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (reference P p q)
      (family P p q) n (t, x) =
    (boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n (t, x) := by
  have h0 := CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (reference P p q) (family P p q) n t x
  have h1 := CommonReferenceNerve.pointwise_reanchor (anchor P p q) n
    (CoefficientBassLaurentCompositionCarrier.family P p q t) x
  have h2 := CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (CoefficientBassLaurentCompositionCarrier.reference P p q)
    (CoefficientBassLaurentCompositionCarrier.family P p q) n t x
  exact h0.symm.trans (h1.trans (h2.trans
    (CoefficientBassLaurentCompositionCarrier.family_native P p q n t x)))

end Quillen.PerfectComplexes.CoefficientBassLaurentCompositionReference
