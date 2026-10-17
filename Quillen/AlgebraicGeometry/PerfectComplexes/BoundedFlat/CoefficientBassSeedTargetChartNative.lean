/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetChartAttachment
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNervePointwiseFamily
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceProductNodes
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationSimplexComposition

/-! Whole-reference recovery of the prescribed target coefficient chart homotopy. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTargetChartNative
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open CoefficientBassSeedTargetChartAttachment

private theorem pair_iso_other {V W T : Model.{u}} {D N : V ⟶ W} {H Z : W ⟶ T}
    (e : D.functor ≅ N.functor) (f : H.functor ≅ Z.functor) :
    (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso (e.prod f) =
      isoWhiskerLeft D.functor f ≪≫ isoWhiskerRight e Z.functor := by
  apply Iso.ext
  ext X
  exact f.hom.naturality (e.hom.app X)

/-- Whole-parameter evaluation of the full reference product with a finite simplex family. -/
theorem finite_product_native {V W T : Model.{u}}
    (D : V ⟶ W) (H : W ⟶ T) (G : V ⟶ T)
    (δ : G.functor ≅ (D ≫ H).functor) {q : ℕ} (Z : Fin (q + 1) → Node H)
    (n : ℕ) (y : |parameterSSet D|) (w : StdSimplex ℝ (Fin (q + 1)))
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily G n
      (FiniteParameter.parameter D G (fun N i ↦ CommonReferenceProduct.node G D H δ N (Z i))
        (y, w)) x =
    prespectrumFamily H Z n (w, pointwisePrespectrumFamily D n y x) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter D y
  rw [FiniteParameter.parameter_characteristic, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter, prespectrumFamily_eq, prespectrumFamily_eq,
    prespectrumFamily_eq]
  have hs : ModelSimplex.ofIsos G
      (fun i ↦ (FiniteParameter.gridNodes D G
        (fun M j ↦ CommonReferenceProduct.node G D H δ M (Z j)) N i).1)
      (fun i ↦ (FiniteParameter.gridNodes D G
        (fun M j ↦ CommonReferenceProduct.node G D H δ M (Z j)) N i).2) =
      CommonReferenceProduct.simplex D (fun i ↦ (N i).1) (fun i ↦ (N i).2)
        H (fun i ↦ (Z i).1) (fun i ↦ (Z i).2) :=
    ModelSimplex.ofIsos_change_reference δ _ _
  rw [hs]
  exact CommonReferenceProduct.prespectrum_comp D (fun i ↦ (N i).1) (fun i ↦ (N i).2)
    H (fun i ↦ (Z i).1) (fun i ↦ (Z i).2) n x z w

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (polynomialUnderFunctor R).obj a))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (ε : G.functor ≅ (D ≫ Ja P (a := a)).functor)

private theorem moving_product (N : Node D) (i : Fin 5) :
    movingNode P f D G ε N i =
      CommonReferenceProduct.node (G ≫ L P f) D (H P f) (squareAnchor P f D G ε) N
        (NativeSquareFiveSimplex.nodes
          (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentPlus P a)
          (laurentPlus P b) (coefficientMap P ((polynomialUnderFunctor R).map f))
          (coefficientMap_naturality P (underToLaurent R) f) i) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [movingNode, CommonReferenceProduct.node, pair_iso_other]

/-- The entire moving chart is the original chart-square homotopy, for all levels and inputs. -/
theorem moving_native (n : ℕ) (y : |parameterSSet D|) (t : I)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (G ≫ L P f) n (moving P f D G ε (y, t)) x =
      (boundedFlatCoefficientPlusSquareHomotopy P f).level n
        (t, pointwisePrespectrumFamily D n y x) := by
  have hf := funext (fun N ↦ funext (moving_product P f D G ε N))
  change pointwisePrespectrumFamily (G ≫ L P f) n
    (FiniteParameter.parameter D (G ≫ L P f) (movingNode P f D G ε)
      (y, NativeSquareFiveSimplex.parameter t)) x = _
  rw [hf]
  refine (finite_product_native D (H P f) (G ≫ L P f) (squareAnchor P f D G ε)
    _ n y (NativeSquareFiveSimplex.parameter t) x).trans ?_
  rw [prespectrumFamily_eq]
  exact NativeSquareFiveSimplex.native
        (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentPlus P a)
        (laurentPlus P b) (coefficientMap P ((polynomialUnderFunctor R).map f))
        (coefficientMap_naturality P (underToLaurent R) f) n t
        (pointwisePrespectrumFamily D n y x)

end Quillen.PerfectComplexes.CoefficientBassSeedTargetChartNative
