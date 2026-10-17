/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetChartNative

/-!
# A finite source family acting before a whole target reference nerve

The finite parameter construction puts the whole nerve first. The two finite characteristic
simplicial maps agree under product braiding before realization, retaining every full dependent
reference node. The actual realization-product comparison therefore exchanges the two independent
parameters, and the existing forward native-composition theorem gives the reverse-order formula
at every prespectrum level, including the original loop input at level zero.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory CartesianMonoidalCategory Convexity
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology
universe u
namespace Quillen.PerfectComplexes.CoefficientBassReverseFiniteProduct
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier

private theorem parameter_characteristic_realization {V W V' W' : Model.{u}}
    (E : V ⟶ W) (F : V' ⟶ W') {p q : ℕ}
    (f : Node E → Fin (q + 1) → Node F) (N : Fin (p + 1) → Node E)
    (z : StdSimplex ℝ (Fin (p + 1))) (w : StdSimplex ℝ (Fin (q + 1))) :
    FiniteParameter.parameter E F f (parameter E N z, w) =
      SSet.toTop.map (simplexMap E N ▷ Δ[q] ≫ FiniteParameter.simplicial E F f)
        ((realizationProductSimplexIso (Δ[p] : SSet.{u}) q).inv
          ((SimplexCategory.toTopHomeo ⦋p⦌).symm z,
            (SimplexCategory.toTopHomeo ⦋q⦌).symm w)) := by
  have h := ConcreteCategory.congr_hom
    (realizationProductSimplexIso_inv_whisker (simplexMap E N) q)
    ((SimplexCategory.toTopHomeo ⦋p⦌).symm z,
      (SimplexCategory.toTopHomeo ⦋q⦌).symm w)
  change SSet.toTop.map (simplexMap E N ▷ Δ[q])
      ((realizationProductSimplexIso (Δ[p] : SSet.{u}) q).inv
        ((SimplexCategory.toTopHomeo ⦋p⦌).symm z,
          (SimplexCategory.toTopHomeo ⦋q⦌).symm w)) =
    (realizationProductSimplexIso (parameterSSet E) q).inv
      (parameter E N z, (SimplexCategory.toTopHomeo ⦋q⦌).symm w) at h
  change SSet.toTop.map (FiniteParameter.simplicial E F f)
      ((realizationProductSimplexIso (parameterSSet E) q).inv
        (parameter E N z, (SimplexCategory.toTopHomeo ⦋q⦌).symm w)) = _
  rw [← h, Functor.map_comp]
  rfl

private theorem realization_product_swap (p q : ℕ)
    (z : |(Δ[p] : SSet.{u})|) (w : |(Δ[q] : SSet.{u})|) :
    SSet.toTop.map (β_ (Δ[p] : SSet.{u}) Δ[q]).hom
      ((realizationProductSimplexIso Δ[p] q).inv (z, w)) =
    (realizationProductSimplexIso Δ[q] p).inv (w, z) := by
  apply (TopCat.homeoOfIso (realizationProductSimplexIso Δ[q] p)).injective
  have h : SSet.toTop.map (β_ (Δ[p] : SSet.{u}) Δ[q]).hom ≫
      (realizationProductSimplexIso Δ[q] p).hom =
      (realizationProductSimplexIso Δ[p] q).hom ≫
        (β_ |(Δ[p] : SSet.{u})| |(Δ[q] : SSet.{u})|).hom := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]
  have he := ConcreteCategory.congr_hom h
    ((realizationProductSimplexIso Δ[p] q).inv (z, w))
  change (realizationProductSimplexIso Δ[q] p).hom _ =
    (realizationProductSimplexIso Δ[q] p).hom
      ((realizationProductSimplexIso Δ[q] p).inv (w, z))
  rw [Iso.inv_hom_id_apply]
  simpa only [TopCat.comp_app, Iso.inv_hom_id_apply, TopCat.braiding_hom_apply] using he

/-- Interchanging the product factors identifies the literal full-node simplicial maps. -/
theorem finite_product_simplicial_exchange {V W T : Model.{u}}
    (D : V ⟶ W) (H : W ⟶ T) (G : V ⟶ T)
    (δ : G.functor ≅ (D ≫ H).functor) {p q : ℕ}
    (Z : Fin (p + 1) → Node D) (N : Fin (q + 1) → Node H) :
    simplexMap H N ▷ Δ[p] ≫ FiniteParameter.simplicial H G
        (fun M i ↦ CommonReferenceProduct.node G D H δ (Z i) M) =
      (β_ (Δ[q] : SSet.{u}) Δ[p]).hom ≫ simplexMap D Z ▷ Δ[q] ≫
        FiniteParameter.simplicial D G
          (fun M i ↦ CommonReferenceProduct.node G D H δ M (N i)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  apply Subsingleton.elim

/-- The two independent finite characteristic parameters agree in the original target nerve. -/
theorem finite_product_parameter_exchange {V W T : Model.{u}}
    (D : V ⟶ W) (H : W ⟶ T) (G : V ⟶ T)
    (δ : G.functor ≅ (D ≫ H).functor) {p q : ℕ}
    (Z : Fin (p + 1) → Node D) (N : Fin (q + 1) → Node H)
    (z : StdSimplex ℝ (Fin (p + 1))) (w : StdSimplex ℝ (Fin (q + 1))) :
    FiniteParameter.parameter H G
        (fun M i ↦ CommonReferenceProduct.node G D H δ (Z i) M)
        (parameter H N w, z) =
      FiniteParameter.parameter D G
        (fun M i ↦ CommonReferenceProduct.node G D H δ M (N i))
        (parameter D Z z, w) := by
  rw [parameter_characteristic_realization, parameter_characteristic_realization,
    finite_product_simplicial_exchange]
  rw [Functor.map_comp]
  change SSet.toTop.map (simplexMap D Z ▷ Δ[q] ≫
      FiniteParameter.simplicial D G
        (fun M i ↦ CommonReferenceProduct.node G D H δ M (N i)))
      (SSet.toTop.map (β_ (Δ[q] : SSet.{u}) Δ[p]).hom
        ((realizationProductSimplexIso Δ[q] p).inv
          ((SimplexCategory.toTopHomeo ⦋q⦌).symm w,
            (SimplexCategory.toTopHomeo ⦋p⦌).symm z))) = _
  rw [realization_product_swap]

/-- The finite source family acts before the arbitrary whole target-nerve family, with both
parameters independent at every original prespectrum level, including degree zero. -/
theorem finite_product_native {V W T : Model.{u}}
    (D : V ⟶ W) (H : W ⟶ T) (G : V ⟶ T)
    (δ : G.functor ≅ (D ≫ H).functor) {p : ℕ} (Z : Fin (p + 1) → Node D)
    (n : ℕ) (y : |parameterSSet H|) (z : StdSimplex ℝ (Fin (p + 1)))
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily G n
      (FiniteParameter.parameter H G
        (fun M i ↦ CommonReferenceProduct.node G D H δ (Z i) M) (y, z)) x =
      pointwisePrespectrumFamily H n y (prespectrumFamily D Z n (z, x)) := by
  obtain ⟨q, N, w, rfl⟩ := exists_parameter H y
  rw [finite_product_parameter_exchange,
    CoefficientBassSeedTargetChartNative.finite_product_native,
    pointwisePrespectrumFamily_parameter, pointwisePrespectrumFamily_parameter]

end Quillen.PerfectComplexes.CoefficientBassReverseFiniteProduct
