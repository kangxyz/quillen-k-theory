/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBottomCommonFamily
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitTrack
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0UnitStrip
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceProductNodes

/-! The actual source-unit action on the Laurent composition product, with full references. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1SourceUnitProduct
open CommonReferenceNerve CommonReferenceProduct LaurentUnitReferenceSpecialization
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The literal Laurent binary total is the actual composite coefficient map. -/
theorem laurent_total :
    BassLaurentBottomFace.firstMap P q ≫ BassLaurentBottomFace.secondMap P p =
      coefficientMap P ((laurentUnderFunctor R).map (p ≫ q)) := by
  simp only [BassLaurentBottomFace.firstMap, BassLaurentBottomFace.secondMap,
    Functor.map_comp, coefficientMap_comp]

/-- Pullback along that actual total preserves the specified forward Laurent scalar. -/
theorem laurent_total_unit :
    Units.map (BassLaurentBottomFace.firstMap P q ≫
      BassLaurentBottomFace.secondMap P p).appTop.hom.toMonoidHom (laurentUnit P a) =
        laurentUnit P c := by
  rw [laurent_total]
  exact boundedFlatCoefficientLaurentUnit_coefficient P (p ≫ q)

/-- The original normalized small-model functor preserves the source and target unit actions. -/
theorem laurent_source_preserves :
    Preserves (BassLaurentBottomFace.source P p q).functor (smallUnit P a) (smallUnit P c) := by
  have h := GlobalUnitReferenceNaturality.normalizedModel_preserves
    (i := (op P, (laurentUnderFunctor R).obj a))
    (k := (op P, (laurentUnderFunctor R).obj c))
    (BassLaurentBottomFace.firstMap P q ≫ BassLaurentBottomFace.secondMap P p)
    (laurentUnit P a)
  rw [laurent_total_unit] at h
  exact h

/-- The actual bottom anchor intertwines the total unit and the beta-conjugated source unit. -/
theorem source_unit_reference :
    commonUnit P p q ≪≫ BassBottomCommonFamily.referenceIso P p q =
      BassBottomCommonFamily.referenceIso P p q ≪≫
        isoWhiskerRight (splitProjectionUnit P a) (BassLaurentBottomFace.source P p q).functor := by
  rw [commonUnit_eq_action, splitProjectionUnit_eq_action]
  apply Iso.ext
  change (onFunctor (BassOverlap.commonReference P p q).functor (smallUnit P c)).hom ≫
      (BassBottomCommonFamily.referenceIso P p q).hom =
    (BassBottomCommonFamily.referenceIso P p q).hom ≫
      Functor.whiskerRight (onFunctor (BassProjectionPath.source P a).functor
        (smallUnit P a)).hom (BassLaurentBottomFace.source P p q).functor
  exact onFunctor_intertwine (BassOverlap.commonReference P p q).functor
    (BassProjectionPath.source P a).functor (BassLaurentBottomFace.source P p q).functor
    (BassBottomCommonFamily.referenceIso P p q).hom (smallUnit P a) (smallUnit P c)
    (laurent_source_preserves P p q)

/-- All three original Laurent binary maps retain their complete normalization references. -/
def laurentNodes (j : Fin 3) : Node (BassLaurentBottomFace.source P p q) :=
  ⟨BassLaurentBottomFace.vertices P p q j, BassLaurentBottomFace.references P p q j⟩

/-- The full ordinary start row of the source-positive product. -/
def positiveStartNodes (j : Fin 3) : Node (BassOverlap.commonReference P p q) :=
  node (BassOverlap.commonReference P p q) (BassProjectionPath.source P a)
    (BassLaurentBottomFace.source P p q) (BassBottomCommonFamily.referenceIso P p q)
    ⟨BassProjectionPath.source P a, Iso.refl _⟩ (laurentNodes P p q j)

/-- Six actual source-unit/Laurent-composition nodes, in source-first grid order. -/
def unitSixNodes (i : Fin 6) : Node (BassOverlap.commonReference P p q) :=
  node (BassOverlap.commonReference P p q) (BassProjectionPath.source P a)
    (BassLaurentBottomFace.source P p q) (BassBottomCommonFamily.referenceIso P p q)
    (CoefficientBassPositiveC0UnitStrip.unitNodes P a ((SimplexGrid.indexEquiv 1 2).symm i).1)
    (laurentNodes P p q ((SimplexGrid.indexEquiv 1 2).symm i).2)

private theorem product_unit_node {V W T : Model.{v}} (F : V ⟶ T) (H : V ⟶ W) (G : W ⟶ T)
    (eta : F.functor ≅ (H ≫ G).functor) (tau : F.functor ≅ F.functor)
    (theta : H.functor ≅ H.functor)
    (h : tau ≪≫ eta = eta ≪≫ isoWhiskerRight theta G.functor) (M : Node G) :
    node F H G eta ⟨H, theta⟩ M = reanchor tau (node F H G eta ⟨H, Iso.refl _⟩ M) := by
  have hN : (⟨H, theta⟩ : Node H) = reanchor theta ⟨H, Iso.refl _⟩ := by
    simp only [reanchor, Iso.trans_refl]
  rw [hN, node_first_reanchor, ← h]
  change (⟨H ≫ M.1, (tau ≪≫ eta) ≪≫ _⟩ : Node F) =
    ⟨H ≫ M.1, tau ≪≫ (eta ≪≫ _)⟩
  exact congrArg (fun rho : F.functor ≅ (H ≫ M.1).functor ↦
    (⟨H ≫ M.1, rho⟩ : Node F)) (Iso.trans_assoc tau eta _)

/-- Every lower source-unit node is the exact ordinary positive start node. -/
theorem unitSix_lower_nodes (j : Fin 3) :
    unitSixNodes P p q (SimplexGrid.index 1 2 (0, j)) = positiveStartNodes P p q j := by
  unfold unitSixNodes
  rw [SimplexGrid.decode_index]
  rfl

/-- All three upper nodes are the actual common-unit-shifted full dependent nodes. -/
theorem unitSix_upper_nodes (j : Fin 3) :
    unitSixNodes P p q (SimplexGrid.index 1 2 (1, j)) =
      reanchor (commonUnit P p q) (positiveStartNodes P p q j) := by
  unfold unitSixNodes
  rw [SimplexGrid.decode_index]
  exact product_unit_node (BassOverlap.commonReference P p q) (BassProjectionPath.source P a)
    (BassLaurentBottomFace.source P p q) (BassBottomCommonFamily.referenceIso P p q)
    (commonUnit P p q) (splitProjectionUnit P a) (source_unit_reference P p q)
    (laurentNodes P p q j)

end Quillen.PerfectComplexes.CoefficientBassPositiveC1SourceUnitProduct
