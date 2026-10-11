/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Pseudofunctor
public import Quillen.CategoryTheory.FiberedCategory.CocartesianEvaluationCoherence

/-!
# Original bounded-flat coefficient evaluation coherence

The actual geometric pseudofunctor and actual cocartesian section transitions satisfy the two
coefficient routes, with original source transports and all functor associators retained.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckSections
universe u
namespace Quillen.Tests.BoundedFlatEvaluationCoherence

/-- The actual forward coefficient comparison obeys the proved original two-route equation. -/
theorem original_forward_composition {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (originalCoefficientIso boundedFlatAffinePseudofunctor (f ≫ g)).hom ≫
        whiskerLeft (originalEvaluation boundedFlatAffinePseudofunctor R)
          (boundedFlatAffinePseudofunctor.mapComp f.toLoc g.toLoc).hom.toNatTrans =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation boundedFlatAffinePseudofunctor T)
        (underCocartesianReindex_comp
          (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) f g)) ≫
        (originalCoefficientRouteIso boundedFlatAffinePseudofunctor f g).hom :=
  originalCoefficientIso_comp_hom boundedFlatAffinePseudofunctor f g

/-- The original identity comparison retains both strict restriction and geometric unit. -/
theorem original_identity (R : CommRingCat.{u}) :
    (originalCoefficientIso boundedFlatAffinePseudofunctor (𝟙 R)).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation boundedFlatAffinePseudofunctor R)
          (underCocartesianReindex_id
            (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) R)) ≫
        (Functor.leftUnitor (originalEvaluation boundedFlatAffinePseudofunctor R)).hom =
      whiskerLeft (originalEvaluation boundedFlatAffinePseudofunctor R)
          (boundedFlatAffinePseudofunctor.mapId ⟨R⟩).hom.toNatTrans ≫
        (Functor.rightUnitor (originalEvaluation boundedFlatAffinePseudofunctor R)).hom :=
  originalCoefficientIso_id boundedFlatAffinePseudofunctor R

/-- The middle coefficient arrow is the actual reindexed transition with its source transport. -/
theorem original_middle_arrow {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) R) :
    (boundedFlatAffinePseudofunctor.map g.toLoc).toFunctor.map
        ((eqToIso (originalEvaluation_reindex boundedFlatAffinePseudofunctor R f)).inv.app s) ≫
        originalTransition boundedFlatAffinePseudofunctor S
          ((underCocartesianReindex
            (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) f).obj s)
          (Under.mk g) =
      originalArrowTransition boundedFlatAffinePseudofunctor R s
        (Under.homMk g : Under.mk f ⟶ Under.mk (f ≫ g)) :=
  originalTransition_reindex_source boundedFlatAffinePseudofunctor f g s

/-- The comparison uses the unchanged original transition component at every coefficient arrow. -/
theorem original_inverse_component {R S : CommRingCat.{u}} (f : R ⟶ S)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) R) :
    (originalCoefficientIso boundedFlatAffinePseudofunctor f).inv.app s =
      originalTransition boundedFlatAffinePseudofunctor R s (Under.mk f) ≫
        (eqToIso (originalEvaluation_reindex boundedFlatAffinePseudofunctor R f)).inv.app s :=
  originalCoefficientIso_inv_app boundedFlatAffinePseudofunctor f s

end Quillen.Tests.BoundedFlatEvaluationCoherence
