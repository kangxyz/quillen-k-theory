import Quillen.CategoryTheory.ExactCategory.Functor
import Quillen.Topology.ClassifyingSpace.PointedFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Exact functors induce maps between zero-based Quillen K-groups

An exact functor preserves the chosen zero object up to the canonical
zero-object isomorphism. We use its induced Q-isomorphism to rebase the
Q-functor, giving a genuinely pointed continuous map and hence a homomorphism
between the actual homotopy groups defining Quillen K-theory.

The rebased functor is naturally isomorphic to the original Q-functor.
The identity law is proved below. The composition law, using the actual
based realization homotopy, is proved in `Quillen.KMapFunctoriality`.
-/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.ExactFunctor

variable {C : Type u} {D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive D] [HasFiniteBiproducts D]
  {EC : Quillen.ExactStructure C} {ED : Quillen.ExactStructure D}

/-- The homomorphism of genuine Quillen K-groups associated to an exact
functor, with both basepoints the chosen zero objects. -/
def KMap (F : ExactFunctor EC ED) (n : ℕ) : EC.K n →* ED.K n :=
  F.toQCompatibleFunctor.kMapWithZeroIso F.toFunctor.mapZeroObject n

set_option backward.isDefEq.respectTransparency false in
/-- The identity exact functor induces the identity on every K-group. -/
@[simp]
theorem KMap_id (E : Quillen.ExactStructure C) (n : ℕ) :
    (ExactFunctor.id E).KMap n = MonoidHom.id (E.K n) := by
  have hz : (ExactFunctor.id E).toFunctor.mapZeroObject = Iso.refl (0 : C) := by
    apply Iso.ext
    apply Subsingleton.elim
  change pointedShiftedHomotopyGroupMap (ExactFunctor.id E).mapQ
    (Q.of E.deflation E.inflation (0 : C))
    (Q.of E.deflation E.inflation (0 : C))
    (E.qIsoOfIso (ExactFunctor.id E).toFunctor.mapZeroObject) n = _
  rw [hz]
  change pointedShiftedHomotopyGroupMap (ExactFunctor.id E).mapQ
    (Q.of E.deflation E.inflation (0 : C))
    (Q.of E.deflation E.inflation (0 : C))
    (Iso.refl (Q.of E.deflation E.inflation (0 : C))) n = _
  have hF : rebaseFunctor (ExactFunctor.id E).mapQ
      (Q.of E.deflation E.inflation (0 : C))
      (Q.of E.deflation E.inflation (0 : C)) (Iso.refl _) =
      𝟭 (Q E.deflation E.inflation) :=
    (rebaseFunctor_refl (ExactFunctor.id E).mapQ _).trans (ExactFunctor.mapQ_id E)
  have hT : classifyingSpaceMap (rebaseFunctor (ExactFunctor.id E).mapQ
      (Q.of E.deflation E.inflation (0 : C))
      (Q.of E.deflation E.inflation (0 : C)) (Iso.refl _)) =
      𝟙 (ClassifyingSpace (Q E.deflation E.inflation)) := by
    rw [hF, classifyingSpaceMap_id]
  apply MonoidHom.ext
  intro a
  change homotopyGroupMap (classifyingSpaceMap (rebaseFunctor (ExactFunctor.id E).mapQ
      (Q.of E.deflation E.inflation (0 : C))
      (Q.of E.deflation E.inflation (0 : C)) (Iso.refl _))).hom _ a = a
  simpa only [hT, TopCat.hom_id] using homotopyGroupMap_id a


end Quillen.ExactFunctor
