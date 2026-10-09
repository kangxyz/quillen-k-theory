import Quillen.CategoryTheory.QConstruction.ZeroEndomorphisms
import Quillen.Topology.ClassifyingSpace.PointedFunctor

/-! # Q-valued functors whose objects are zero

A functor landing in original zero objects is naturally isomorphic to the
constant zero-vertex functor. This prepares the actual nullhomotopy needed
for the Serre-localization homotopy-fiber comparison.
-/

noncomputable section
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : Quillen.ExactStructure C) {D : Type u'} [Category.{v'} D]

/-- The zero-image condition determines a genuine natural isomorphism to the
constant Q-zero functor, because all the relevant Q-hom sets are subsingletons. -/
def qFunctorIsoConstZero (F : D ⥤ E.QCategory)
    (hF : ∀ X, IsZero (F.obj X).obj.of) : F ≅ (Functor.const D).obj E.qZero :=
  NatIso.ofComponents (fun X => E.qIsoOfIso ((hF X).iso (isZero_zero C)))
    (fun {X Y} f => by
      exact (E.qHom_subsingleton_of_isZero (F.obj X) E.qZero
        (isZero_zero C)).elim _ _)

end Quillen.ExactStructure
