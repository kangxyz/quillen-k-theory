import Quillen.Topology.Realization.EdgewiseSimplex
import Quillen.Topology.Realization.EdgewiseCellular
import Quillen.Topology.ClassifyingSpace.Equivalence
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preorder

/-!
# The canonical realization equivalence for edgewise subdivision

The second-half endpoint map from the genuine edgewise subdivision of every
simplicial set realizes to a homotopy equivalence. The proof contracts the
subdivision of each standard simplex, then glues along the actual simplicial
skeletal cell complex. No realization comparison is assumed as an input.
-/

noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.Edgewise

instance subdivisionFunctor_preservesColimits : PreservesColimits subdivisionFunctor.{u} := by
  unfold subdivisionFunctor
  infer_instance

instance subdivisionFunctor_preservesSequentialColimits :
    PreservesColimitsOfShape ℕ subdivisionFunctor.{u} := by
  unfold subdivisionFunctor
  infer_instance

instance subdivisionFunctor_preservesMonomorphisms :
    subdivisionFunctor.{u}.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    have : ∀ n, Mono ((subdivisionFunctor.map f).app n) := fun n ↦ by
      change Mono (f.app (ε.op.obj n))
      infer_instance
    exact NatTrans.mono_of_mono_app _

private theorem homotopic_into_contractible {A B : Type u}
    [TopologicalSpace A] [TopologicalSpace B] [ContractibleSpace B]
    (f g : C(A, B)) : f.Homotopic g := by
  obtain ⟨b, h⟩ := id_nullhomotopic B
  have hf : f.Homotopic (ContinuousMap.const A b) :=
    h.comp (ContinuousMap.Homotopic.refl f)
  have hg : g.Homotopic (ContinuousMap.const A b) :=
    h.comp (ContinuousMap.Homotopic.refl g)
  exact hf.trans hg.symm

/-- The genuine endpoint map is a realization equivalence on every representable. -/
theorem realizesEquiv_endpoint_simplex (n : ℕ) :
    RealizesEquiv endpointNatTrans (Δ[n] : SSet.{u}) := by
  let : ContractibleSpace |subdivisionFunctor.obj (Δ[n] : SSet.{u})| :=
    contractibleSpace_simplex.{u} n
  let : ContractibleSpace |nerve (ULift.{u} (Fin (n + 1)))| := by
    change ContractibleSpace (ClassifyingSpace (ULift.{u} (Fin (n + 1))))
    infer_instance
  let : ContractibleSpace |(Δ[n] : SSet.{u})| :=
    (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.isoNerve n))).contractibleSpace
  refine ⟨{
    toFun := (SSet.toTop.map (endpoint (Δ[n] : SSet.{u}))).hom
    invFun := ContinuousMap.const _ (realizationPoint (simplexVertex n))
    left_inv := homotopic_into_contractible _ _
    right_inv := homotopic_into_contractible _ _ }, rfl⟩

/-- The canonical second-half endpoint realizes to a homotopy equivalence for
an arbitrary simplicial set, including infinite-dimensional ones. -/
theorem realizesEquiv_endpoint (X : SSet.{u}) : RealizesEquiv endpointNatTrans X :=
  realizesEquiv_all endpointNatTrans realizesEquiv_endpoint_simplex X

/-- Edgewise subdivision preserves the actual realization homotopy type.
Its forward map is exactly the realized second-half endpoint comparison. -/
def realizationHomotopyEquiv (X : SSet.{u}) :
    ContinuousMap.HomotopyEquiv |subdivision X| |X| := by
  let e : ContinuousMap.HomotopyEquiv |subdivision X| |X| :=
    (realizesEquiv_endpoint X).choose
  have he : e.toFun = (SSet.toTop.map (endpoint X)).hom :=
    (realizesEquiv_endpoint X).choose_spec
  exact {
    toFun := (SSet.toTop.map (endpoint X)).hom
    invFun := e.invFun
    left_inv := by rw [← he]; exact e.left_inv
    right_inv := by rw [← he]; exact e.right_inv }

@[simp] theorem realizationHomotopyEquiv_toFun (X : SSet.{u}) :
    (realizationHomotopyEquiv X).toFun = (SSet.toTop.map (endpoint X)).hom := rfl

/-- The forward realization equivalences commute with every simplicial map. -/
theorem realizationHomotopyEquiv_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    (realizationHomotopyEquiv Y).toFun.comp
      (SSet.toTop.map (subdivisionFunctor.map f)).hom =
    (SSet.toTop.map f).hom.comp (realizationHomotopyEquiv X).toFun := by
  exact congrArg TopCat.Hom.hom (realization_naturality endpointNatTrans f)

/-- The forward equivalence sends every subdivided vertex to its endpoint vertex. -/
@[simp] theorem realizationHomotopyEquiv_point (X : SSet.{u})
    (x : (subdivision X) _⦋0⦌) :
    realizationHomotopyEquiv X (realizationPoint x) =
      realizationPoint ((endpoint X).app _ x) :=
  realizationPoint_naturality (endpoint X) x

/-- A vertex of a simplicial set determines the degenerate interval vertex
of its edgewise subdivision. -/
def vertex {X : SSet.{u}} (x : X _⦋0⦌) : (subdivision X) _⦋0⦌ := X.σ 0 x

@[simp] theorem endpoint_vertex {X : SSet.{u}} (x : X _⦋0⦌) :
    (endpoint X).app _ (vertex x) = x := by
  have hr : second.app ⦋0⦌ = SimplexCategory.δ 0 := by
    ext i : 3
    have hi : i = 0 := by
      exact @Subsingleton.elim (Fin 1) inferInstance i 0
    subst i
    rfl
  change X.map (second.app ⦋0⦌).op (X.σ 0 x) = x
  rw [hr]
  change X.δ 0 (X.σ 0 x) = x
  exact X.δ_comp_σ_self_apply 0 x

/-- The canonical forward equivalence preserves the original chosen vertex. -/
@[simp] theorem realizationHomotopyEquiv_vertex {X : SSet.{u}} (x : X _⦋0⦌) :
    realizationHomotopyEquiv X (realizationPoint (vertex x)) = realizationPoint x := by
  rw [realizationHomotopyEquiv_point, endpoint_vertex]

end Quillen.Edgewise
