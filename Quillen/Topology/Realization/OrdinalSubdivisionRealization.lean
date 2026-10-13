/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Realization.OrdinalSubdivisionSimplex
public import Quillen.Topology.Realization.EdgewiseCellular
public import Quillen.Topology.ClassifyingSpace.Equivalence
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preorder

/-!
# The canonical realization equivalence for ordinary twofold subdivision

The first-half endpoint map from the genuine ordinary twofold subdivision of every
simplicial set realizes to a homotopy equivalence. The proof contracts the
subdivision of each standard simplex, then glues along the actual simplicial
skeletal cell complex. No realization comparison is assumed as an input.
-/
@[expose] public section


noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.OrdinalSubdivision

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
      change Mono (f.app (δ.op.obj n))
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
    Edgewise.RealizesEquiv endpointNatTrans (Δ[n] : SSet.{u}) := by
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

/-- The canonical first-half endpoint realizes to a homotopy equivalence for
an arbitrary simplicial set, including infinite-dimensional ones. -/
theorem realizesEquiv_endpoint (X : SSet.{u}) : Edgewise.RealizesEquiv endpointNatTrans X :=
  Edgewise.realizesEquiv_all endpointNatTrans realizesEquiv_endpoint_simplex X

/-- Ordinary subdivision preserves the actual realization homotopy type.
Its forward map is exactly the realized first-half endpoint comparison. -/
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
  exact congrArg TopCat.Hom.hom (Edgewise.realization_naturality endpointNatTrans f)

/-- The forward equivalence sends every subdivided vertex to its endpoint vertex. -/
theorem realizationHomotopyEquiv_point (X : SSet.{u})
    (x : (subdivision X) _⦋0⦌) :
    realizationHomotopyEquiv X (realizationPoint x) =
      realizationPoint ((endpoint X).app _ x) :=
  realizationPoint_naturality (endpoint X) x

/-- A vertex of a simplicial set determines the degenerate interval vertex
of its ordinary twofold subdivision. -/
def vertex {X : SSet.{u}} (x : X _⦋0⦌) : (subdivision X) _⦋0⦌ := X.σ 0 x

@[simp] theorem endpoint_vertex {X : SSet.{u}} (x : X _⦋0⦌) :
    (endpoint X).app _ (vertex x) = x := by
  have hr : first.app ⦋0⦌ = SimplexCategory.δ 1 := by
    ext i : 3
    have hi : i = 0 := by
      exact @Subsingleton.elim (Fin 1) inferInstance i 0
    subst i
    rfl
  change X.map (first.app ⦋0⦌).op (X.σ 0 x) = x
  rw [hr]
  change X.δ 1 (X.σ 0 x) = x
  exact X.δ_comp_σ_succ_apply 0 x

/-- The canonical forward equivalence preserves the original chosen vertex. -/
theorem realizationHomotopyEquiv_vertex {X : SSet.{u}} (x : X _⦋0⦌) :
    realizationHomotopyEquiv X (realizationPoint (vertex x)) = realizationPoint x := by
  rw [realizationHomotopyEquiv_point, endpoint_vertex]

end Quillen.OrdinalSubdivision
