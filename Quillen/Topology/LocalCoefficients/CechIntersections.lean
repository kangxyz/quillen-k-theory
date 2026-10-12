/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.CechFunctoriality
public import Quillen.Topology.LocalCoefficients.SubspaceChains

/-!
# Actual intersection summands of the twisted Čech columns

In fixed Čech degree, labeled singular simplices reindex as the coproduct,
over ordered lists of cover members, of actual small chains in their common
intersection. The reindexing preserves the original coefficient fiber and
commutes with the original singular transport.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type u}
  (U : ι → Set X) (A : System.{u, u} X)

/-- The actual intersection specified by a nonempty ordered list of cover members. -/
def cechIntersection {p : SimplexCategory} (l : Fin (p.len + 1) → ι) : Set X :=
  {x | ∀ i, x ∈ U (l i)}

/-- Forget the membership proofs while retaining the entire ordered cover list. -/
def cechSimplexLabels {n p : SimplexCategory} (t : CechSimplex U n p) : Fin (p.len + 1) → ι :=
  fun i ↦ (t.2 i).val

/-- The original simplex lies in the actual intersection of all its containing labels. -/
def cechSimplexInIntersection {n p : SimplexCategory} (t : CechSimplex U n p) :
    CoverSmallSimplex (singletonCover (cechIntersection U (cechSimplexLabels U t))) n :=
  ⟨t.1.val, ⟨(), fun _ hx i ↦ (t.2 i).property hx⟩⟩

/-- A simplex in an actual intersection has the corresponding complete list of cover labels. -/
def intersectionCechSimplex {n p : SimplexCategory} (l : Fin (p.len + 1) → ι)
    (σ : CoverSmallSimplex (singletonCover (cechIntersection U l)) n) : CechSimplex U n p :=
  ⟨⟨σ.val, ⟨l 0, fun _ hx ↦ σ.property.choose_spec hx 0⟩⟩,
    fun i ↦ ⟨l i, fun _ hx ↦ σ.property.choose_spec hx i⟩⟩

/-- The actual coproduct of the intersection-small chain modules. -/
def cechIntersectionModule (n p : SimplexCategory) : ModuleCat.{u} ℤ :=
  ∐ fun l : Fin (p.len + 1) → ι ↦ smallChainModule (singletonCover (cechIntersection U l)) A n

/-- Reindex labeled chains as original intersection-small chains. -/
def cechIntersectionModuleIso (n p : SimplexCategory) :
    cechChainModule U A n p ≅ cechIntersectionModule U A n p where
  hom := Sigma.desc fun t ↦
    smallChainInclusion (singletonCover (cechIntersection U (cechSimplexLabels U t))) A
      (cechSimplexInIntersection U t) ≫
      Sigma.ι (fun l : Fin (p.len + 1) → ι ↦
        smallChainModule (singletonCover (cechIntersection U l)) A n) (cechSimplexLabels U t)
  inv := Sigma.desc fun l ↦ Sigma.desc fun σ ↦
    cechChainInclusion U A (intersectionCechSimplex U l σ)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro t
    simp [cechChainInclusion, smallChainInclusion, cechSimplexInIntersection,
      intersectionCechSimplex, cechSimplexLabels, cechChainModule]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro l
    apply Sigma.hom_ext
    intro σ
    simp only [cechChainInclusion, smallChainInclusion, Sigma.ι_comp_desc_assoc,
      Sigma.ι_comp_desc]
    rfl

/-- Original singular restriction acts separately in each actual intersection summand. -/
def cechIntersectionModuleMap (p : SimplexCategory) {m n : SimplexCategory} (α : m ⟶ n) :
    cechIntersectionModule U A n p ⟶ cechIntersectionModule U A m p :=
  Sigma.desc fun l ↦ smallChainMap (singletonCover (cechIntersection U l)) A α ≫
    Sigma.ι (fun k : Fin (p.len + 1) → ι ↦
      smallChainModule (singletonCover (cechIntersection U k)) A m) l

/-- The original reindexing commutes with the genuine local-system differential. -/
@[reassoc]
theorem cechIntersectionModuleIso_naturality (p : SimplexCategory)
    {m n : SimplexCategory} (α : m ⟶ n) :
    cechSingularMap U A p α ≫ (cechIntersectionModuleIso U A m p).hom =
      (cechIntersectionModuleIso U A n p).hom ≫ cechIntersectionModuleMap U A p α := by
  apply Sigma.hom_ext
  intro t
  simp [cechSingularMap, cechIntersectionModuleIso, cechIntersectionModuleMap,
    smallChainInclusion, cechChainInclusion, smallChainMap]
  rfl

/-- The actual singular simplicial column in fixed Čech degree. -/
def cechSingularSimplicialColumn (p : SimplexCategory) : SimplicialObject (ModuleCat.{u} ℤ) where
  obj n := cechChainModule U A n.unop p
  map α := cechSingularMap U A p α.unop
  map_id n := cechSingularMap_id U A n.unop p
  map_comp α β := cechSingularMap_comp U A p β.unop α.unop

/-- The actual intersection-summand simplicial column. -/
def cechIntersectionSimplicialColumn (p : SimplexCategory) :
    SimplicialObject (ModuleCat.{u} ℤ) where
  obj n := cechIntersectionModule U A n.unop p
  map α := cechIntersectionModuleMap U A p α.unop
  map_id n := by
    apply Sigma.hom_ext
    intro l
    simp [cechIntersectionModuleMap, cechIntersectionModule]
  map_comp α β := by
    apply Sigma.hom_ext
    intro l
    simp [cechIntersectionModuleMap, smallChainMap_comp, Category.assoc]

/-- Actual singular columns identify with the intersection summands simplicially. -/
def cechIntersectionSimplicialIso (p : SimplexCategory) :
    cechSingularSimplicialColumn U A p ≅ cechIntersectionSimplicialColumn U A p :=
  NatIso.ofComponents (fun n ↦ cechIntersectionModuleIso U A n.unop p)
    (fun α ↦ cechIntersectionModuleIso_naturality U A p α.unop)

/-- The actual twisted singular column of the Čech bicomplex. -/
def cechSingularColumnComplex (p : SimplexCategory) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (cechSingularSimplicialColumn U A p)

/-- The genuine chain complex of the intersection summands. -/
def cechIntersectionColumnComplex (p : SimplexCategory) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (cechIntersectionSimplicialColumn U A p)

/-- The original twisted column differential respects the actual intersection decomposition. -/
def cechIntersectionColumnIso (p : SimplexCategory) :
    cechSingularColumnComplex U A p ≅ cechIntersectionColumnComplex U A p :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso (cechIntersectionSimplicialIso U A p)

end Quillen.LocalCoefficients
