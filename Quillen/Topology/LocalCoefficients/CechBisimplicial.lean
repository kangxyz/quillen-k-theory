/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.CechContraction

/-!
# The actual twisted Čech bisimplicial module

Singular restriction retains every containing-cover label and uses the
original local-system transport. It commutes with restriction of the label
list. Thus the contracted Čech rows form a genuine bisimplicial module,
with an augmentation to the actual small singular simplicial module.
The independently chosen row contractions are not asserted to be natural
in the singular direction.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite Convexity
open scoped Simplicial

universe u

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type u}

/-- Equality of labeled simplices is equality of the original simplex and labels. -/
theorem cechSimplex_ext (U : ι → Set X) {n p : SimplexCategory}
    {s t : CechSimplex U n p} (hσ : s.1.val = t.1.val)
    (hl : ∀ i, (s.2 i).val = (t.2 i).val) : s = t := by
  rcases s with ⟨s, l⟩
  rcases t with ⟨t, k⟩
  have h : s = t := Subtype.ext hσ
  subst t
  congr 1
  funext i
  exact Subtype.ext (hl i)

/-- Singular restriction retains the same actual containing-cover members. -/
def singularRestrictCechSimplex (U : ι → Set X) {m n p : SimplexCategory}
    (t : CechSimplex U n p) (α : m ⟶ n) : CechSimplex U m p :=
  ⟨restrictSmallSimplex U t.1 α, fun i ↦ ⟨(t.2 i).val,
    fun _ ⟨x, hx⟩ ↦ (t.2 i).property ⟨StdSimplex.map α x, hx⟩⟩⟩

@[simp]
theorem singularRestrictCechSimplex_id (U : ι → Set X) {n p : SimplexCategory}
    (t : CechSimplex U n p) : singularRestrictCechSimplex U t (𝟙 n) = t := by
  apply cechSimplex_ext U (restrictSimplex_id t.1.val)
  intro i
  rfl

theorem singularRestrictCechSimplex_comp (U : ι → Set X) {l m n p : SimplexCategory}
    (t : CechSimplex U n p) (α : l ⟶ m) (β : m ⟶ n) :
    singularRestrictCechSimplex U t (α ≫ β) =
      singularRestrictCechSimplex U (singularRestrictCechSimplex U t β) α := by
  apply cechSimplex_ext U (restrictSimplex_comp t.1.val α β)
  intro i
  rfl

/-- Equality of labeled indices induces the canonical equality map of coefficients. -/
theorem cechChainInclusion_congr (U : ι → Set X) (A : System.{u, u} X)
    {n p : SimplexCategory} {s t : CechSimplex U n p} (h : s = t) :
    eqToHom (congrArg (fun r : CechSimplex U n p ↦ simplexFiber A r.1.val) h) ≫
      cechChainInclusion U A t = cechChainInclusion U A s := by
  subst t
  simp

/-- The singular-direction map uses precisely the original coefficient transport. -/
def cechSingularMap (U : ι → Set X) (A : System.{u, u} X) (p : SimplexCategory)
    {m n : SimplexCategory} (α : m ⟶ n) :
    cechChainModule U A n p ⟶ cechChainModule U A m p :=
  Sigma.desc fun t ↦ restrictionTransport A t.1.val α ≫
    cechChainInclusion U A (singularRestrictCechSimplex U t α)

@[reassoc (attr := simp)]
theorem cechChainInclusion_cechSingularMap (U : ι → Set X) (A : System.{u, u} X)
    {p m n : SimplexCategory} (α : m ⟶ n) (t : CechSimplex U n p) :
    cechChainInclusion U A t ≫ cechSingularMap U A p α =
      restrictionTransport A t.1.val α ≫
        cechChainInclusion U A (singularRestrictCechSimplex U t α) :=
  Sigma.ι_comp_desc _ _

@[simp]
theorem cechSingularMap_id (U : ι → Set X) (A : System.{u, u} X)
    (n p : SimplexCategory) : cechSingularMap U A p (𝟙 n) = 𝟙 _ := by
  apply Sigma.hom_ext
  intro t
  change cechChainInclusion U A t ≫ _ = cechChainInclusion U A t ≫ _
  rw [cechChainInclusion_cechSingularMap, Category.comp_id]
  have h : restrictionTransport A t.1.val (𝟙 n) =
      eqToHom (congrArg (simplexFiber A) (restrictSimplex_id t.1.val).symm) :=
    simplexTransport_eqToHom A t.1.val (StdSimplex.map_id _).symm
  rw [h]
  exact cechChainInclusion_congr U A (singularRestrictCechSimplex_id U t).symm

@[reassoc]
theorem cechSingularMap_comp (U : ι → Set X) (A : System.{u, u} X)
    (p : SimplexCategory) {l m n : SimplexCategory} (α : l ⟶ m) (β : m ⟶ n) :
    cechSingularMap U A p (α ≫ β) = cechSingularMap U A p β ≫ cechSingularMap U A p α := by
  apply Sigma.hom_ext
  intro t
  change cechChainInclusion U A t ≫ _ = cechChainInclusion U A t ≫ _
  simp only [cechChainInclusion_cechSingularMap, cechChainInclusion_cechSingularMap_assoc]
  dsimp only [singularRestrictCechSimplex, restrictSmallSimplex]
  rw [← Category.assoc, restrictionTransport_comp, Category.assoc]
  congr 1
  exact (cechChainInclusion_congr U A (singularRestrictCechSimplex_comp U t α β)).symm

/-- The two genuine simplicial directions commute, with unchanged local coefficients. -/
@[reassoc]
theorem cechSingularMap_cechChainMap (U : ι → Set X) (A : System.{u, u} X)
    {m n p q : SimplexCategory} (α : m ⟶ n) (β : p ⟶ q) :
    cechSingularMap U A q α ≫ cechChainMap U A m β =
      cechChainMap U A n β ≫ cechSingularMap U A p α := by
  apply Sigma.hom_ext
  intro t
  simp [cechSingularMap, cechChainMap, cechChainInclusion, singularRestrictCechSimplex,
    restrictCechSimplex]

/-- Singular restriction gives an actual morphism of Čech simplicial rows. -/
def cechRowSimplicialMap (U : ι → Set X) (A : System.{u, u} X)
    {m n : SimplexCategory} (α : m ⟶ n) :
    cechSimplicialModule U A n ⟶ cechSimplicialModule U A m where
  app p := cechSingularMap U A p.unop α
  naturality _p _q β := (cechSingularMap_cechChainMap U A α β.unop).symm

/-- The actual bisimplicial module, with singular degree outermost. -/
def cechBisimplicialModule (U : ι → Set X) (A : System.{u, u} X) :
    SimplicialObject (SimplicialObject (ModuleCat.{u} ℤ)) where
  obj n := cechSimplicialModule U A n.unop
  map α := cechRowSimplicialMap U A α.unop
  map_id n := by ext p : 1; exact cechSingularMap_id U A n.unop p.unop
  map_comp α β := by ext p : 1; exact cechSingularMap_comp U A p.unop β.unop α.unop

/-- Forgetting labels commutes with genuine singular restriction. -/
@[reassoc]
theorem cechSingularMap_augmentation (U : ι → Set X) (A : System.{u, u} X)
    {m n : SimplexCategory} (p : SimplexCategory) (α : m ⟶ n) :
    cechSingularMap U A p α ≫ cechModuleAugmentation U A m p =
      cechModuleAugmentation U A n p ≫ smallChainMap U A α := by
  apply Sigma.hom_ext
  intro t
  simp [cechSingularMap, cechModuleAugmentation, cechChainInclusion, smallChainInclusion,
    smallChainMap]
  rfl

/-- Singular restriction on the actual augmented rows. -/
def cechAugmentedRowMap (U : ι → Set X) (A : System.{u, u} X)
    {m n : SimplexCategory} (α : m ⟶ n) :
    cechAugmentedRow U A n ⟶ cechAugmentedRow U A m where
  left := cechRowSimplicialMap U A α
  right := smallChainMap U A α
  w := by ext p : 1; exact cechSingularMap_augmentation U A p.unop α

/-- The genuine simplicial family of augmented Čech rows. -/
def cechSimplicialAugmentedRows (U : ι → Set X) (A : System.{u, u} X) :
    SimplicialObject (SimplicialObject.Augmented (ModuleCat.{u} ℤ)) where
  obj n := cechAugmentedRow U A n.unop
  map α := cechAugmentedRowMap U A α.unop
  map_id n := by
    ext : 1
    · ext p : 1; exact cechSingularMap_id U A n.unop p.unop
    · exact smallChainMap_id U A n.unop
  map_comp α β := by
    ext : 1
    · ext p : 1; exact cechSingularMap_comp U A p.unop β.unop α.unop
    · exact smallChainMap_comp U A β.unop α.unop

end Quillen.LocalCoefficients
