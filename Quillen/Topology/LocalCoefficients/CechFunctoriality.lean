/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.CechAugmentation
public import Quillen.Topology.LocalCoefficients.SmallChainFunctoriality

/-!
# Actual spatial maps of twisted Čech chains

A continuous map respecting indexed cover members sends each labeled
singular simplex to its original composite, retaining the pulled-back
coefficient. This gives the original map of bisimplicial modules, bicomplexes,
and total complexes, together with the actual augmentation square.
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

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {ι κ : Type u} (f : C(X, Y)) (U : ι → Set X) (V : κ → Set Y)
  (index : ι → κ) (h : ∀ i, Set.MapsTo f (U i) (V (index i))) (A : System.{u, u} Y)

/-- The original composite simplex with the corresponding actual containing members. -/
def pushforwardCechSimplex {n p : SimplexCategory} (t : CechSimplex U n p) :
    CechSimplex V n p :=
  ⟨⟨f.comp t.1.val, t.1.property.map index h⟩, fun i ↦
    ⟨index (t.2 i).val, by rintro _ ⟨x, rfl⟩; exact h _ ((t.2 i).property ⟨x, rfl⟩)⟩⟩

/-- Push forward the actual labeled singular simplex, with its unchanged coefficient. -/
def cechPushforwardModuleMap (n p : SimplexCategory) :
    cechChainModule U (pullback f A) n p ⟶ cechChainModule V A n p :=
  Sigma.desc fun t ↦ cechChainInclusion V A (pushforwardCechSimplex f U V index h t)

/-- Spatial pushforward commutes with restriction of the cover-label list. -/
@[reassoc]
theorem cechPushforwardModuleMap_cover (n : SimplexCategory)
    {p q : SimplexCategory} (α : p ⟶ q) :
    cechChainMap U (pullback f A) n α ≫ cechPushforwardModuleMap f U V index h A n p =
      cechPushforwardModuleMap f U V index h A n q ≫ cechChainMap V A n α := by
  apply Sigma.hom_ext
  intro t
  simp [cechChainMap, cechPushforwardModuleMap, cechChainInclusion,
    restrictCechSimplex, pushforwardCechSimplex]

/-- Spatial pushforward commutes with genuine singular restriction and transport. -/
@[reassoc]
theorem cechPushforwardModuleMap_singular (p : SimplexCategory)
    {m n : SimplexCategory} (α : m ⟶ n) :
    cechSingularMap U (pullback f A) p α ≫ cechPushforwardModuleMap f U V index h A m p =
      cechPushforwardModuleMap f U V index h A n p ≫ cechSingularMap V A p α := by
  apply Sigma.hom_ext
  intro t
  simp [cechSingularMap, cechPushforwardModuleMap, cechChainInclusion]
  rfl

/-- The original spatial morphism of Čech simplicial rows. -/
def cechPushforwardSimplicialRow (n : SimplexCategory) :
    cechSimplicialModule U (pullback f A) n ⟶ cechSimplicialModule V A n where
  app p := cechPushforwardModuleMap f U V index h A n p.unop
  naturality _ _ α := cechPushforwardModuleMap_cover f U V index h A n α.unop

/-- The actual spatial map of twisted Čech bisimplicial modules. -/
def cechPushforwardBisimplicial :
    cechBisimplicialModule U (pullback f A) ⟶ cechBisimplicialModule V A where
  app n := cechPushforwardSimplicialRow f U V index h A n.unop
  naturality _ _ α := by
    ext p : 1
    exact cechPushforwardModuleMap_singular f U V index h A p.unop α.unop

/-- The genuine spatial map of the simplicial family of row complexes. -/
def cechPushforwardRowComplexes :
    cechSimplicialRowComplexes U (pullback f A) ⟶ cechSimplicialRowComplexes V A :=
  Functor.whiskerRight (cechPushforwardBisimplicial f U V index h A)
    (AlgebraicTopology.alternatingFaceMapComplex _)

/-- Taking original alternating faces produces the spatial bicomplex map. -/
def cechPushforwardBicomplex : cechBicomplex U (pullback f A) ⟶ cechBicomplex V A :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map
    (cechPushforwardRowComplexes f U V index h A)

/-- The original spatial map on the actual total complexes. -/
def cechPushforwardTotal : cechTotalComplex U (pullback f A) ⟶ cechTotalComplex V A :=
  HomologicalComplex₂.total.map (cechPushforwardBicomplex f U V index h A) (ComplexShape.down ℕ)

/-- Forgetting labels retains the original spatial map of small-chain modules. -/
@[reassoc]
theorem cechPushforwardModuleMap_augmentation (n p : SimplexCategory) :
    cechPushforwardModuleMap f U V index h A n p ≫ cechModuleAugmentation V A n p =
      cechModuleAugmentation U (pullback f A) n p ≫
        smallPushforwardModuleMap f U V A (fun hσ ↦ hσ.map index h) n := by
  apply Sigma.hom_ext
  intro t
  simp [cechPushforwardModuleMap, cechModuleAugmentation, smallPushforwardModuleMap,
    cechChainInclusion, smallChainInclusion, pushforwardCechSimplex]

/-- The corresponding actual spatial map on the small-chain target bicomplexes. -/
def smallSinglePushforwardBicomplex :
    smallSingleBicomplex U (pullback f A) ⟶ smallSingleBicomplex V A :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map
    (Functor.whiskerRight (smallPushforwardSimplicialMap f U V A (fun hσ ↦ hσ.map index h))
      (ChainComplex.single₀ _))

/-- The actual spatial bicomplex map commutes with the original augmentation. -/
@[reassoc]
theorem cechPushforwardBicomplex_augmentation :
    cechPushforwardBicomplex f U V index h A ≫ cechBicomplexAugmentation V A =
      cechBicomplexAugmentation U (pullback f A) ≫
        smallSinglePushforwardBicomplex f U V index h A := by
  ext n : 1
  apply HomologicalComplex.to_single_hom_ext
  change cechPushforwardModuleMap f U V index h A ⦋n⦌ ⦋0⦌ ≫
    cechModuleAugmentation V A ⦋n⦌ ⦋0⦌ =
      cechModuleAugmentation U (pullback f A) ⦋n⦌ ⦋0⦌ ≫
        ((ChainComplex.single₀ _).map
          (smallPushforwardModuleMap f U V A (fun hσ ↦ hσ.map index h) ⦋n⦌)).f 0
  rw [ChainComplex.single₀_map_f_zero]
  exact cechPushforwardModuleMap_augmentation f U V index h A ⦋n⦌ ⦋0⦌

/-- The same augmentation square after genuine totalization. -/
@[reassoc]
theorem cechPushforwardTotal_augmentation :
    cechPushforwardTotal f U V index h A ≫ cechTotalAugmentation V A =
      cechTotalAugmentation U (pullback f A) ≫
        HomologicalComplex₂.total.map (smallSinglePushforwardBicomplex f U V index h A)
          (ComplexShape.down ℕ) := by
  simpa only [cechPushforwardTotal, cechTotalAugmentation,
    HomologicalComplex₂.total.map_comp] using
    congrArg (fun g ↦ HomologicalComplex₂.total.map g (ComplexShape.down ℕ))
      (cechPushforwardBicomplex_augmentation f U V index h A)

end Quillen.LocalCoefficients
