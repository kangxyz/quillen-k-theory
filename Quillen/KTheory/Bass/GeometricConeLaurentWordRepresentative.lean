/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDoubleLaurentQuotient
public import Quillen.KTheory.Bass.GeometricConeBetaRecursion

/-!
# Original finite Laurent representatives and the actual geometric word

The successive original target inclusions define a representative of every finite
unlooped cone iterate. A second representative uses the actual endofunctor powers;
the comparison retains the original complete `power_obj` equality transport.
The literal Laurent insertion and reversal words are built from actual scheme
factor swaps. Their action on representatives is proved from the original
local double-cone formula and raw inclusion naturality, with no connectivity,
epimorphism, quotient-sign, or desired whole-word square hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum
universe u w
namespace Quillen.KTheory.Bass.GeometricConeInterchange
open FiniteConeTopology GeometricConeFixedWords

local notation "L" => laurent.op

/-- Raw scheme naturality of the original target inclusion, before stable homotopy. -/
@[reassoc]
theorem coneInclusion_naturality (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    F.map ((L).map f) ≫ coneInclusion F Y =
      coneInclusion F X ≫ (coneFunctor.obj F).map f :=
  (mappingConeInclusionSquare (strictSquareComparisonFunctor.map
    (F.mapArrow.mapArrow.map (squareFunctor.map f)))).w

/-- The original target inclusion is natural in the entire input spectrum diagram. -/
@[reassoc]
theorem coneInclusion_diagramMap
    {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}} (a : F ⟶ G) (X : Scheme.{u}ᵒᵖ) :
    a.app ((L).obj X) ≫ coneInclusion G X =
      coneInclusion F X ≫ (ConeTrack.map squareFunctor a).app X := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  rfl

/-- The literal nested Laurent bases, associated to match the original inclusion recursion. -/
def laurentIterate : ℕ → Scheme.{u}ᵒᵖ ⥤ Scheme.{u}ᵒᵖ
  | 0 => 𝟭 _
  | n + 1 => L ⋙ laurentIterate n

/-- The finite representative into the original unlooped cone iterates. -/
def laurentInclusion : ∀ (n : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ), F.obj ((laurentIterate n).obj X) ⟶
      (iterate squareFunctor n F).obj X
  | 0, F, X => 𝟙 (F.obj X)
  | n + 1, F, X => laurentInclusion n F ((L).obj X) ≫
      coneInclusion (iterate squareFunctor n F) X

/-- The same successive inclusions into the actual endofunctor powers. -/
def powerLaurentInclusion : ∀ (n : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ), F.obj ((laurentIterate n).obj X) ⟶
      ((Functor.FixedWords.power coneFunctor n).obj F).obj X
  | 0, F, X => 𝟙 (F.obj X)
  | n + 1, F, X => powerLaurentInclusion n F ((L).obj X) ≫
      coneInclusion ((Functor.FixedWords.power coneFunctor n).obj F) X

/-- The original complete successor cast is the cone image of the preceding cast. -/
theorem power_obj_succ_hom (n : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    eqToHom (power_obj (n + 1) F) = coneFunctor.map (eqToHom (power_obj n F)) :=
  (eqToHom_map coneFunctor (power_obj n F)).symm

/-- The finite representative comparison retains the original `power_obj` cast. -/
@[reassoc]
theorem powerLaurentInclusion_cast (n : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) :
    powerLaurentInclusion n F X ≫ (eqToHom (power_obj n F)).app X =
      laurentInclusion n F X := by
  induction n generalizing X with
  | zero => simp only [powerLaurentInclusion, laurentInclusion,
      eqToHom_refl, NatTrans.id_app, Category.comp_id]
  | succ n ih =>
    rw [power_obj_succ_hom, coneFunctor_map]
    simp only [powerLaurentInclusion, laurentInclusion, Category.assoc,
      ← coneInclusion_diagramMap]
    rw [← Category.assoc, ih]

/-- Original finite representatives are natural in every actual scheme map. -/
@[reassoc]
theorem laurentInclusion_naturality (n : ℕ)
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    F.map ((laurentIterate n).map f) ≫ laurentInclusion n F Y =
      laurentInclusion n F X ≫ (iterate squareFunctor n F).map f := by
  induction n generalizing X Y with
  | zero => exact (Category.comp_id (F.map f)).trans (Category.id_comp (F.map f)).symm
  | succ n ih =>
    change F.map ((laurentIterate n).map ((L).map f)) ≫
        (laurentInclusion n F ((L).obj Y) ≫ coneInclusion (iterate squareFunctor n F) Y) =
      (laurentInclusion n F ((L).obj X) ≫ coneInclusion (iterate squareFunctor n F) X) ≫
        (coneFunctor.obj (iterate squareFunctor n F)).map f
    rw [← Category.assoc, ih, Category.assoc, coneInclusion_naturality, Category.assoc]

/-- The last two original inclusions give the existing double-Laurent representative. -/
theorem laurentInclusion_succ_succ (n : ℕ)
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    laurentInclusion (n + 2) F X =
      laurentInclusion n F ((L).obj ((L).obj X)) ≫
        doubleLaurentInclusion (iterate squareFunctor n F) X := by
  exact Category.assoc _ _ _

/-- The unchanged original two-factor Scheme swap, in the actual opposite direction. -/
def laurentSwapMap (X : Scheme.{u}ᵒᵖ) :
    (L).obj ((L).obj X) ⟶ (L).obj ((L).obj X) :=
  (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
    (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op

/-- The literal insertion word moving a new Laurent factor through the previous block. -/
def laurentInsertionMap : ∀ (n : ℕ) (X : Scheme.{u}ᵒᵖ),
    (laurentIterate (n + 1)).obj X ⟶ (laurentIterate (n + 1)).obj X
  | 0, X => 𝟙 ((L).obj X)
  | n + 1, X => (laurentIterate n).map (laurentSwapMap X) ≫
      laurentInsertionMap n ((L).obj X)

/-- The prescribed literal reversal word, accumulated from the original insertions. -/
def laurentReversalMap : ∀ (n : ℕ) (X : Scheme.{u}ᵒᵖ),
    (laurentIterate n).obj X ⟶ (laurentIterate n).obj X
  | 0, X => 𝟙 X
  | n + 1, X => laurentReversalMap n ((L).obj X) ≫ laurentInsertionMap n X

/-- The local geometric permutation acts by its actual scheme swap on finite representatives. -/
@[reassoc]
theorem laurentInclusion_local_swap (n : ℕ)
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    laurentInclusion (n + 2) F X ≫ (permutationNatIso (iterate squareFunctor n F)).hom.app X =
      F.map ((laurentIterate n).map (laurentSwapMap X)) ≫ laurentInclusion (n + 2) F X := by
  rw [laurentInclusion_succ_succ, Category.assoc]
  change laurentInclusion n F ((L).obj ((L).obj X)) ≫
      (doubleLaurentInclusion (iterate squareFunctor n F) X ≫
        (permutation (iterate squareFunctor n F) X).hom) = _
  rw [doubleLaurentInclusion_permutation, ← Category.assoc,
    ← laurentInclusion_naturality, Category.assoc]
  rfl

/-- A known representative equation lifts through one actual original cone inclusion. -/
theorem laurentInclusion_cone_action (n : ℕ)
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (a : iterate squareFunctor n F ⟶ iterate squareFunctor n F) (X : Scheme.{u}ᵒᵖ)
    (f : (laurentIterate n).obj ((L).obj X) ⟶ (laurentIterate n).obj ((L).obj X))
    (h : laurentInclusion n F ((L).obj X) ≫ a.app ((L).obj X) =
      F.map f ≫ laurentInclusion n F ((L).obj X)) :
    laurentInclusion (n + 1) F X ≫ (ConeTrack.map squareFunctor a).app X =
      F.map f ≫ laurentInclusion (n + 1) F X := by
  simp only [laurentInclusion, Category.assoc, ← coneInclusion_diagramMap]
  rw [← Category.assoc, h, Category.assoc]

/-- Every actual insertion acts by its literal Laurent insertion on original representatives. -/
@[reassoc]
theorem laurentInclusion_betaAt (n : ℕ)
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    laurentInclusion (n + 1) F X ≫ (betaAt n F).hom.app X =
      F.map (laurentInsertionMap n X) ≫ laurentInclusion (n + 1) F X := by
  induction n generalizing X with
  | zero =>
    rw [betaAt_zero_hom]
    exact (Category.comp_id (laurentInclusion 1 F X)).trans
      ((congrArg (fun k => k ≫ laurentInclusion 1 F X) (F.map_id ((L).obj X))).trans
        (Category.id_comp _)).symm
  | succ n ih =>
    have hl := laurentInclusion_cone_action (n + 1) F (betaAt n F).hom X
      (laurentInsertionMap n ((L).obj X)) (ih ((L).obj X))
    simp only [betaAt_succ_hom, NatTrans.comp_app]
    rw [laurentInclusion_local_swap_assoc, hl]
    simp only [laurentInsertionMap, F.map_comp, Category.assoc]

/-- The original cast-preserving geometric word acts by the actual Laurent reversal word. -/
@[reassoc]
theorem laurentInclusion_wordAt (n : ℕ)
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    laurentInclusion n F X ≫ (wordAt n F).hom.app X =
      F.map (laurentReversalMap n X) ≫ laurentInclusion n F X := by
  induction n generalizing X with
  | zero =>
    rw [wordAt_zero_hom]
    exact (Category.comp_id (laurentInclusion 0 F X)).trans
      (((congrArg (fun k => k ≫ laurentInclusion 0 F X) (F.map_id X))).trans
        (Category.id_comp _)).symm
  | succ n ih =>
    have hl := laurentInclusion_cone_action n F (wordAt n F).hom X
      (laurentReversalMap n ((L).obj X)) (ih ((L).obj X))
    simp only [wordAt_succ_hom, NatTrans.comp_app]
    rw [← Category.assoc, hl, Category.assoc, laurentInclusion_betaAt]
    simp only [laurentReversalMap, F.map_comp, Category.assoc]

/-- The same word square keeps the explicit original power-to-iterate transport. -/
@[reassoc]
theorem powerLaurentInclusion_wordAt (n : ℕ)
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    powerLaurentInclusion n F X ≫ (eqToHom (power_obj n F)).app X ≫
        (wordAt n F).hom.app X =
      F.map (laurentReversalMap n X) ≫ powerLaurentInclusion n F X ≫
        (eqToHom (power_obj n F)).app X := by
  rw [powerLaurentInclusion_cast_assoc, powerLaurentInclusion_cast,
    laurentInclusion_wordAt]

end Quillen.KTheory.Bass.GeometricConeInterchange
