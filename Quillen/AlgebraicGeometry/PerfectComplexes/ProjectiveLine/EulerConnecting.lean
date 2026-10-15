/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.EulerInverse
public import Quillen.Algebra.Homology.DerivedCategory.PlusComplexTriangle

/-! # The actual natural Euler connecting isomorphism in D+ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.Euler
open FlasqueCoefficients
variable (R : CommRingCat.{u})

local instance eulerConnectingStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

local instance toPlus_additive (X : Scheme.{u}) : (toPlus X).Additive := by
  unfold toPlus
  infer_instance

lemma flasqueSequencePlus_shortExact {X : Scheme.{u}}
    (S : ShortComplex (FlasqueBoundedBelow.Obj X))
    (hS : (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
      (Quillen.abelianExactStructure (Complex X))
      (FlasqueBoundedBelow.objects X)).conflation S) :
    ((S.map (toPlus X)).map (CochainComplex.Plus.ι X.Modules)).ShortExact := hS

/-- The original projected incidence map, retaining its actual bounded-below inclusion. -/
def plusFirst : E2 R ⋙ toPlus (Spec R) ⟶ E1 R ⋙ toPlus (Spec R) :=
  Functor.whiskerRight (projectedFirst R) (toPlus (Spec R))

/-- The original projected determinant quotient map with that same inclusion. -/
def plusSecond : E1 R ⋙ toPlus (Spec R) ⟶ E0 R ⋙ toPlus (Spec R) :=
  Functor.whiskerRight (projectedSecond R) (toPlus (Spec R))

lemma plusFirst_second : plusFirst R ≫ plusSecond R = 0 := by
  apply NatTrans.ext
  funext A
  have hw : (projectedFirst R).app A ≫ (projectedSecond R).app A = 0 :=
    NatTrans.congr_app (projectedFirst_second R) A
  change (toPlus (Spec R)).map ((projectedFirst R).app A) ≫
    (toPlus (Spec R)).map ((projectedSecond R).app A) = 0
  rw [← Functor.map_comp, hw, Functor.map_zero]

/-- The actual original Euler sequence, with its original maps and strict lower bounds. -/
def projectedPlusSequence (A : StrictPerfect (Spec R)) :
    ShortComplex (CochainComplex.Plus (Spec R).Modules) :=
  ShortComplex.mk ((plusFirst R).app A) ((plusSecond R).app A)
    (NatTrans.congr_app (plusFirst_second R) A)

lemma projectedPlusSequence_shortExact (A : StrictPerfect (Spec R)) :
    ((projectedPlusSequence R A).map (CochainComplex.Plus.ι (Spec R).Modules)).ShortExact := by
  have h := flasqueSequencePlus_shortExact _ (projectedModelSequence_conflation R A)
  dsimp only [projectedPlusSequence, projectedModelSequence, boundedModelSequence,
    plusFirst, plusSecond, projectedFirst, projectedSecond, ShortComplex.map,
    Functor.comp_obj, Functor.whiskerRight_app, E2, E1, E0, projectedEndpoint] at h ⊢
  exact h

/-- Canonical SES connecting arrows are natural for actual natural sequences of Plus functors. -/
def connectingOfSequence
    {F G H : StrictPerfect (Spec R) ⥤ CochainComplex.Plus (Spec R).Modules}
    (a : F ⟶ G) (b : G ⟶ H) (w : a ≫ b = 0)
    (hs : ∀ A, ((ShortComplex.mk (a.app A) (b.app A) (NatTrans.congr_app w A)).map
      (CochainComplex.Plus.ι (Spec R).Modules)).ShortExact) :
    H ⋙ DerivedCategory.Plus.Q ⟶ F ⋙ DerivedCategory.Plus.Q ⋙
      shiftFunctor (DerivedCategory.Plus (Spec R).Modules) (1 : ℤ) where
  app A := (DerivedCategory.Plus.triangleOfSESPlus (hs A)).mor₃
  naturality {A B} f := by
    have h := (DerivedCategory.Plus.triangleOfSESPlusMap (hs A) (hs B)
      (Waldhausen.GilletWaldhausen.exactFunctorSequenceMap a b w f)).comm₃
    simpa only [DerivedCategory.Plus.triangleOfSESPlusMap_hom₁,
      DerivedCategory.Plus.triangleOfSESPlusMap_hom₃,
      Waldhausen.GilletWaldhausen.exactFunctorSequenceMap, Functor.comp_map] using h.symm

/-- The canonical original Euler connecting arrow retains Mathlib's actual SES cone sign. -/
def connecting : E0 R ⋙ toPlus (Spec R) ⋙ DerivedCategory.Plus.Q ⟶
    E2 R ⋙ toPlus (Spec R) ⋙ DerivedCategory.Plus.Q ⋙
      shiftFunctor (DerivedCategory.Plus (Spec R).Modules) (1 : ℤ) :=
  connectingOfSequence R (plusFirst R) (plusSecond R) (plusFirst_second R)
    (projectedPlusSequence_shortExact R)

/-- Actual middle vanishing makes precisely that canonical connecting arrow invertible. -/
instance connecting_isIso : IsIso (connecting R) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro A
  exact ((DerivedCategory.Plus.triangleOfSESPlus
    (projectedPlusSequence_shortExact R A)).isZero₂_iff_isIso₃
      (DerivedCategory.Plus.triangleOfSESPlus_distinguished
        (projectedPlusSequence_shortExact R A))).mp (middleProjected_derived_zero R A)

/-- The canonical connecting arrow to the actual shifted model uses native shift units. -/
def connectingToShift : E0 R ⋙ toPlus (Spec R) ⋙ DerivedCategory.Plus.Q ⟶
    E2Shift R ⋙ toPlus (Spec R) ⋙ DerivedCategory.Plus.Q :=
  connecting R ≫ (Functor.isoWhiskerLeft (E2 R) (modelShiftDerivedIso (Spec R) 1)).inv

instance connectingToShift_isIso : IsIso (connectingToShift R) := inferInstanceAs
  (IsIso (connecting R ≫ (Functor.isoWhiskerLeft (E2 R)
    (modelShiftDerivedIso (Spec R) 1)).inv))

/-- This isomorphism is fixed by the actual Euler connecting map and native shift comparison. -/
def connectingToShiftIso : E0 R ⋙ toPlus (Spec R) ⋙ DerivedCategory.Plus.Q ≅
    E2Shift R ⋙ toPlus (Spec R) ⋙ DerivedCategory.Plus.Q := asIso (connectingToShift R)

end Quillen.PerfectComplexes.ProjectiveLine.Euler
