/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Single
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Closure
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Quillen.Aglib.Algebra.Homology.DerivedCategory.TopSingleRepresentative

/-!
# Strict reassembly from an actual top attachment

The actual vector-bundle single, its given cone model and the exact interval [a,b-1] reassemble
the original complex in [a,b]. Only the retained top-single chain realization is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Opposite ModuleCat HomologicalComplex
open AlgebraicGeometry.Scheme.Modules.Complex AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
/-- The standard derived category of module sheaves, used for strict-model reassembly. -/
local instance reassemblyStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- A strict model of the cone of a top-degree vector-bundle attachment
reassembles to a strict model of the original object in the exact interval.
Only maps to the top single are realized by chain maps. -/
theorem strict_model_of_top_attachment {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (V : X.Modules) [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X V]
    (a b : ℤ) (hab : a ≤ b)
    (f : (CochainComplex.singleFunctor X.Modules b).obj V ⟶ K)
    (P : StrictPerfect X)
    (hP : ∀ i, i < a ∨ b - 1 < i → IsZero (P.obj.X i))
    (eP : (DerivedCategory.Q (C := X.Modules)).obj (CochainComplex.mappingCone f) ≅
      (DerivedCategory.Q (C := X.Modules)).obj P.obj) :
    ∃ S : StrictPerfect X, (∀ i, i < a ∨ b < i → IsZero (S.obj.X i)) ∧
      Nonempty ((DerivedCategory.Q (C := X.Modules)).obj S.obj ≅
        (DerivedCategory.Q (C := X.Modules)).obj K) := by
  let A := (CochainComplex.singleFunctor X.Modules b).obj V
  let B := (CochainComplex.singleFunctor X.Modules (b - 1)).obj V
  let T := (DerivedCategory.Q (C := X.Modules)).mapTriangle.obj
    (CochainComplex.mappingCone.triangle f)
  let eV : ((DerivedCategory.Q (C := X.Modules)).obj A)⟦(1 : ℤ)⟧ ≅
    (DerivedCategory.Q (C := X.Modules)).obj B :=
    ((DerivedCategory.singleFunctors X.Modules).shiftIso 1 (b - 1) b (by omega)).app V
  have : P.obj.IsStrictlyLE (b - 1) :=
    (CochainComplex.isStrictlyLE_iff _ _).mpr (fun i hi => hP i (Or.inr hi))
  let α : (DerivedCategory.Q (C := X.Modules)).obj P.obj ⟶
    (DerivedCategory.Q (C := X.Modules)).obj B :=
    eP.inv ≫ T.mor₃ ≫ eV.hom
  obtain ⟨g, hg⟩ := exists_chain_to_top_single P.obj (b - 1) V α
  change (DerivedCategory.Q (C := X.Modules)).map g = α at hg
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished f
  have hcomm : (DerivedCategory.Q (C := X.Modules)).map g ≫ eV.inv = eP.inv
    ≫ T.rotate.rotate.mor₁ := by
    change (DerivedCategory.Q (C := X.Modules)).map g ≫ eV.inv = eP.inv ≫ T.mor₃
    rw [hg]
    simp [α]
  let eC : (DerivedCategory.Q (C := X.Modules)).obj (CochainComplex.mappingCone g) ≅
      ((DerivedCategory.Q (C := X.Modules)).obj K)⟦(1 : ℤ)⟧ :=
    Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ T.rotate.rotate
      (DerivedCategory.mappingCone_triangle_distinguished g)
      (rot_of_distTriang _ (rot_of_distTriang _ hT)) eP.symm eV.symm hcomm)
  let S : StrictPerfect X := ⟨(CochainComplex.mappingCone g)⟦(-1 : ℤ)⟧,
    strictPerfect_shift
      (strictPerfect_mappingCone P.property (single_strictPerfect_int V (b - 1)) g) (-1)⟩
  refine ⟨S, ?_, ⟨?_⟩⟩
  · intro i hi
    change IsZero ((CochainComplex.mappingCone g).X (i + -1))
    apply (CochainComplex.mappingCone.isZero_X_iff g (i + -1)).mpr
    constructor
    · apply hP
      rcases hi with hi | hi
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by rcases hi with hi | hi <;> omega)
  · change (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.mappingCone g)⟦(-1 : ℤ)⟧) ≅ _
    exact ((DerivedCategory.Q (C := X.Modules)).commShiftIso (-1)).app
      (CochainComplex.mappingCone g) ≪≫
      (shiftFunctor (DerivedCategory X.Modules) (-1)).mapIso eC ≪≫
      (shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by omega)).app
        ((DerivedCategory.Q (C := X.Modules)).obj K)



end Quillen.PerfectComplexes.ProjectiveLine
end
end
