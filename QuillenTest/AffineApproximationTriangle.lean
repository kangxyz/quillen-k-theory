/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.ApproximationTriangle
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PerfectOpenApproximation

/-!
# Affine approximation triangle regression statements

Records the maps, cone comparison, and distinguished-triangle property of the
original affine approximation triangle. The final statement retains an arbitrary
cutoff and the residual finite locally free homology in a single degree.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
universe u
attribute [local instance] Affine.standardDerivedModules Affine.standardDerivedSheaves
namespace QuillenTest.AffineApproximationTriangle

open Quillen

variable (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
  {P K : ModuleComplex R} (f : P ⟶ K) {E : Complex U}
  (eK : (toDerived U).obj ((restrict j).obj ((associatedComplex R).obj K)) ≅ (toDerived U).obj E)

theorem original_approximation_map :
    (originalApproximationTriangle R j f eK).mor₁ =
      (toDerived U).map ((restrict j).map ((associatedComplex R).map f)) ≫ eK.hom := rfl

theorem original_residual_map :
    (originalApproximationTriangle R j f eK).mor₂ =
      eK.inv ≫ (toDerived U).map
        ((restrict j).map ((associatedComplex R).map (CochainComplex.mappingCone.inr f))) :=
  originalApproximationBoundary_eq R j f eK

theorem original_cone_comparison :
    (restrict j).map ((associatedComplex R).map (CochainComplex.mappingCone.inr f)) ≫
      (openAssociatedConeIso R j f).hom =
      CochainComplex.mappingCone.inr ((restrict j).map ((associatedComplex R).map f)) :=
  openAssociatedConeIso_inr R j f

theorem original_roof_cone_equation :
    eK.hom ≫ (originalApproximationTriangle R j f eK).mor₂ =
      (toDerived U).map ((restrict j).map
        ((associatedComplex R).map (CochainComplex.mappingCone.inr f))) := by
  rw [original_residual_map]
  simp

theorem original_distinguished :
    originalApproximationTriangle R j f eK ∈ distTriang (Derived U) :=
  originalApproximationTriangle_distinguished R j f eK

theorem original_input_arbitrary_cutoff (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E) (cutoff : ℤ) :
    ∃ (K P : ModuleComplex R) (n : ℤ) (f : P ⟶ K)
      (eK : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj K)) ≅
        (toDerived W.toScheme).obj E)
      (eD : (toDerived W.toScheme).obj ((restrict W.ι).obj
          ((associatedComplex R).obj (CochainComplex.mappingCone f))) ≅
        (toDerived W.toScheme).obj ((CochainComplex.singleFunctor W.toScheme.Modules n).obj
          (((restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))).homology
            n))),
      moduleStrictPerfect R P ∧ n ≤ cutoff ∧
        AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree W.toScheme
          (((restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))).homology
            n) ∧
        originalApproximationSingleTriangle R W.ι f eK n eD ∈ distTriang (Derived W.toScheme) := by
  obtain ⟨K, a, b, P, n, f, hKa, hKb, hP, hn, ⟨eK⟩, hD, hDa, hDb, ⟨eD⟩⟩ :=
    locallyPerfect_exists_original_strict_approximation R W hW E hE cutoff
  exact ⟨K, P, n, f, eK, eD, hP, hn, hD,
    originalApproximationSingleTriangle_distinguished R W.ι f eK n eD⟩

end QuillenTest.AffineApproximationTriangle
