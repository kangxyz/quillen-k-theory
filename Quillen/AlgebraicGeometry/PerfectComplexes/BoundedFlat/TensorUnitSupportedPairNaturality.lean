/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedForgetNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PairPullback

/-! # Supported tensor input along the original geometric pair square

The actual supported pullback preserves the original restriction-acyclicity
predicate. Forgetting it intertwines its tensor-unit automorphism with the
original ambient tensor pullback through the displayed underlying isomorphism.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)

/-- Original supported pair pullback followed by the actual supported tensor functor. -/
def tensorSupportedPairFunctor :=
  boundedFlatPerfectSupportedPullback p ⋙ boundedFlatPerfectSupportedTensorUnit A.obj.hom

/-- The actual pair restriction and supported tensor retain their inherited exact structures. -/
theorem tensorSupportedPair_exact :
    IsExact (boundedFlatPerfectSupportedWaldhausen B.obj.hom).cof
      (boundedFlatPerfectSupportedWaldhausen B.obj.hom).weq
      (boundedFlatPerfectSupportedWaldhausen A.obj.hom).cof
      (boundedFlatPerfectSupportedWaldhausen A.obj.hom).weq (tensorSupportedPairFunctor p) :=
  (boundedFlatPerfectSupportedPullback_exact p).comp
    (boundedFlatPerfectSupportedTensorUnit_exact A.obj.hom)

/-- The original forward unit acts on every genuinely supported pulled-back complex. -/
def tensorSupportedPairAutomorphism (r : (Γ(A.obj.right, ⊤))ˣ) :
    tensorSupportedPairFunctor p ≅ tensorSupportedPairFunctor p :=
  Functor.isoWhiskerLeft (boundedFlatPerfectSupportedPullback p)
    (boundedFlatPerfectSupportedTensorUnitAutomorphism A.obj.hom r)

/-- Forgetting the pair support retains the original geometric tensor pullback. -/
def tensorSupportedPairForgetIso :
    tensorSupportedPairFunctor p ⋙ tensorCoefficientSupportedForget A.obj.hom ≅
      tensorCoefficientSupportedForget B.obj.hom ⋙
        boundedFlatPerfectTensorUnitPullback p.hom.right :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (by intro K L g; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- The complete actual pair-forgetting square preserves the original tensor coefficient. -/
theorem tensorSupportedPairForget_unit (r : (Γ(A.obj.right, ⊤))ˣ) :
    Functor.whiskerRight (tensorSupportedPairAutomorphism p r).hom
        (tensorCoefficientSupportedForget A.obj.hom) ≫ (tensorSupportedPairForgetIso p).hom =
      (tensorSupportedPairForgetIso p).hom ≫
        Functor.whiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
          (boundedFlatPerfectTensorUnitPullbackAutomorphism p.hom.right r).hom := by
  apply NatTrans.ext
  funext K
  apply (boundedFlatPerfect A.obj.right).ι.map_injective
  simp only [NatTrans.comp_app, tensorSupportedPairForgetIso, NatIso.ofComponents_hom_app,
    Iso.refl_hom, Category.id_comp, Category.comp_id, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, tensorSupportedPairAutomorphism, Functor.isoWhiskerLeft_hom,
    boundedFlatPerfectTensorUnitPullbackAutomorphism]
  exact (boundedFlatPerfectSupportedTensorUnitAutomorphism_hom_original A.obj.hom r
    ((boundedFlatPerfectSupportedPullback p).obj K)).trans
    (boundedFlatPerfectTensorUnitAutomorphism_hom_original A.obj.right r
      ((boundedFlatPerfectPullback p.hom.right).obj
        ((tensorCoefficientSupportedForget B.obj.hom).obj K))).symm

/-- The actual geometric supported input square realizes to its whole normalization-relative prism.
-/
def tensorSupportedPairForgetPasting (r : (Γ(A.obj.right, ⊤))ˣ) :=
  exactOriginalPrespectrumPastingHomotopy
    (boundedFlatPerfectSupportedWaldhausen B.obj.hom) (boundedFlatPerfectWaldhausen A.obj.right)
    ((tensorSupportedPair_exact p).comp (tensorCoefficientSupportedForget_exact A.obj.hom))
    ((tensorSupportedPair_exact p).comp (tensorCoefficientSupportedForget_exact A.obj.hom))
    ((tensorCoefficientSupportedForget_exact B.obj.hom).comp
      (boundedFlatPerfectTensorUnitPullback_exact p.hom.right))
    ((tensorCoefficientSupportedForget_exact B.obj.hom).comp
      (boundedFlatPerfectTensorUnitPullback_exact p.hom.right))
    (Functor.whiskerRight (tensorSupportedPairAutomorphism p r).hom
      (tensorCoefficientSupportedForget A.obj.hom))
    (tensorSupportedPairForgetIso p).hom (tensorSupportedPairForgetIso p).hom
    (Functor.whiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
      (boundedFlatPerfectTensorUnitPullbackAutomorphism p.hom.right r).hom)
    (fun _ => (boundedFlatPerfectWaldhausen A.obj.right).weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen A.obj.right).weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen A.obj.right).weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen A.obj.right).weq_iso _ inferInstance)
    (tensorSupportedPairForget_unit p r)

end Quillen.PerfectComplexes
