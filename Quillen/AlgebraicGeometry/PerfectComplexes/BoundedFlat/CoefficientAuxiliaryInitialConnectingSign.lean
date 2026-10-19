/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryInitialConnecting
public import Quillen.Waldhausen.SConstruction.Iterated.ModelStableHomotopy
public import Quillen.Waldhausen.Fibration.StableConnectingComparison

/-!
# The original native sign in initial auxiliary-supported localization

The intrinsic initial coefficient connecting map, evaluated by the actual
native supported-to-acyclic Model map, is the negative of the unchanged native
Waldhausen boundary class. The original native inclusion and degree cast
are kept explicitly; this does not yet identify a Bass telescope endpoint.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology
universe u
namespace Quillen.PerfectComplexes

private theorem stableMap_degree_cast {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    {d e : ℤ} (h : d = e) :
    eqToHom (congrArg (stableHomotopyGroup E) h) ≫ (stableHomotopyFunctor e).map f =
      (stableHomotopyFunctor d).map f ≫ eqToHom (congrArg (stableHomotopyGroup F) h) := by
  subst e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem piMap_congr {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (h : f = g) : piMap n f hf = piMap n g hg := by
  subst g
  rfl

/-- The literal common-universe inclusion preserves the original native K-stable class. -/
theorem boundedFlatCoefficientNativeSmallModelMap_stable (M : Model.{u})
    (F : M ⟶ modelOf M.waldhausen) (hF : F.functor = AsSmall.up)
    (n : ℕ) (x : M.waldhausen.K n) :
    (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap F)
        (modelKStableEquiv M n (Additive.ofMul x)) =
      originalKStableEquiv M.waldhausen n (Additive.ofMul x) := by
  have hK : KMap F.exact n x = M.waldhausen.smallModelKEquiv n x := by
    rw [KMap_eq_piMap_of_zeroEq F.exact F.zero]
    have hd : (deloopingMap F.exact).hom =
        M.waldhausen.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun := by
      change (SSet.toTop.map (sSetMap F.exact)).hom = _
      have hs : sSetMap F.exact = M.waldhausen.smallModelSSetIso.hom := by
        ext A B : 4
        apply Subtype.ext
        change _ ⋙ F.functor = _ ⋙ AsSmall.up
        rw [hF]
      rw [hs]
      rfl
    change piMap n (deloopingMap F.exact).hom _ x =
      piMap n M.waldhausen.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun _ x
    exact DFunLike.congr_fun (piMap_congr n _ _ _ _ hd) x
  have hn := (modelKStableEquiv_naturality F n x).symm
  rw [hK] at hn
  exact hn

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Original native conversion detects the negative sign of the actual auxiliary boundary. -/
theorem boundedFlatCoefficientAuxiliaryInitialConnecting_native_sign (a : Under R) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : (boundedFlatCoefficientSupportedOpenModel f T a).waldhausen.K (n + 1)) :
    let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a (n : ℤ)
    (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap (auxiliaryNativeFiberAcyclicModelMap f T a))
        (stableFiberLiftConnecting
          ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
          ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
          ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a) (n : ℤ)
          (eqToHom (congrArg (stableHomotopyGroup
            ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)) κ)
            (modelKStableEquiv (boundedFlatCoefficientSupportedOpenModel f T a) (n + 1)
              (Additive.ofMul x)))) =
      -(originalKStableEquiv (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)) n
        (Additive.ofMul (changeWeakConnectingHom (boundedFlatCoefficientSupportedOpenNested f T a)
          (boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence f T a) n
          x))) := by
  let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a (n : ℤ)
  let := boundedFlatCoefficientAuxiliaryNativeFiberLift_isStableEquivalence f T a (n : ℤ)
  have he := ConcreteCategory.congr_hom
    (boundedFlatCoefficientAuxiliaryInitialConnecting_native f T a (n : ℤ))
    (eqToHom (congrArg (stableHomotopyGroup
      ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)) κ)
      (modelKStableEquiv (boundedFlatCoefficientSupportedOpenModel f T a) (n + 1)
        (Additive.ofMul x)))
  have hc := ConcreteCategory.congr_hom
    (stableMap_degree_cast (prespectrumMap (auxiliaryNativeCoarseModelMap f T a)) κ)
    (modelKStableEquiv (boundedFlatCoefficientSupportedOpenModel f T a) (n + 1) (Additive.ofMul x))
  have hk := boundedFlatCoefficientNativeSmallModelMap_stable
    (boundedFlatCoefficientSupportedOpenModel f T a)
    (auxiliaryNativeCoarseModelMap f T a) rfl (n + 1) x
  have ht := hc.trans (congrArg
    (eqToHom (congrArg (stableHomotopyGroup
      (originalPrespectrum (boundedFlatCoefficientSupportedOpenWaldhausen f T a))) κ)) hk)
  exact he.trans ((congrArg
    (stableFiberLiftConnecting
      (acyclicInclusionPrespectrumMap (boundedFlatCoefficientSupportedOpenNested f T a))
      (changeWeakPrespectrumMap (boundedFlatCoefficientSupportedOpenNested f T a))
      (acyclicPrespectrumNullhomotopy (boundedFlatCoefficientSupportedOpenNested f T a)) (n : ℤ))
    ht).trans (originalKStableEquiv_liftConnecting_sign _
      (boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence f T a) n κ
      x))

end Quillen.PerfectComplexes
