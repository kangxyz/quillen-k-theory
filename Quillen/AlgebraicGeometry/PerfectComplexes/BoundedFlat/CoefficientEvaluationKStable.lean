/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionKComparison
public import Quillen.Waldhausen.SConstruction.Iterated.ModelStableHomotopy

/-!
# Original evaluation classes under actual coefficient Model maps

An exact evaluation equivalence and its literal common-universe Model arrow
preserve the existing coefficient K-equivalence and the original stable class.
No normalization of that arrow or replacement of the original classes is needed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- An actual lifted evaluation map retains the original coefficient K/stable classes. -/
theorem boundedFlatCoefficientEvaluationKEquiv_stable
    (M : Model.{u + 1}) {D : Type (u + 1)} [Category.{u} D]
    (W : Structure D) (e : M ≌ D)
    (hE : IsExact M.waldhausen.cof M.waldhausen.weq W.cof W.weq e.functor)
    (hEi : IsExact W.cof W.weq M.waldhausen.cof M.waldhausen.weq e.inverse)
    (f : M ⟶ modelOf W) (hf : f.functor = e.functor ⋙ AsSmall.up)
    (n : ℕ) (x : M.waldhausen.K n) :
    (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap f)
        (modelKStableEquiv M n (Additive.ofMul x)) =
      originalKStableEquiv W n
        (Additive.ofMul (boundedFlatCoefficientEvaluationKEquiv M.waldhausen W e hE hEi n x)) := by
  have hK : KMap f.exact n x = W.smallModelKEquiv n
      (boundedFlatCoefficientEvaluationKEquiv M.waldhausen W e hE hEi n x) := by
    change KMap f.exact n x = W.smallModelKEquiv n
      ((W.smallModelKEquiv n).symm (KMap (hE.comp W.smallModel_up_exact) n x))
    rw [MulEquiv.apply_symm_apply]
    exact DFunLike.congr_fun (KMap_eq_of_iso f.exact (hE.comp W.smallModel_up_exact)
      (eqToIso hf) n) x
  have hn := modelKStableEquiv_naturality f n x
  rw [hK] at hn
  exact hn.symm

/-- A genuine evaluation equivalence makes this same nonnegative stable map invertible. -/
theorem boundedFlatCoefficientEvaluationKEquiv_stable_isIso
    (M : Model.{u + 1}) {D : Type (u + 1)} [Category.{u} D]
    (W : Structure D) (e : M ≌ D)
    (hE : IsExact M.waldhausen.cof M.waldhausen.weq W.cof W.weq e.functor)
    (hEi : IsExact W.cof W.weq M.waldhausen.cof M.waldhausen.weq e.inverse)
    (f : M ⟶ modelOf W) (hf : f.functor = e.functor ⋙ AsSmall.up) (n : ℕ) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map (prespectrumMap f)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  let eK := (boundedFlatCoefficientEvaluationKEquiv M.waldhausen W e hE hEi n).toAdditive.trans
    (originalKStableEquiv W n)
  have he : (fun x ↦ (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap f)
      (modelKStableEquiv M n x)) = (fun x ↦ eK x) := by
    funext x
    exact boundedFlatCoefficientEvaluationKEquiv_stable M W e hE hEi f hf n x.toMul
  have hb : Function.Bijective (fun x ↦ (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap f)
      (modelKStableEquiv M n x)) := by
    rw [he]
    exact eK.bijective
  exact (Function.Bijective.of_comp_iff _ (modelKStableEquiv M n).bijective).mp hb

end Quillen.PerfectComplexes
