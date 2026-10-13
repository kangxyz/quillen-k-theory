/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.CofiberObjectChangeWeak
public import Quillen.Waldhausen.GrothendieckComparison.ObjectNaturality
public import Quillen.Waldhausen.SConstruction.Rows.CofiberTwoComparison
public import Quillen.Topology.HomotopyGroups.Loop.LeftComponentTranslation

/-!
# Component translation using the actual identity-cofiber triangle

The suffix path is the original identity-cofiber triangle, with its literal chosen-zero
quotient. Its localization keeps every original comparison and loop coordinate. The resulting
component equivalence is explicitly matched to that prism face; no equality with the standard
suffix-removal path or final Laurent boundary normalization is asserted here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open Quillen.Waldhausen.QuotientRows
open scoped Topology Simplicial
universe u v
namespace Quillen.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (W : Structure C) (A : C)

/-- The original identity-cofiber triangle removes the literal chosen-zero suffix. -/
def identityCofiberSuffixPath :
    Path ((W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint)) (W.kZeroObjectLoop A) where
  toFun s := {
    toFun t := W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
      (cofiberTwo_identity_square W) (s, t)
    continuous_toFun := by fun_prop
    source' := Path.Homotopy.source _ s
    target' := Path.Homotopy.target _ s }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
      (cofiberTwo_identity_square W)).continuous
  source' := by
    ext t
    change W.cofiberObjectLoopTrack _ _ _ _ (0, t) = _
    rw [ContinuousMap.HomotopyWith.apply_zero]
    change ((W.kZeroObjectLoop A).trans (W.kZeroObjectLoop W.zero)) t = _
    rw [W.kZeroObjectLoop_zero]
  target' := by
    ext t
    exact (W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
      (cofiberTwo_identity_square W)).apply_one t

/-- Both original triangle comparison and object-loop coordinates remain unchanged. -/
theorem identityCofiberSuffixPath_apply (s t : unitInterval) :
    W.identityCofiberSuffixPath A s t =
      W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
        (cofiberTwo_identity_square W) (s, t) := rfl

/-- Left prefix followed by the actual identity triangle gives the prism-matched equivalence. -/
def identityCofiberComponentEquiv (n : ℕ) :
    HomotopyGroup.Pi n (Path W.kBasepoint W.kBasepoint) (Path.refl W.kBasepoint) ≃
      HomotopyGroup.Pi n (Path W.kBasepoint W.kBasepoint) (W.kZeroObjectLoop A) :=
  (loopLeftTranslationHomotopyEquiv (W.kZeroObjectLoop A) n).trans
    (pathTransport (W.identityCofiberSuffixPath A) n)

end Quillen.Waldhausen.Structure
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {V : Structure C} (N : NestedWeakEquivalences V) (A : C)

/-- The entire identity triangle retains its actual grid whenever the chosen zeros agree. -/
theorem identityCofiberSimplex_val_of_zero_eq (W : Structure C) (h0 : V.zero = W.zero) :
    (V.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ V.zero) (V.cof.id_mem A)
        (cofiberTwo_identity_square V)).val =
      (W.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
        (cofiberTwo_identity_square W)).val := by
  cases V
  cases W
  cases h0
  rfl

/-- Localization retains the whole specified identity-triangle suffix path. -/
theorem identityCofiberSuffixPath_changeWeak (s t : unitInterval) :
    changeWeakMap N (V.identityCofiberSuffixPath A s t) =
      N.coarse.identityCofiberSuffixPath A s t := by
  have he : (sSetMap (changeWeak_exact N)).app (Opposite.op ⦋2⦌)
      (V.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ V.zero) (V.cof.id_mem A)
        (cofiberTwo_identity_square V)) =
      N.coarse.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ N.coarse.zero)
        (N.coarse.cof.id_mem A) (cofiberTwo_identity_square N.coarse) := by
    apply Subtype.ext
    change _ ⋙ 𝟭 C = _
    rw [Functor.comp_id]
    exact identityCofiberSimplex_val_of_zero_eq A N.coarse N.zero_eq.symm
  rw [Structure.identityCofiberSuffixPath_apply, Structure.identityCofiberSuffixPath_apply,
    Structure.cofiberObjectLoopTrack_apply, Structure.cofiberObjectLoopTrack_apply,
    realizationEdgeCompositionHomotopy_apply, realizationEdgeCompositionHomotopy_apply]
  change (SSet.toTop.map (SSet.yonedaEquiv.symm
    (V.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ V.zero) (V.cof.id_mem A)
      (cofiberTwo_identity_square V))) ≫ SSet.toTop.map (sSetMap (changeWeak_exact N))) _ = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp, he]
  rfl

/-- The prism-matched component equivalence is natural for the original localization map. -/
theorem identityCofiberComponentEquiv_naturality (n : ℕ)
    (a : HomotopyGroup.Pi n (Path V.kBasepoint V.kBasepoint) (Path.refl V.kBasepoint)) :
    N.coarse.identityCofiberComponentEquiv A n
        (homotopyGroupMap (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
          (basedLoopMap_refl _ _) a) =
      homotopyGroupMap (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A)
        (V.identityCofiberComponentEquiv A n a) := by
  let g := basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)
  have hA : g (V.kZeroObjectLoop A) = N.coarse.kZeroObjectLoop A :=
    deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A
  have ht : g ((V.kZeroObjectLoop A).trans (Path.refl V.kBasepoint)) =
      (N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint) := by
    rw [basedLoopMap_trans, basedLoopMap_refl, hA]
  have hn : homotopyGroupMap g ht
        (loopLeftTranslationHomotopyEquiv (V.kZeroObjectLoop A) n a) =
      loopLeftTranslationHomotopyEquiv (N.coarse.kZeroObjectLoop A) n
        (homotopyGroupMap g (basedLoopMap_refl _ _) a) := by
    induction a using Quotient.inductionOn with
    | h p =>
      change Quotient.mk' (genLoopPostcomp g ht
        (genLoopPostcomp (loopLeftTranslationEquiv (V.kZeroObjectLoop A)).toFun _ p)) =
          Quotient.mk' (genLoopPostcomp (loopLeftTranslationEquiv
            (N.coarse.kZeroObjectLoop A)).toFun _ (genLoopPostcomp g _ p))
      apply congrArg Quotient.mk'
      ext s t
      change g (loopLeftTranslationEquiv (V.kZeroObjectLoop A) (p s)) t =
        loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A) (g (p s)) t
      rw [loopLeftTranslationEquiv_apply, loopLeftTranslationEquiv_apply,
        basedLoopMap_trans, hA]
  change pathTransport (N.coarse.identityCofiberSuffixPath A) n
    (loopLeftTranslationHomotopyEquiv (N.coarse.kZeroObjectLoop A) n
      (homotopyGroupMap g (basedLoopMap_refl _ _) a)) = _
  rw [← hn]
  exact pathTransport_naturality_of_track g (V.identityCofiberSuffixPath A)
    (N.coarse.identityCofiberSuffixPath A) ht hA
    (fun s ↦ by ext t; exact identityCofiberSuffixPath_changeWeak N A s t)
    n (loopLeftTranslationHomotopyEquiv (V.kZeroObjectLoop A) n a)

end Quillen.Waldhausen.Fibration
