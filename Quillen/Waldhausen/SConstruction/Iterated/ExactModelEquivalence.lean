/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopy
public import Quillen.Topology.Prespectrum.HomotopyTransport
public import Quillen.Topology.Prespectrum.StableEquivalence
public import Quillen.Topology.HomotopyGroups.WeakEquivalenceProperty

/-!
# Actual prespectrum equivalences from zero-preserving exact model equivalences

The original forward functor is retained. Its actual categorical inverse is canonically zero
normalized, and the original unit and counit supply whole coherent inverse homotopies. Every
level, including the zeroth loop level, therefore has an actual homotopy inverse.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u
namespace Quillen.Waldhausen.IteratedS.ExactModelEquivalence
variable {V W : Model.{u}} (e : V ≌ W)
  (hF : IsExact V.waldhausen.cof V.waldhausen.weq
    W.waldhausen.cof W.waldhausen.weq e.functor)
  (hG : IsExact W.waldhausen.cof W.waldhausen.weq
    V.waldhausen.cof V.waldhausen.weq e.inverse)
  (h0 : e.functor.obj V.waldhausen.zero = W.waldhausen.zero)

/-- The original strictly zero-preserving exact functor. -/
def forward : V ⟶ W := ⟨e.functor, hF, h0⟩

/-- The actual inverse functor with its canonical original chosen-zero normalization. -/
def backward : W ⟶ V :=
  ⟨Quillen.rebaseFunctor e.inverse W.waldhausen.zero V.waldhausen.zero
      ((hG.zero W.waldhausen.isZero).iso V.waldhausen.isZero),
    hG.rebase, Quillen.rebaseFunctor_obj_base _ _ _ _⟩

/-- The original categorical unit, pasted with the actual inverse normalization comparison. -/
def unitIso : (forward e hF h0 ≫ backward e hG).functor ≅ (𝟙 V : V ⟶ V).functor :=
  isoWhiskerLeft e.functor
    (Quillen.rebaseFunctorIso e.inverse W.waldhausen.zero V.waldhausen.zero
      ((hG.zero W.waldhausen.isZero).iso V.waldhausen.isZero)).symm ≪≫ e.unitIso.symm

/-- The original categorical counit, pasted with the same inverse normalization comparison. -/
def counitIso : (backward e hG ≫ forward e hF h0).functor ≅ (𝟙 W : W ⟶ W).functor :=
  isoWhiskerRight
    (Quillen.rebaseFunctorIso e.inverse W.waldhausen.zero V.waldhausen.zero
      ((hG.zero W.waldhausen.isZero).iso V.waldhausen.isZero)).symm e.functor ≪≫ e.counitIso

/-- The actual full prespectrum left inverse comparison. -/
def leftHomotopy :
    LoopPrespectrum.Homotopy
      (prespectrumMap (forward e hF h0) ≫ prespectrumMap (backward e hG))
      (𝟙 (prespectrum V)) :=
  (prespectrumTransformationHomotopy (F := forward e hF h0 ≫ backward e hG) (G := 𝟙 V)
    (unitIso e hF hG h0).hom (fun _ => V.waldhausen.weq_iso _ inferInstance)).cast
      (prespectrumFunctor.map_comp _ _) (prespectrumFunctor.map_id _)

/-- The actual full prespectrum right inverse comparison. -/
def rightHomotopy :
    LoopPrespectrum.Homotopy
      (prespectrumMap (backward e hG) ≫ prespectrumMap (forward e hF h0))
      (𝟙 (prespectrum W)) :=
  (prespectrumTransformationHomotopy (F := backward e hG ≫ forward e hF h0) (G := 𝟙 W)
    (counitIso e hF hG h0).hom (fun _ => W.waldhausen.weq_iso _ inferInstance)).cast
      (prespectrumFunctor.map_comp _ _) (prespectrumFunctor.map_id _)

/-- The unchanged original forward map has an actual homotopy inverse at every level. -/
def levelHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv ((prespectrum V).space n) ((prespectrum W).space n) where
  toFun := (prespectrumMap (forward e hF h0)).map n
  invFun := (prespectrumMap (backward e hG)).map n
  left_inv := ⟨((leftHomotopy e hF hG h0).levelHomotopy n).toHomotopy⟩
  right_inv := ⟨((rightHomotopy e hF hG h0).levelHomotopy n).toHomotopy⟩

include hG in
/-- The original map is a complete weak equivalence at every actual level. -/
theorem level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((prespectrumMap (forward e hF h0)).map n) :=
  isWeakHomotopyEquivalence_of_homotopyEquiv (levelHomotopyEquiv e hF hG h0 n)

include hG in
/-- In particular the original prespectrum map is a genuine stable equivalence. -/
theorem isStableEquivalence :
    LoopPrespectrum.IsStableEquivalence (prespectrumMap (forward e hF h0)) :=
  LoopPrespectrum.isStableEquivalence_of_levelwise _
    (level_isWeakHomotopyEquivalence e hF hG h0)

end Quillen.Waldhausen.IteratedS.ExactModelEquivalence
