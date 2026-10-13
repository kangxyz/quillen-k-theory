/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumZeroNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.ZeroMap
public import Quillen.Topology.Prespectrum.DiagramNullHomotopy

/-!
# Whole reversed zero-to-image null tracks on actual Model diagrams

The supplied weak transformations start at the original chosen zero and end at the
unchanged composite Model functor. Reversing their actual prespectrum tracks gives a
null of the original composite. Strict coefficient squares and uniqueness of arrows
from the chosen zero prove naturality of the whole tracks at the same reversed time.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace Quillen.Waldhausen.IteratedS

/-- Reverse the specified original zero-to-composite transformation without changing its values. -/
def prespectrumCompositeZeroNullHomotopy {V W T : Model.{w}} (f : V ⟶ W) (g : W ⟶ T)
    (η : (zeroHom V T).functor ⟶ (f ≫ g).functor)
    (hη : ∀ S, T.waldhausen.weq (η.app S)) :
    LoopPrespectrum.Homotopy (prespectrumMap f ≫ prespectrumMap g)
      (LoopPrespectrum.zeroHom (prespectrum V) (prespectrum T)) :=
  (prespectrumTransformationHomotopy η hη).symm.cast
    (prespectrumFunctor.map_comp f g) (prespectrumMap_zeroHom V T)

/-- Endpoint casts retain exactly the original reversed transformation time and original point. -/
theorem prespectrumCompositeZeroNullHomotopy_level {V W T : Model.{w}}
    (f : V ⟶ W) (g : W ⟶ T)
    (η : (zeroHom V T).functor ⟶ (f ≫ g).functor)
    (hη : ∀ S, T.waldhausen.weq (η.app S))
    (n : ℕ) (s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumCompositeZeroNullHomotopy f g η hη).level n (s, x) =
      (prespectrumTransformationHomotopy η hη).level n (unitInterval.symm s, x) := rfl

/-- Every original strict Model square preserves the complete prescribed reversed null track. -/
theorem prespectrumCompositeZeroNullHomotopy_naturality {V W T V' W' T' : Model.{w}}
    (f : V ⟶ W) (g : W ⟶ T) (f' : V' ⟶ W') (g' : W' ⟶ T')
    (a : V ⟶ V') (c : T ⟶ T') (h : (f ≫ g) ≫ c = a ≫ (f' ≫ g'))
    (η : (zeroHom V T).functor ⟶ (f ≫ g).functor)
    (η' : (zeroHom V' T').functor ⟶ (f' ≫ g').functor)
    (hη : ∀ S, T.waldhausen.weq (η.app S))
    (hη' : ∀ S, T'.waldhausen.weq (η'.app S))
    (n : ℕ) (s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumMap c).map n
        ((prespectrumCompositeZeroNullHomotopy f g η hη).level n (s, x)) =
      (prespectrumCompositeZeroNullHomotopy f' g' η' hη').level n
        (s, (prespectrumMap a).map n x) := by
  have hn := prespectrumZeroTransformationHomotopy_naturality
    (f ≫ g) (f' ≫ g') a c h η η' hη hη' n
  exact congrArg (fun H => H (unitInterval.symm s, x)) hn

/-- Actual weak zero-to-image transformations give a whole coefficient-natural diagram null. -/
def modelDiagramZeroNull {I : Type u} [Category.{v} I]
    {C F G : I ⥤ Model.{w}} (r : C ⟶ F) (q : F ⟶ G)
    (η : ∀ a, (zeroHom (C.obj a) (G.obj a)).functor ⟶ (r.app a ≫ q.app a).functor)
    (hη : ∀ a S, (G.obj a).waldhausen.weq ((η a).app S)) :
    LoopPrespectrum.DiagramNullHomotopy
      (Functor.whiskerRight r prespectrumFunctor) (Functor.whiskerRight q prespectrumFunctor) where
  homotopy a := prespectrumCompositeZeroNullHomotopy (r.app a) (q.app a) (η a) (hη a)
  naturality {a b} f n s x := prespectrumCompositeZeroNullHomotopy_naturality
    (r.app a) (q.app a) (r.app b) (q.app b) (C.map f) (G.map f)
    ((r ≫ q).naturality f).symm (η a) (η b) (hη a) (hη b) n s x

end Quillen.Waldhausen.IteratedS
