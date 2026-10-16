/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.DiagramZeroNull
public import Quillen.Waldhausen.SConstruction.Iterated.TransformationInterchange
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIdentityAction
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismEvaluation

/-!
# Identity actions on the original reversed zero null

The original whole null commutes with every pair of identity actions intertwined by its
unchanged composite Model functor. The null time and action time are independent, including
the original internal loop coordinate at level zero. The actual intertwining equation is
retained as the generic input; no scalar or Laurent comparison is assumed for a concrete model.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.Waldhausen.IteratedS

/-- A whole prespectrum homotopy intertwines the two actions at independent original times. -/
def IdentityActionInterchange {V T : Model.{u}}
    {h k : prespectrum V ⟶ prespectrum T} (N : LoopPrespectrum.Homotopy h k)
    (α : 𝟭 V ≅ 𝟭 V) (β : 𝟭 T ≅ 𝟭 T) : Prop :=
  ∀ (n : ℕ) (s t : unitInterval) (x : (prespectrum V).space n),
    N.level n (s, (prespectrumIsoHomotopy (𝟙 V) α).level n (t, x)) =
      (prespectrumIsoHomotopy (𝟙 T) β).level n (t, N.level n (s, x))

/-- The same whole null intertwines compatible identity actions at both independent times. -/
def ZeroNullUnitCompatible {V W T : Model.{u}} (f : V ⟶ W) (g : W ⟶ T)
    (N : LoopPrespectrum.Homotopy (prespectrumMap f ≫ prespectrumMap g)
      (LoopPrespectrum.zeroHom (prespectrum V) (prespectrum T))) : Prop :=
  ∀ (α : 𝟭 V ≅ 𝟭 V) (β : 𝟭 T ≅ 𝟭 T),
    FunctorIdentityAutomorphism.Preserves (f ≫ g).functor α β →
      IdentityActionInterchange N α β

/-- The canonical reversed zero-to-image track has the full identity-action interchange. -/
theorem prespectrumCompositeZeroNullHomotopy_unitCompatible {V W T : Model.{u}}
    (f : V ⟶ W) (g : W ⟶ T)
    (η : (zeroHom V T).functor ⟶ (f ≫ g).functor)
    (hη : ∀ S, T.waldhausen.weq (η.app S)) :
    ZeroNullUnitCompatible f g (prespectrumCompositeZeroNullHomotopy f g η hη) := by
  intro α β hunit n s t x
  exact prespectrumTransformationHomotopy_symm_identityAction_interchange
    (F := zeroHom V T) (G := f ≫ g) η α.hom β.hom hη
    (fun S => V.waldhausen.weq_iso _ (show IsIso (α.app S).hom from inferInstance))
    (fun S => T.waldhausen.weq_iso _ (show IsIso (β.app S).hom from inferInstance))
    (fun _ => T.waldhausen.isZero.eq_of_src _ _) hunit n s t x

end Quillen.Waldhausen.IteratedS
