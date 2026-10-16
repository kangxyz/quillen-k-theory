/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIsoNaturality
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphism

/-!
# The original pointwise identity action on an exact Model map

The original target identity automorphism acts on a Model map by its actual whiskering.
Its entire realized homotopy is the original target identity-action homotopy precomposed with
that unchanged map. The formula retains degree zero and the homotopy parameter literally.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} (F : V ⟶ W) (e : 𝟭 W ≅ 𝟭 W)

/-- Pointwise scalar action is the unchanged original target track after the actual Model map. -/
theorem prespectrumIsoHomotopy_onFunctor_level (n : ℕ) :
    (prespectrumIsoHomotopy F (Quillen.FunctorIdentityAutomorphism.onFunctor F.functor e)).level n =
      ((prespectrumIsoHomotopy (𝟙 W) e).precomp (prespectrumMap F)).level n :=
  prespectrumTransformationHomotopy_precomp_level
    (F := 𝟙 W) (G := 𝟙 W) e.hom (fun _ => W.waldhausen.weq_iso _ inferInstance) F n

/-- Every original time value, including degree zero, uses the exact original coefficient map. -/
theorem prespectrumIsoHomotopy_onFunctor_apply (n : ℕ) (t : unitInterval)
    (x : (prespectrum V).space n) :
    (prespectrumIsoHomotopy F (Quillen.FunctorIdentityAutomorphism.onFunctor F.functor e)).level n
        (t, x) =
      (prespectrumIsoHomotopy (𝟙 W) e).level n (t, (prespectrumMap F).map n x) :=
  congrArg (fun k => k (t, x)) (prespectrumIsoHomotopy_onFunctor_level F e n)

end Quillen.Waldhausen.IteratedS
