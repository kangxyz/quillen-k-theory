/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.FiniteFlatPushforward
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineBoundedDerivedPushforward

/-! # Strict-perfect direct image and the original bounded-below derived unit

The comparison is the original derived unit on the original complex. Finite flatness over a
locally noetherian target supplies the previously established strict-perfect direct image.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
/-- The standard ambient derived category of module sheaves. -/
local instance strictDerivedPushforwardStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- The original strict-perfect complex as a bounded-below complex. -/
def strictToPlus (X : Scheme.{u}) : StrictPerfect X ⥤ CochainComplex.Plus X.Modules :=
  (CochainComplex.plus X.Modules).lift (strictPerfect X).ι (fun K ↦ by
    obtain ⟨a, b, h⟩ := K.property.1
    refine ⟨a, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ h i (Or.inl hi))

/-- The original strict-perfect complex in the bounded-below derived category. -/
def strictToDerivedPlus (X : Scheme.{u}) : StrictPerfect X ⥤ DerivedCategory.Plus X.Modules :=
  strictToPlus X ⋙ DerivedCategory.Plus.Q

/-- The actual affine derived unit on every strict-perfect complex is invertible. -/
theorem isIso_derivedPushforwardPlusUnit_strict {Z X : Scheme.{u}}
    (f : Z ⟶ X) [IsAffineHom f] (K : StrictPerfect Z) :
    IsIso ((AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusUnit f).app ((strictToPlus Z).obj
      K)) := by
  obtain ⟨a, b, h⟩ := K.property.1
  apply AlgebraicGeometry.Scheme.Modules.isIso_derivedPushforwardPlusUnit_of_term_bounds f _ a b
    (fun i hi ↦ h i (Or.inl hi)) (fun i hi ↦ h i (Or.inr hi))
  intro n
  let := K.property.2 n
  change (K.obj.X n).IsQuasicoherent
  infer_instance

/-- Strict finite-flat direct image computes the original bounded-below derived direct image. -/
def strictFiniteFlatDerivedPushforwardIso {Z X : Scheme.{u}}
    (f : Z ⟶ X) [IsFinite f] [Flat f] [IsLocallyNoetherian X] :
    strictFiniteFlatPushforward f ⋙ strictToDerivedPlus X ≅
      strictToDerivedPlus Z ⋙ AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlus f :=
  NatIso.ofComponents (fun K ↦ by
    let := isIso_derivedPushforwardPlusUnit_strict f K
    exact asIso ((AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusUnit f).app ((strictToPlus
      Z).obj K)))
    (by
      intro K L g
      change DerivedCategory.Plus.Q.map ((Scheme.Modules.pushforward f).mapCochainComplexPlus.map
          ((strictToPlus Z).map g)) ≫ _ = _ ≫ _
      exact (AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusUnit f).naturality
        ((strictToPlus Z).map g))

/-- The comparison's forward component is literally the original derived unit. -/
@[simp]
theorem strictFiniteFlatDerivedPushforwardIso_hom_app {Z X : Scheme.{u}}
    (f : Z ⟶ X) [IsFinite f] [Flat f] [IsLocallyNoetherian X] (K : StrictPerfect Z) :
    (strictFiniteFlatDerivedPushforwardIso f).hom.app K =
      (AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusUnit f).app ((strictToPlus Z).obj K)
        := rfl

end Quillen.PerfectComplexes
