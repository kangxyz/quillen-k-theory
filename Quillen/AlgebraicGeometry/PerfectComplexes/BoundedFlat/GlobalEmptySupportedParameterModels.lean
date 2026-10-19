/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEmptySupportedModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentTrack

/-!
# Empty-open support on the original scheme-parameter Models and Laurent tracks

The actual product open source has no points because its original second
projection maps to the empty fixed factor. Componentwise support-forgetful
Model isomorphisms assemble along the original pair pullbacks. Their forward
transformation is literally `ParameterModels.forget`; both directions preserve
the original projected Laurent unit and every time of its realized track.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterModels
open GlobalSupportedParameter ParameterLaurentTrack ParameterLaurentUnit
open NaturalTrack

variable {P Q : Scheme.{u}} [IsEmpty P] (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual parameter open source is empty by its unchanged second projection. -/
theorem parameterOpen_isEmpty (X : Scheme.{u}) : IsEmpty (pair f X).obj.left :=
  Function.isEmpty (pullback.snd (toIntegerBase X) (toIntegerBase P))

/-- The original support-forgetful transformation is an isomorphism of parameter Models. -/
def emptySupportedIso : supported f ≅ ambient Q :=
  NatIso.ofComponents (fun X => by
    letI := parameterOpen_isEmpty f X.unop
    exact emptySupportedModelIso (X := op (pair f X.unop).obj.right)
      (pair f X.unop).obj.hom)
    (fun g => (forget f).naturality g)

/-- The forward transformation retains the original support-forgetful Model arrow. -/
theorem emptySupportedIso_hom : (emptySupportedIso f).hom = forget f := rfl

/-- The original Laurent unit is preserved by the forward empty-support isomorphism. -/
theorem emptySupportedIso_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves ((emptySupportedIso f).hom.app (laurent.op.obj X)).functor
      (supportedUnit f X) (ambientUnit Q X) :=
  forget_unit f X

/-- Its literal inverse preserves the same projected Laurent unit. -/
theorem emptySupportedIso_inv_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves ((emptySupportedIso f).inv.app (laurent.op.obj X)).functor
      (ambientUnit Q X) (supportedUnit f X) := by
  intro S
  apply ObjectProperty.hom_ext
  exact (map_lift_hom (parameterSupported f (laurent.op.obj X)).ι
    (ambientUnit Q X)
    (((emptySupportedIso f).inv.app (laurent.op.obj X)).functor.obj S)).symm

/-- The original whole Laurent track commutes with the forward parameter Model isomorphism. -/
theorem emptySupportedIso_equivariant :
    Equivariant (supportedTrack f) (ambientTrack Q)
      (Functor.whiskerRight (emptySupportedIso f).hom prespectrumFunctor) :=
  forget_equivariant f

/-- The literal inverse preserves every time of the same original Laurent track. -/
theorem emptySupportedIso_inv_equivariant :
    Equivariant (ambientTrack Q) (supportedTrack f)
      (Functor.whiskerRight (emptySupportedIso f).inv prespectrumFunctor) :=
  ofModelUnits_equivariant _ _ _ _ _ _ _ _ _ (emptySupportedIso_inv_unit f)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterModels
