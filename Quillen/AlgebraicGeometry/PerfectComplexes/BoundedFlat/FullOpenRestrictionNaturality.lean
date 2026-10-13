/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenRestrictionSquare
public import Quillen.CategoryTheory.Bicategory.Functor.LocallyDiscreteNaturality

/-!
# Coherent original restriction to the fixed full-open diagram

The original natural transformation of scheme inclusions is sent through the original
bounded-flat pullback pseudofunctor. The resulting strong transformation has precisely the
existing open-pair pullback comparison as its naturality isomorphism. Its two coherence laws
come from the original pseudofunctor laws, with no supplied square or pasting assumption.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Original restriction and its original pullback square form a genuine strong transformation. -/
def boundedFlatAffineFullOpenRestrictionStrongTrans :
    Pseudofunctor.StrongTrans (boundedFlatAffineFixedBasePseudofunctor (R := R))
      (boundedFlatAffineFullOpenPseudofunctor j) :=
  Quillen.CategoryTheory.PseudofunctorNaturality.strongTrans boundedFlatPerfectPseudofunctor
    (inclusionTransformation j)

/-- Each original component is literally pullback along the specified open inclusion. -/
theorem boundedFlatAffineFullOpenRestrictionStrongTrans_app (a : Under R) :
    ((boundedFlatAffineFullOpenRestrictionStrongTrans j).app ⟨a⟩).toFunctor =
      boundedFlatAffineFullOpenRestriction j a := rfl

/-- Strong naturality retains the original open-pair comparison in the exact original direction. -/
theorem boundedFlatAffineFullOpenRestrictionStrongTrans_naturality {a b : Under R}
    (f : a ⟶ b) :
    Cat.Hom.toNatIso ((boundedFlatAffineFullOpenRestrictionStrongTrans j).naturality f.toLoc) =
      boundedFlatAffineFullOpenRestrictionIso j f := by
  change Cat.Hom.toNatIso
    (Quillen.CategoryTheory.PseudofunctorNaturality.squareOfEq
      boundedFlatPerfectPseudofunctor _ _ _ _
      ((inclusionTransformation j).naturality f)) = _
  rw [Quillen.CategoryTheory.PseudofunctorNaturality.squareOfEq_toNatIso]
  rfl

end Quillen.PerfectComplexes
