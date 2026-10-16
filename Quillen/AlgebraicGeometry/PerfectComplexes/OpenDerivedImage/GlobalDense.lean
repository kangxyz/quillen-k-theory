/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.GlobalComplements


public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalDensity
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Dense
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-!
# Genuine global qcqs density in the original derived image

The global perfect-complement theorem supplies actual coproduct density for
the derived-saturated image of any original compact open immersion into a
qcqs scheme. Together with original morphism roofs this gives the standard
DenseCofiberData, including genuine extension and quotient closure in the
unchanged perfect-complex category. The complement itself uses no roof premise.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Genuine qcqs density and closure reduce cofinality precisely to original
morphism roofs; no complement or joint-data hypothesis remains. -/
theorem globalDenseData (hroof : HasDerivedRoofs j) [HasBinaryCoproducts (Perfect U)] :
    Cofinality.DenseCofiberData (perfectWaldhausen U) (objects j) where
  zero := zero_mem j
  weak f hf := by
    have : QuasiIso f.hom := hf
    exact complexObjects_iff_of_quasiIso j f.hom
  extension := extension_mem j hroof
  quotient := quotient_mem j hroof
  complement := global_complement j

end Quillen.PerfectComplexes.OpenDerivedImage
