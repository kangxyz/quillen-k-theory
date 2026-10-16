/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.Algebra.Homology.CochainComplex.DegreewiseSplitMono

/-!
# Degreewise split monomorphisms under open restriction

The original degreewise splittings are carried by the actual module restriction functor.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Open restriction preserves the degreewise splittings themselves. -/
theorem degreewiseSplitMono_restrict {K L : CochainComplex X.Modules ℤ} {f : K ⟶ L}
    (hf : CochainComplex.degreewiseSplitMono f) :
    CochainComplex.degreewiseSplitMono ((restrict j).map f) := by
  intro n
  let : IsSplitMono (f.f n) := hf n
  change IsSplitMono ((Scheme.Modules.restrictFunctor j).map (f.f n))
  infer_instance

end Quillen.PerfectComplexes

end

end
