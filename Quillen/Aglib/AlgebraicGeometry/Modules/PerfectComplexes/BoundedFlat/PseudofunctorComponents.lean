/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Pseudofunctor

/-! # Actual geometric components of the bounded-flat pullback pseudofunctor

These projections expose the original pullback functor and its original composition
isomorphism without expanding the pseudofunctor coherence proofs in consumers.
The intended upstream owner is
`Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PseudofunctorComponents`.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- The original scheme pseudofunctor uses the actual geometric pullback. -/
theorem boundedFlatPerfectPseudofunctor_map_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatPerfectPseudofunctor.map f.op.toLoc).toFunctor =
      boundedFlatPerfectPullback f := rfl

/-- Its original composition comparison is exactly the geometric pullback comparison. -/
theorem boundedFlatPerfectPseudofunctor_mapComp_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Cat.Hom.toNatIso (boundedFlatPerfectPseudofunctor.mapComp g.op.toLoc f.op.toLoc) =
      boundedFlatPerfectPullbackCompIso f g := rfl

end Quillen.PerfectComplexes
