/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Resolution.FiniteProjectiveDimension
public import Quillen.Aglib.RingTheory.RegularLocalRing.GlobalProjectiveDimension

/-!
# Finite locally free resolutions over regular affine schemes

Every coherent sheaf on the spectrum of an arbitrary regular ring admits an actual finite locally free resolution with a bound depending on the sheaf.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- Every actual coherent sheaf on a regular affine scheme has a genuine
finite locally free admissible resolution, with an object-dependent length. -/

theorem coherentResolutionHypothesis_of_regular (R : CommRingCat.{u}) [IsRegularRing R] :
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure (Spec R)).ResolutionHypothesis
      (coherentVectorBundle (Spec R)) :=
  coherentResolutionHypothesis_of_finite_projectiveDimension R
    (fun M => AlgebraicGeometry.Scheme.Modules.Coherent.projectiveDimension_ne_top_of_regular R
      M.obj)

end AlgebraicGeometry.Scheme.Modules
