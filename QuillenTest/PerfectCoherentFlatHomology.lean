/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.CoherentHomologyFlatPullback

/-! # Naturality of actual coherent homology under flat perfect pullback -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace QuillenTest.PerfectCoherentFlatHomology

open Quillen
open PerfectComplexes
variable {X Y : AlgebraicGeometry.Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [Flat f] (i : ℤ)

/-- The actual comparison is an isomorphism on unrestricted original perfect terms. -/
theorem actual_comparison_isIso (K : Perfect Y) :
    IsIso ((coherentHomologyFlatPullbackIso f i).hom.app K) := inferInstance

/-- Naturality applies to the original arbitrary perfect chain map. -/
theorem actual_chain_naturality {K L : Perfect Y} (s : K ⟶ L) :
    (perfectFlatPullback f ⋙ coherentHomology X i).map s ≫
      (coherentHomologyFlatPullbackIso f i).hom.app L =
    (coherentHomologyFlatPullbackIso f i).hom.app K ≫
      (coherentHomology Y i ⋙ AlgebraicGeometry.Scheme.Modules.Coherent.coherentPullback f).map s :=
  (coherentHomologyFlatPullbackIso f i).hom.naturality s

/-- No alternate homology map is substituted for the ambient comparison. -/
theorem actual_underlying_sheaf_map (K : Perfect Y) :
    ((coherentHomologyFlatPullbackIso f i).hom.app K).hom =
      ((K.obj.sc i).mapHomologyIso (AlgebraicGeometry.Scheme.Modules.pullback f)).hom :=
  coherentHomologyFlatPullbackIso_hom_app f i K

end QuillenTest.PerfectCoherentFlatHomology
