/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.CoherentHomology
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlatPullback
public import Aglib.AlgebraicGeometry.Modules.Coherent.FlatPullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FlatPullback

/-!
# Original coherent-homology comparison for flat perfect pullback

Genuine ambient flat exactness gives a natural isomorphism between coherent
homology after actual locally-perfect pullback and actual coherent pullback
of homology. The isomorphism retains the original ambient homology comparison.
Locally noetherianity is used for the coherent targets, while no compactness
or coherence of the original complex terms is required. Homology is not exact,
so no induced perfect-to-G K-map is asserted here.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes

/-- Coherent homology commutes with actual flat pullback on the original
locally-perfect and coherent sheaf models. -/
def coherentHomologyFlatPullbackIso {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] (i : ℤ) :
    perfectFlatPullback f ⋙ coherentHomology X i ≅
      coherentHomology Y i ⋙ AlgebraicGeometry.Scheme.Modules.Coherent.coherentPullback f :=
  NatIso.ofComponents
    (fun K => (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X).isoMk
      ((K.obj.sc i).mapHomologyIso (Scheme.Modules.pullback f)))
    (fun s => by
      apply ObjectProperty.hom_ext
      exact ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor Y.Modules (ComplexShape.up ℤ) i).map s.hom)
        (Scheme.Modules.pullback f))

/-- The natural comparison has the genuine ambient homology comparison
as its underlying sheaf map, rather than an independently chosen isomorphism. -/
theorem coherentHomologyFlatPullbackIso_hom_app {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] (i : ℤ) (K : Perfect Y) :
    ((coherentHomologyFlatPullbackIso f i).hom.app K).hom =
      ((K.obj.sc i).mapHomologyIso (Scheme.Modules.pullback f)).hom := rfl

end Quillen.PerfectComplexes
