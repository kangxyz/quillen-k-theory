/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionModel
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SupportedSectionUnit
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIsoNaturality

/-!
# The actual supported scalar action on original coefficient prespectra

The already constructed original supported global-unit automorphism acts on the actual exact
coefficient Model map. Its value on the original chosen zero is the identity by the genuine zero
universal property. Realization retains the complete original transformation, including level
zero and every structure parameter. No new action or zero-compatibility premise is supplied.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)

/-- The original target unit acts pointwise on the unchanged supported coefficient functor. -/
def boundedFlatAffineSupportedSectionPullbackUnitIso (r : (Γ(Spec S, ⊤))ˣ) :
    (boundedFlatAffineSupportedSectionModelMap j j' f l h).functor ≅
      (boundedFlatAffineSupportedSectionModelMap j j' f l h).functor :=
  Quillen.FunctorIdentityAutomorphism.onFunctor
    (boundedFlatAffineSupportedSectionsMap j j' f l h)
    (boundedFlatAffineSupportedSectionUnitIso j' r)

/-- At the original section zero the actual scalar automorphism is the identity. -/
theorem boundedFlatAffineSupportedSectionPullbackUnitIso_zero (r : (Γ(Spec S, ⊤))ˣ) :
    (boundedFlatAffineSupportedSectionPullbackUnitIso j j' f l h r).hom.app
        (boundedFlatAffineSupportedSectionWaldhausen j).zero = 𝟙 _ :=
  ((boundedFlatAffineSupportedSectionsMap_exact j j' f l h).zero
    (boundedFlatAffineSupportedSectionWaldhausen j).isZero).eq_of_src _ _

/-- The actual supported scalar automorphism supplies the whole original prespectrum loop. -/
def boundedFlatAffineSupportedSectionUnitHomotopy (r : (Γ(Spec S, ⊤))ˣ) :
    LoopPrespectrum.Homotopy (boundedFlatAffineSupportedSectionPrespectrumMap j j' f l h)
      (boundedFlatAffineSupportedSectionPrespectrumMap j j' f l h) :=
  prespectrumIsoHomotopy (boundedFlatAffineSupportedSectionModelMap j j' f l h)
    (boundedFlatAffineSupportedSectionPullbackUnitIso j j' f l h r)

end Quillen.PerfectComplexes
