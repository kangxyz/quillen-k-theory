/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Pullback
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TensorRestriction
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.OpenCoverExactness
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LineTensor

/-! # Arbitrary coefficient tensor on an actual locally split sequence

The finite locally free quotient supplies genuine local splittings. Tensoring
those splittings and using the original tensor/restriction comparison proves
exactness for an arbitrary coefficient sheaf; it need not be flat.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.SchemeSheaf

/-- Arbitrary left coefficient tensor preserves a short exact sequence with vector-bundle quotient.
-/
theorem shortExact_tensorLeft_of_finiteLocallyFree_quotient {X : Scheme.{u}}
    (M : X.Modules) {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [IsFiniteLocallyFree X S.X₃] : (S.map (moduleTensorLeftFunctor X M)).ShortExact := by
  classical
  choose U hx hs using fun x : X => exists_local_splitting hS x
  apply shortExact_of_restrict_openCover (fun x => (U x).toScheme) (fun x => (U x).ι)
    (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
  intro x
  have : (Scheme.Modules.overEquiv (U x)).functor.Additive := by
    let := preservesBinaryBiproducts_of_preservesBinaryProducts
      (Scheme.Modules.overEquiv (U x)).functor
    exact Functor.additive_of_preservesBinaryBiproducts _
  have : (SheafOfModules.overFunctor.{u} X.ringCatSheaf (U x)).Additive :=
    overRestriction_additive (U x)
  let sU : (S.map (Scheme.Modules.restrictFunctor (U x).ι)).Splitting :=
    ((Classical.choice (hs x)).map (Scheme.Modules.overEquiv (U x)).functor).ofIso
      (S.mapNatIso (Scheme.Modules.overFunctorEquiv (U x)))
  exact ((sU.map (moduleTensorLeftFunctor (U x).toScheme (M.restrict (U x).ι))).ofIso
    (S.mapNatIso (tensorRestrictionNatIso (U x).ι M))).shortExact

/-- Original right tensor preserves the same locally split sequence for arbitrary coefficients. -/
theorem shortExact_tensorRight_of_finiteLocallyFree_quotient {X : Scheme.{u}}
    (M : X.Modules) {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [IsFiniteLocallyFree X S.X₃] :
    (S.map (Quillen.PerfectComplexes.moduleTensorByLineRight M)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (S.mapNatIso (Quillen.PerfectComplexes.moduleTensorByLineSymmetry M))
    (shortExact_tensorLeft_of_finiteLocallyFree_quotient M hS)

end Quillen.SchemeSheaf
