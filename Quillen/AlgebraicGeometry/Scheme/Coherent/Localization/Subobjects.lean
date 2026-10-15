/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.AffineTransport
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian

/-!
# Quasicoherent subobjects of actual coherent sheaves

This is the noetherian finiteness step needed after constructing a
quasicoherent extension inside a coherent ambient sheaf. The quasicoherence
hypothesis is essential: arbitrary module-sheaf subobjects need not be
coherent.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- On a noetherian affine, a quasicoherent sheaf embedded in a coherent
sheaf is finite. Global sections preserve the monomorphism, and a submodule
of a finite module over a noetherian ring is finite. -/
theorem affineFiniteSheaf_of_mono (R : CommRingCat.{u}) [IsNoetherianRing R]
    {M N : (Spec R).Modules} (f : M ⟶ N) [Mono f] [M.IsQuasicoherent]
    (hN : affineFiniteSheaf R N) : affineFiniteSheaf R M := by
  have : Module.Finite R (moduleSpecΓFunctor.obj N) := hN.2
  have : (moduleSpecΓFunctor (R := R)).IsRightAdjoint := tilde.adjunction.isRightAdjoint
  refine ⟨inferInstance, ?_⟩
  exact Module.Finite.of_injective (moduleSpecΓFunctor.map f).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- Every quasicoherent subobject of an actual coherent sheaf on a locally
noetherian scheme is coherent. This makes no false assertion about arbitrary
subobjects in the category of all module sheaves. -/
theorem affineLocallyFiniteType_of_quasicoherent_mono {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} (f : M ⟶ N) [Mono f] [M.IsQuasicoherent]
    (hN : affineLocallyFiniteType X N) : affineLocallyFiniteType X M := by
  intro R j _
  let : IsNoetherianRing R := noetherian_affineChart R j
  exact affineFiniteSheaf_of_mono R ((Scheme.Modules.restrictFunctor j).map f) (hN R j)

end AlgebraicGeometry.Scheme.Modules.Coherent
