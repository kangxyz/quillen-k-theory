/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.SubobjectExtension
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.AffineSectionsGlobal

/-!
# Fullness of actual coherent restriction from the support quotient

The quasicoherence of open pushforward is proved by finite denominator
clearing and actual open base change. The preimage-kernel construction and
graph fractions therefore give unconditional fullness on locally noetherian
schemes. Essential surjectivity still requires coherent object extension.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.CoherentScheme


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Every coherent subsheaf on the open extends inside its given coherent
ambient sheaf by the actual quasicoherent preimage kernel. -/
theorem coherent_subobject_extension (H : FiniteTypeSheaves X) (A : FiniteTypeSheaves U)
    (i : A ⟶ (finiteTypeSheavesRestriction j).obj H) [Mono i] :
    ∃ (H' : FiniteTypeSheaves X) (s : H' ⟶ H), Mono s ∧
      ∃ (e : (finiteTypeSheavesRestriction j).obj H' ≅ A),
        (finiteTypeSheavesRestriction j).map s = e.hom ≫ i := by
  have : (cokernel i.hom).IsQuasicoherent := quasicoherent_cokernel i.hom
  have : ((Scheme.Modules.pushforward j).obj (cokernel i.hom)).IsQuasicoherent :=
    quasicoherent_pushforward_open_of_locallyNoetherian j _
  exact affineLocallyFiniteType_subobject_extension_of_quasicoherent_pushforward j H A i

/-- Actual coherent open morphisms admit supported-Serre fractions on the
ambient locally noetherian scheme. -/
theorem coherent_exists_fraction {M N : FiniteTypeSheaves X}
    (φ : (finiteTypeSheavesRestriction j).obj M ⟶ (finiteTypeSheavesRestriction j).obj N) :
    ∃ (M' : FiniteTypeSheaves X) (s : M' ⟶ M) (g : M' ⟶ N),
      (finiteTypeSheavesSupportedAway j).isoModSerre s ∧
        (finiteTypeSheavesRestriction j).map s ≫ φ = (finiteTypeSheavesRestriction j).map g := by
  apply coherent_fraction_of_subobject_extension j
  intro H A i hi
  have : Mono i := hi
  exact coherent_subobject_extension j H A i

/-- The canonical functor from the actual support quotient is full.
Faithfulness and exactness were already proved in `Quotient`. -/
instance quotientCoherentRestriction_full : (quotientCoherentRestriction j).Full := by
  apply quotientCoherentRestriction_full_of_quasicoherent_pushforward j
  intro M hM
  have : M.IsQuasicoherent := hM
  exact quasicoherent_pushforward_open_of_locallyNoetherian j M

end AlgebraicGeometry.Scheme.Modules.Coherent
