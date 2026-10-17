/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.SourceAndComplement

public import Quillen.AlgebraicGeometry.Scheme.Localization
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.GeneralLocalization

/-!
# Canonical closed–open G-localization

For every closed immersion into a noetherian scheme, actual closed pushforward
identifies G of the closed scheme with supported G by dévissage. The source's
noetherianity is derived from the geometric assumptions, not requested as an
extra input. All groups below are the original public scheme G-groups.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

open AlgebraicGeometry.Scheme
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Closed
variable {Z X : AlgebraicGeometry.Scheme.{u}} [IsNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- The canonical map of the original exact coherent sheaf pushforward. -/
abbrev pushforwardG (n : ℕ) : @G Z (source_locallyNoetherian i) n →* G X n := by
  letI := source_locallyNoetherian i
  exact
    AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.coherentPushforwardGMap i
    n

/-- Genuine geometric dévissage, with G of the original closed scheme. -/
abbrev supportedGEquiv (n : ℕ) :
    @G Z (source_locallyNoetherian i) n ≃* SupportedG (openMap i) n := by
  letI := source_locallyNoetherian i
  exact AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.closedSupportedGEquiv
    i n

/-- The actual transported localization boundary. -/
abbrev boundaryG (n : ℕ) :
    G (openScheme i) (n + 1) →* @G Z (source_locallyNoetherian i) n := by
  letI := source_locallyNoetherian i
  exact AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.closedConnectingHom i
    n

/-- The dévissage comparison retains the original pushforward map. -/
theorem supportedGEquiv_pushforward (n : ℕ) :
    (inclusionG (openMap i) n).comp (supportedGEquiv i n).toMonoidHom = pushforwardG i n := by
  let := source_locallyNoetherian i
  simpa only [AlgebraicGeometry.Scheme.Modules.Coherent.globalInclusionGMap_eq_smallKMap] using
    Modules.Coherent.Pushforward.ClosedImmersion.closedSupportedGEquiv_pushforward i n

/-- Exactness at G of the ambient scheme. -/
theorem pushforward_range_eq_restrict_ker (n : ℕ) :
    (pushforwardG i n).range = (restrictG (openMap i) n).ker := by
  let := source_locallyNoetherian i
  exact Modules.Coherent.Pushforward.ClosedImmersion.pushforward_range_eq_restriction_ker i n

/-- Exactness at G of the open complement. -/
theorem restrict_range_eq_boundary_ker (n : ℕ) :
    (restrictG (openMap i) (n + 1)).range = (boundaryG i n).ker := by
  let := source_locallyNoetherian i
  exact Modules.Coherent.Pushforward.ClosedImmersion.restriction_range_eq_closedConnecting_ker i n

/-- Exactness at G of the actual closed scheme. -/
theorem boundary_range_eq_pushforward_ker (n : ℕ) :
    (boundaryG i n).range = (pushforwardG i n).ker := by
  let := source_locallyNoetherian i
  exact Modules.Coherent.Pushforward.ClosedImmersion.closedConnecting_range_eq_pushforward_ker i n

/-- The connective G₀ tail is surjective. -/
theorem restrictG_zero_surjective : Function.Surjective (restrictG (openMap i) 0) := by
  let := source_locallyNoetherian i
  exact (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.closed_open_longExact
    i).2.2.2

/-- The full canonical closed–open connective sequence, including G₀. -/
theorem localization_longExact :
    (∀ n, (pushforwardG i n).range = (restrictG (openMap i) n).ker) ∧
    (∀ n, (restrictG (openMap i) (n + 1)).range = (boundaryG i n).ker) ∧
    (∀ n, (boundaryG i n).range = (pushforwardG i n).ker) ∧
    Function.Surjective (restrictG (openMap i) 0) :=
  ⟨pushforward_range_eq_restrict_ker i, restrict_range_eq_boundary_ker i,
    boundary_range_eq_pushforward_ker i, restrictG_zero_surjective i⟩
end AlgebraicGeometry.Scheme.Closed
