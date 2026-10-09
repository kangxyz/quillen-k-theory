import Quillen.Scheme.Coherent.ClosedImmersion.GeneralPushforward

/-! # Noetherianity of the source of an actual closed immersion -/
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Quillen.CoherentScheme.ClosedImmersion.General

/-- The source hypothesis needed to form coherent G-theory is derived from
the closed immersion and local noetherianity of its ambient scheme. -/
theorem closedSource_isLocallyNoetherian {Z X : Scheme.{u}}
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] : IsLocallyNoetherian Z :=
  LocallyOfFiniteType.isLocallyNoetherian i

/-- A closed subscheme of a noetherian scheme is itself noetherian. -/
theorem closedSource_isNoetherian {Z X : Scheme.{u}}
    [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] : IsNoetherian Z := by
  let : IsLocallyNoetherian Z := closedSource_isLocallyNoetherian i
  let : CompactSpace Z := i.isClosedEmbedding.compactSpace
  exact ⟨⟩

end Quillen.CoherentScheme.ClosedImmersion.General
