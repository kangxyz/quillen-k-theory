/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.ClosedGTheory

/-!
# Closed-immersion G-theory examples

Uses the public closed pushforward and open restriction for a closed immersion
into a noetherian scheme. The examples obtain noetherianity of the source,
record exactness, and identify the supported dévissage equivalence's forward
composite with the original pushforward.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace Consumer
variable {Z X : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]

include i in
/-- No independent noetherianity hypothesis on the closed source is needed. -/
theorem closed_source_noetherian : IsNoetherian Z :=
  Quillen.Scheme.Closed.source_noetherian i

/-- The actual global closed pushforward and open restriction are exact. -/
theorem global_closed_exact (n : ℕ) :
    (Quillen.Scheme.Closed.pushforwardG i n).range =
      (Quillen.Scheme.restrictG (Quillen.Scheme.Closed.openMap i) n).ker :=
  Quillen.Scheme.Closed.pushforward_range_eq_restrict_ker i n

/-- The public dévissage comparison retains exactly the closed map. -/
theorem global_closed_comparison_forward (n : ℕ) :
    (Quillen.Scheme.inclusionG (Quillen.Scheme.Closed.openMap i) n).comp
      (Quillen.Scheme.Closed.supportedGEquiv i n).toMonoidHom =
        Quillen.Scheme.Closed.pushforwardG i n :=
  Quillen.Scheme.Closed.supportedGEquiv_pushforward i n
end Consumer
