import Quillen.Scheme.ClosedGTheory

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
