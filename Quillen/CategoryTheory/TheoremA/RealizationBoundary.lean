import Quillen.CategoryTheory.TheoremA.RealizationHEP
import Quillen.Topology.Realization.SimplexBoundaryHEP

/-!
# Simplex-boundary cofibrations for realization skeleta

The explicit simplex-cylinder retraction supplies HEP for
`X × ∂Δ[n] ⟶ X × Δ[n]`, with arbitrary parameter space `X`.
Consequently every topological pushout attaching such a parametrized simplex
has a canonical cofibration inclusion.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory Convexity
open scoped Topology unitInterval

universe u

namespace Quillen.TheoremA

/-- The actual inclusion of a parametrized simplex boundary. -/
def parameterizedSimplexBoundaryInclusion (X : TopCat.{u}) (n : ℕ) :
    TopCat.of (X × simplexBoundary n) ⟶
      TopCat.of (X × StdSimplex ℝ (Fin (n + 1))) :=
  TopCat.ofHom ⟨fun p ↦ (p.1, p.2.1), continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)⟩

/-- A parametrized simplex-boundary inclusion has the actual homotopy
extension property, including the zero-dimensional empty-boundary case. -/
theorem homotopyExtensionProperty_simplexBoundary (X : TopCat.{u}) (n : ℕ) :
    homotopyExtensionProperty (parameterizedSimplexBoundaryInclusion X n) := by
  apply homotopyExtensionProperty_of_continuous
  intro Z f H hzero
  let H' : C((X × simplexBoundary n) × unitInterval, Z) :=
    H.comp ContinuousMap.prodSwap
  have hzero' : ∀ x b, H' ((x, b), 0) = f (x, b.1) := fun x b ↦ hzero (x, b)
  obtain ⟨K, hK₀, hK⟩ := simplexBoundary_homotopy_extension n f H' hzero'
  refine ⟨K.comp ContinuousMap.prodSwap, ?_, ?_⟩
  · rintro ⟨x, b⟩
    exact hK₀ x b
  · rintro t ⟨x, b⟩
    exact hK x b t

/-- Attaching a parametrized topological simplex along its actual boundary
produces a map with HEP. -/
theorem homotopyExtensionProperty_simplexAttachment
    (X : TopCat.{u}) (n : ℕ) {C D : TopCat.{u}}
    {f : TopCat.of (X × simplexBoundary n) ⟶ C}
    {g : TopCat.of (X × StdSimplex ℝ (Fin (n + 1))) ⟶ D}
    {j : C ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion X n) f g j) :
    homotopyExtensionProperty j :=
  homotopyExtensionProperty_pushout sq (homotopyExtensionProperty_simplexBoundary X n)

end Quillen.TheoremA
