/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerve
public import Quillen.Topology.Realization.UniverseLift

/-!
# Exact characteristic maps of common-reference nerve faces

The actual nerve parameter retains both the original model morphism and its specified reference
isomorphism at each vertex. Ordered faces with equal full nodes have equal characteristic maps.
A relabeling ordered only on a used support is applied only on that support; no global order or
ordinary-product comparison with the whole nerve is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve
variable {V W : Model.{u}} (F : V ⟶ W)

/-- The actual barycentric characteristic map of the specified full-node nerve chain. -/
def parameter {k : ℕ} (N : Fin (k + 1) → Node F) :
    C(StdSimplex ℝ (Fin (k + 1)), |nerve (Codiscrete (Node F))|) :=
  Quillen.realizationSimplex (Codiscrete.functor N)

/-- Every ordered face is its exact original nerve characteristic map. -/
theorem parameter_face {k l : ℕ} (N : Fin (k + 1) → Node F)
    (α : ⦋l⦌ ⟶ ⦋k⦌) (z : StdSimplex ℝ (Fin (l + 1))) :
    parameter F N (StdSimplex.map α.toOrderHom z) =
      parameter F (fun i ↦ N (α.toOrderHom i)) z :=
  Quillen.realizationSimplex_naturality (X := nerve (Codiscrete (Node F)))
    α (Codiscrete.functor N) z

/-- Equality of full dependent nodes identifies every point on the two ordered faces. -/
theorem parameter_eq_of_face_nodes {p q k : ℕ}
    (N : Fin (p + 1) → Node F) (M : Fin (q + 1) → Node F)
    (α : ⦋k⦌ ⟶ ⦋p⦌) (β : ⦋k⦌ ⟶ ⦋q⦌)
    (h : ∀ i, M (β.toOrderHom i) = N (α.toOrderHom i))
    (z : StdSimplex ℝ (Fin (k + 1))) :
    parameter F M (StdSimplex.map β.toOrderHom z) =
      parameter F N (StdSimplex.map α.toOrderHom z) := by
  rw [parameter_face, parameter_face, funext h]

/-- A possibly nonmonotone enclosing relabeling preserves the actual parameter on a proved
ordered support, retaining full node equality rather than only native values. -/
theorem parameter_supported {p q k : ℕ}
    (N : Fin (p + 1) → Node F) (M : Fin (q + 1) → Node F)
    (f : Fin (p + 1) → Fin (q + 1)) (hn : ∀ i, M (f i) = N i)
    (α : ⦋k⦌ ⟶ ⦋p⦌) (h : Monotone (f ∘ α.toOrderHom))
    (z : StdSimplex ℝ (Fin (k + 1))) :
    parameter F M (StdSimplex.map f (StdSimplex.map α.toOrderHom z)) =
      parameter F N (StdSimplex.map α.toOrderHom z) := by
  rw [← StdSimplex.map_comp]
  exact parameter_eq_of_face_nodes F N M α
    (SimplexCategory.Hom.mk ⟨f ∘ α.toOrderHom, h⟩)
    (fun i ↦ hn (α.toOrderHom i)) z

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve
