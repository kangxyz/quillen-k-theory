/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.SimplexBoundaryProducts
public import Quillen.Topology.LocalCoefficients.RelativeFunctoriality

/-!
# Original twisted comparison for the geometric simplex boundary pair

The actual absolute simplex-product comparison and boundary-product comparison
induce a quasi-isomorphism of the original relative cokernel map. No shifted
homology identification or Künneth comparison is assumed.
-/

@[expose] public section
noncomputable section
open CategoryTheory Convexity
universe u
namespace Quillen.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Original products with a geometric simplex boundary pair preserve abelian-system
homology comparison, with arbitrary possibly nonconstant target coefficients. -/
theorem prodMap_id_simplexRelative_quasiIso (f : C(X, Y))
    (hf : ∀ (A : System.{u, u} Y), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap f A)) (n : ℕ)
    (A : System.{u, u} (Y × StdSimplex ℝ (Fin (n + 1)))) (hA : AbelianMonodromy A) :
    QuasiIso (relativePushforwardChainMap
      (f.prodMap (ContinuousMap.id (StdSimplex ℝ (Fin (n + 1)))))
      {z : X × StdSimplex ℝ (Fin (n + 1)) | z.2 ∈ simplexBoundary n}
      {z : Y × StdSimplex ℝ (Fin (n + 1)) | z.2 ∈ simplexBoundary n}
      (fun _ hx ↦ hx) A) := by
  apply relativePushforwardChainMap_quasiIso
  · exact prodMap_id_simplex_quasiIso f hf n A hA
  · exact subspacePushforwardChainMap_prodMap_id_quasiIso f (simplexBoundary n)
      (prodMap_id_simplexBoundary_quasiIso f hf n) A hA

end Quillen.LocalCoefficients
