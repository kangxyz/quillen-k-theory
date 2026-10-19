/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor

/-!
# Actual zero coefficients in degreewise tensor

The original additive sheaf tensor in its coefficient argument makes tensor by an actual zero
module an actual zero complex. Its unique zero isomorphisms form a natural isomorphism, retaining
all original tensor objects and arrows.

Intended upstream owner: `Aglib.AlgebraicGeometry.Modules.Complex.TensorZero`.
No flatness hypothesis is needed. The current consumer is the first coefficient quotient row of
the restricted tensor-unit construction on bounded-flat perfect complexes.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped ZeroObject
universe u
namespace AlgebraicGeometry.Scheme.Modules.Complex

/-- The actual tensor by any zero coefficient is zero in every original complex degree. -/
theorem tensorLeft_isZero_of_coefficient {X : Scheme.{u}} {L : X.Modules} (hL : IsZero L)
    (K : CochainComplex X.Modules ℤ) : IsZero ((tensorLeft L).obj K) := by
  rw [IsZero.iff_id_eq_zero]
  ext n : 1
  exact ((moduleTensorRightFunctor X (K.X n)).map_isZero hL).eq_of_src _ _

/-- The genuine tensor-zero objects and arrows identify naturally with the original zero complex. -/
def tensorLeftZeroIso (X : Scheme.{u}) :
    tensorLeft (0 : X.Modules) ≅ (Functor.const (CochainComplex X.Modules ℤ)).obj 0 :=
  NatIso.ofComponents
    (fun K => (tensorLeft_isZero_of_coefficient (isZero_zero _) K).iso (isZero_zero _))
    (by
      intro K L f
      exact (tensorLeft_isZero_of_coefficient (isZero_zero _) K).eq_of_src _ _)

end AlgebraicGeometry.Scheme.Modules.Complex
