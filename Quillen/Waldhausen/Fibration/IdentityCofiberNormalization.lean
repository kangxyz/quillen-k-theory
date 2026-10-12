/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.IdentityCofiberComponent

/-!
# Normalization of the original identity-cofiber component translation

The actual identity-cofiber triangle and the existing standard suffix-removal path give
identical maps on the first homotopy group of the loop space. This follows from the already
proved path naturality of the original component equivalences. Neither path is replaced in
its defining continuous family. Comparison with the normalized Laurent unit remains separate.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (W : Structure C) (A : C)

/-- The original identity triangle and standard suffix removal induce the same degree-one map. -/
theorem identityCofiberSuffixPath_transport_eq
    (b : HomotopyGroup.Pi 1 (Path W.kBasepoint W.kBasepoint)
      ((W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint))) :
    pathTransport (W.identityCofiberSuffixPath A) 1 b =
      pathTransport (loopRightUnitPath (W.kZeroObjectLoop A)) 1 b := by
  obtain ⟨a, rfl⟩ := (loopComponentHomotopyEquiv
    ((W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint)) 1).surjective b
  exact (loopComponentHomotopyEquiv_pathTransport
    (W.identityCofiberSuffixPath A) 1 a).trans
      (loopComponentHomotopyEquiv_pathTransport
        (loopRightUnitPath (W.kZeroObjectLoop A)) 1 a).symm

/-- The prism-matched equivalence agrees with the original standard left-component normalization.
-/
theorem identityCofiberComponentEquiv_eq :
    W.identityCofiberComponentEquiv A 1 =
      loopLeftComponentHomotopyEquiv (W.kZeroObjectLoop A) 1 := by
  apply Equiv.ext
  intro a
  exact W.identityCofiberSuffixPath_transport_eq A
    (loopLeftTranslationHomotopyEquiv (W.kZeroObjectLoop A) 1 a)

end Quillen.Waldhausen.Structure
