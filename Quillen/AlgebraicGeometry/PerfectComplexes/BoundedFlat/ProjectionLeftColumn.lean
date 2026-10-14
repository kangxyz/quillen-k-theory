/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleLeftColumnNodes

/-! Actual projection-rectangle source columns under the canonical reference transport. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)
  (F : modelOf (boundedFlatPerfectWaldhausen A) ⟶ modelOf (boundedFlatPerfectWaldhausen C'))
  (e : F.functor = (ProjectionReference.reference c r).functor)

def rectangleLeftIndex : Fin 3 → Fin 18 := ![2, 3, 11]

def projectionLeftNode (i : Fin 3) :=
  ModelSimplex.reanchorNodes (F₀ := F) (F₁ := ProjectionReference.reference c r) (eqToIso e)
    (ProjectionReference.nodes p q p' q' a b c hp hq r hr) (rectangleLeftIndex i)

theorem projection_left_functor (i : Fin 3) :
    (projectionLeftNode p q p' q' a b c hp hq r hr F e i).1.functor =
      (tripleLeftNode F c q p (e.trans (ProjectionReference.anchor p q c r hr)) i).1.functor := by
  fin_cases i <;> rfl

/-- The original left column is unchanged after composing its two actual equality transports. -/
theorem projection_left_triple (i : Fin 3) :
    projectionLeftNode p q p' q' a b c hp hq r hr F e i =
      tripleLeftNode F c q p (e.trans (ProjectionReference.anchor p q c r hr)) i := by
  fin_cases i <;>
    apply Sigma.ext (Model.Hom.ext (projection_left_functor p q p' q' a b c hp hq r hr F e _)) <;>
    apply heq_of_eq <;>
    change eqToIso e ≪≫ (eqToIso (ProjectionReference.anchor p q c r hr) ≪≫ _) =
      eqToIso (e.trans (ProjectionReference.anchor p q c r hr)) ≪≫ _ <;>
    rw [← Iso.trans_assoc, eqToIso_trans] <;> rfl

/-- The exact complete source column is the original binary normalization postcomposed by c. -/
theorem projection_left_column (i : Fin 3) :
    projectionLeftNode p q p' q' a b c hp hq r hr F e i =
      binaryColumnNode F c q p (e.trans (ProjectionReference.anchor p q c r hr)) i :=
  (projection_left_triple p q p' q' a b c hp hq r hr F e i).trans
    (triple_left_column F c q p _ i)

end Quillen.PerfectComplexes.BassH0Merge
