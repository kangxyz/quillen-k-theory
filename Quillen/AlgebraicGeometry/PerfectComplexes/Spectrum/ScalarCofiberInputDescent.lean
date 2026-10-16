/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberFineProjectionCubePath
public import Quillen.Waldhausen.Additivity.SeparatedFirstPiSurjectivity

/-!
# Class-level descent through the actual scalar projection input

Every original K-class has a representative obtained by the actual forward separated first map
on an original subdivision cube. Consequently a property, or equality of homomorphisms, proved
on all such input classes descends to every original class. The representative hypothesis is
explicit; it does not follow from this lemma and must retain any required geometric Theta and
canonical-null comparison in its own proof.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Additivity
open scoped Simplicial Topology
universe u v
namespace Quillen.PerfectComplexes
variable (X : Scheme.{u}) (n : ℕ)

/-- The literal scalar projection input classes cover the entire original K-group. -/
theorem perfectScalarProjectionInputCube_class_surjective (a : (perfectWaldhausen X).K n) :
    ∃ p : GenLoop (Fin (n + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
      (subdivisionBasepoint (perfectWaldhausen X)),
      (⟦perfectScalarProjectionInputCube n p⟧ : (perfectWaldhausen X).K n) = a :=
  separatedFirstCube_class_surjective (perfectWaldhausen X) n a

/-- A supplied class property descends only after it is proved on every actual input cube. -/
theorem perfectScalarProjectionInputCube_forall (P : (perfectWaldhausen X).K n → Prop)
    (h : ∀ p : GenLoop (Fin (n + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
      (subdivisionBasepoint (perfectWaldhausen X)), P ⟦perfectScalarProjectionInputCube n p⟧) :
    ∀ a, P a := by
  intro a
  obtain ⟨p, hp⟩ := perfectScalarProjectionInputCube_class_surjective X n a
  rw [← hp]
  exact h p

/-- An explicit equality on all literal input classes determines the original homomorphisms. -/
theorem perfectScalarProjectionInputCube_hom_ext {G : Type v} [Monoid G]
    (f g : (perfectWaldhausen X).K n →* G)
    (h : ∀ p : GenLoop (Fin (n + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (perfectWaldhausen X))|
      (subdivisionBasepoint (perfectWaldhausen X)),
      f ⟦perfectScalarProjectionInputCube n p⟧ = g ⟦perfectScalarProjectionInputCube n p⟧) :
    f = g := by
  apply MonoidHom.ext
  exact perfectScalarProjectionInputCube_forall X n (fun a => f a = g a) h

end Quillen.PerfectComplexes
