/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliarySupportNull
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceWeakZeroCone

/-!
# The original localization null inside a finite normalization family

This is a Model-level primitive for the original supported localization composite. Its weak
zero-to-composite arrow, reversal, and full normalization faces are retained literally. It does
not construct a supported raw Bass successor or assert an isomorphism from zero to the composite.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputWeakZero
open GlobalSectionChangeIndex GlobalSectionChangeIndex.ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
  (X : Scheme.{u}ᵒᵖ)

/-- The unchanged support-enlargement followed by the unchanged restriction. -/
def reference := (enlargement f T).app X ≫ (restriction f T).app X

variable {k : ℕ} (N : Fin (k + 1) → CommonReferenceNerve.Node (reference f T X))

/-- The original weak zero vertex is kept outside the supplied isomorphism-reference nodes. -/
def simplex := CommonReferenceWeakZero.simplex (reference f T X) N
  (zeroToFull f T X) (zeroToFull_weak f T X)

/-- Every original null time is the actual reversed marked edge, at all native levels. -/
theorem null_native (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    prespectrumSimplexFamily (simplex f T X N) n
      ((edge (k := k + 2) 0 1).symm r, x) =
        ((fullNull f T).homotopy X).level n (r, x) :=
  (CommonReferenceWeakZero.reverse_native (reference f T X) N
    (zeroToFull f T X) (zeroToFull_weak f T X) n r x).trans
      (fullNull_level f T X n r x).symm

/-- The original finite full-reference family is retained as an entire face. -/
theorem normalization_native (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    prespectrumSimplexFamily (simplex f T X N) n
      (StdSimplex.map Fin.succ (StdSimplex.map Fin.succ z), x) =
        CommonReferenceNerve.prespectrumFamily (reference f T X) N n (z, x) :=
  CommonReferenceWeakZero.normalization_native (reference f T X) N
    (zeroToFull f T X) (zeroToFull_weak f T X) n z x

/-- A continuous finite family retains independent original null and normalization parameters. -/
def family (n : ℕ) := CommonReferenceWeakZero.coneFamily (reference f T X) N
  (zeroToFull f T X) (zeroToFull_weak f T X) n

/-- The reference slice recovers the same canonical localization null, including its clock. -/
theorem family_null (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    family f T X N n ((r, StdSimplex.single 0), x) =
      ((fullNull f T).homotopy X).level n (r, x) :=
  (CommonReferenceWeakZero.coneFamily_reference (reference f T X) N
    (zeroToFull f T X) (zeroToFull_weak f T X) n r x).trans
      (fullNull_level f T X n r x).symm

/-- The independent original structure time is unchanged in the entire finite family. -/
theorem family_structure (n : ℕ) (r : unitInterval)
    (z : StdSimplex ℝ (Fin (k + 2)))
    (x : (prespectrum ((fiber f T).obj X)).space n) (t : unitInterval) :
    family f T X N (n + 1) ((r, z), (prespectrum ((fiber f T).obj X)).structureMap n x t) =
      (prespectrum ((openModel f T).obj X)).structureMap n (family f T X N n ((r, z), x)) t :=
  CommonReferenceWeakZero.coneFamily_structure (reference f T X) N
    (zeroToFull f T X) (zeroToFull_weak f T X) n r z x t

/-- Every coefficient arrow preserves the complete original null slice at the same time. -/
theorem null_slice_naturality {Y : Scheme.{u}ᵒᵖ} (a : X ⟶ Y) {l : ℕ}
    (M : Fin (l + 1) → CommonReferenceNerve.Node (reference f T Y))
    (n : ℕ) (r : unitInterval) (x : (prespectrum ((fiber f T).obj X)).space n) :
    (prespectrumMap ((openModel f T).map a)).map n
        (family f T X N n ((r, StdSimplex.single 0), x)) =
      family f T Y M n ((r, StdSimplex.single 0),
        (prespectrumMap ((fiber f T).map a)).map n x) := by
  rw [family_null, family_null]
  exact (fullNull f T).naturality a n r x

/-- The original Laurent unit and canonical null retain both independent old times. -/
theorem null_slice_laurentInterchange {l : ℕ}
    (M : Fin (l + 1) → CommonReferenceNerve.Node
      (reference f T (AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.laurent.op.obj X)))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum ((fiber f T).obj X)).space n) :
    family f T (AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.laurent.op.obj X) M n
        ((r, StdSimplex.single 0),
          ((ParameterLaurentTrack.supportedTrack (unionOpen f T).ι).homotopy X).level n (s, x)) =
      ((ParameterLaurentTrack.supportedTrack (inverseOpen f T).ι).homotopy X).level n
        (s, family f T X N n ((r, StdSimplex.single 0), x)) := by
  rw [family_null, family_null]
  exact fullNull_laurentInterchange f T X n r s x

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputWeakZero
