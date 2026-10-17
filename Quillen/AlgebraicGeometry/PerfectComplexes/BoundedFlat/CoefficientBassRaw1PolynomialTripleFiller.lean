/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleBoundary
public import Quillen.Topology.HELP.Nullhomotopic

/-! Exact extension of the actual polynomial split-triple boundary and compact native evaluation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleFiller
open CoefficientBassRaw1PolynomialTripleRoutes
open Quillen.SimplexCubeExtension
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d) (negative : Bool)
local notation "V" => modelOf (boundedFlatPerfectWaldhausen
  (space (op P, CategoryTheory.Functor.obj (polynomialUnderFunctor R) a)))
local notation "J" => BassMWholeNerve.coefficientModel P
  (CategoryTheory.NatTrans.app (chartChoice negative) d)
local notation "X" => CoefficientBassRaw1PolynomialPostcomp.carrier P p q w (chartChoice negative)

/-- Contractibility extends precisely the proved six-face boundary in this original sheet. -/
theorem exists_extension : ∃ E : C(Fin 3 → I, X),
    E.restrict (Cube.boundary (Fin 3)) =
      CoefficientBassRaw1PolynomialTripleBoundary.boundary P p q w negative := by
  let : ContractibleSpace X :=
    CoefficientBassRaw1PolynomialPostcomp.carrier_contractible P p q w (chartChoice negative)
  let b' : C(CubicalTests.boundary.{u+1} 3, X) :=
    (CoefficientBassRaw1PolynomialTripleBoundary.boundary P p q w negative).comp
      ⟨CubicalTests.boundaryULiftHomeomorph 3,
        (CubicalTests.boundaryULiftHomeomorph 3).continuous⟩
  have hb : b'.Nullhomotopic := (id_nullhomotopic X).comp_left b'
  obtain ⟨E, hE⟩ := Quillen.exists_extend_of_nullhomotopic
    (CubicalTests.boundaryInclusion 3) (CubicalTests.boundaryInclusion_hep 3) b' hb
  refine ⟨E.comp ⟨ULift.up, continuous_uliftUp⟩, ?_⟩
  ext z
  exact DFunLike.congr_fun hE ⟨⟨z.val⟩, z.property⟩

/-- One chosen extension leaves every original face point unchanged. -/
def extension : C(Fin 3 → I, X) := (exists_extension P p q w negative).choose

/-- The entire prescribed boundary is recovered literally. -/
theorem extension_restrict : (extension P p q w negative).restrict (Cube.boundary (Fin 3)) =
    CoefficientBassRaw1PolynomialTripleBoundary.boundary P p q w negative :=
  (exists_extension P p q w negative).choose_spec

/-- Each original face retains its full scalar carrier value, before evaluation. -/
theorem extension_face (a : Fin 3 × Bool) (z : face a) :
    extension P p q w negative z.val.val =
      CoefficientBassRaw1PolynomialTripleBoundary.faces P p q w negative a z := by
  exact (DFunLike.congr_fun (extension_restrict P p q w negative) z.val).trans
    (glueClosedCover_apply face isClosed_face faces_cover
      (CoefficientBassRaw1PolynomialTripleBoundary.faces P p q w negative)
      (edgeCompatible_pairwise _
        (CoefficientBassRaw1PolynomialTripleBoundary.compatible P p q w negative)) a z)

/-- Compact evaluation retains arbitrary genuine polynomial input in every native degree. -/
def nativeFamily (n : ℕ) :=
  CoefficientBassRaw1PolynomialPostcomp.compactFamily P p q w (chartChoice negative)
    (extension P p q w negative) n

/-- Exact whole-face recovery commutes with compact native evaluation. -/
theorem nativeFamily_face (n : ℕ) (a : Fin 3 × Bool) (z : face a)
    (x : (prespectrum V).space n) :
    nativeFamily P p q w negative n (z.val.val, x) =
      CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w (chartChoice negative) n
        (CoefficientBassRaw1PolynomialTripleBoundary.faces P p q w negative a z) x :=
  congrArg (fun y ↦ CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w
    (chartChoice negative) n y x) (extension_face P p q w negative a z)

/-- Every scalar point preserves the original based native input. -/
theorem nativeFamily_point (n : ℕ) (z : Fin 3 → I) :
    nativeFamily P p q w negative n (z, (prespectrum V).point n) =
      (CommonReferenceNerve.CutOpenCarrier.nativeCone J).point n :=
  CoefficientBassRaw1PolynomialPostcomp.evaluate_point P p q w (chartChoice negative)
    n (extension P p q w negative z)

/-- The structure time stays independent of all three coherence coordinates. -/
theorem nativeFamily_structure (n : ℕ) (z : Fin 3 → I)
    (x : (prespectrum V).space n) (t : I) :
    nativeFamily P p q w negative (n + 1) (z, (prespectrum V).structureMap n x t) =
      (CommonReferenceNerve.CutOpenCarrier.nativeCone J).structureMap n
        (nativeFamily P p q w negative n (z, x)) t :=
  CoefficientBassRaw1PolynomialPostcomp.evaluate_structure P p q w (chartChoice negative)
    n (extension P p q w negative z) x t

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleFiller
