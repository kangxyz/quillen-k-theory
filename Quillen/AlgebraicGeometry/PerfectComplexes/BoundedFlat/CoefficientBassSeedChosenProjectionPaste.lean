/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedChosenPathTransport
public import Quillen.Topology.Path.CarrierSquareDescent

/-! Paste the two original selected cubes along their proved common whole J0 path. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedChosenProjectionPaste
open CoefficientBassSeedChosenPathCube CoefficientBassSeedChosenPathTransport

/-- The exact whole-path equality identifies its source. -/
theorem sharedSource {X : Type*} [TopologicalSpace X] {o₀ m₀ o m : X}
    (T₀ : Path o₀ m₀) (T : Path o m) (h : ∀ t, T₀ t = T t) : o = o₀ :=
  T.source.symm.trans ((h 0).symm.trans T₀.source)

/-- The exact whole-path equality identifies its target. -/
theorem sharedTarget {X : Type*} [TopologicalSpace X] {o₀ m₀ o m : X}
    (T₀ : Path o₀ m₀) (T : Path o m) (h : ∀ t, T₀ t = T t) : m = m₀ :=
  T.target.symm.trans ((h 1).symm.trans T₀.target)

/-- Retype only the two shared endpoints using the given full-path equality. -/
def align {X : Type*} [TopologicalSpace X] {o₀ m₀ o m a d : X}
    (T₀ : Path o₀ m₀) (T : Path o m) (h : ∀ t, T₀ t = T t)
    (D : Path o₀ a) (K : Path m₀ d) (L : Path a d)
    (J : L.Homotopy (D.symm.trans (T₀.trans K))) :
    L.Homotopy ((D.cast (sharedSource T₀ T h) rfl).symm.trans
      (T.trans (K.cast (sharedTarget T₀ T h) rfl))) :=
  J.cast rfl (by
    apply Path.ext
    funext t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · rfl
    · rw [Path.trans_apply, Path.trans_apply]
      split_ifs
      · exact h _
      · rfl)

/-- The original right inverse-edge cancellation word. -/
def closeRight {X : Type*} [TopologicalSpace X] {a b c : X}
    {H : Path a b} {A : Path a c} {B : Path b c}
    (J : H.Homotopy (A.trans B.symm)) : (H.trans B).Homotopy A := by
  have cancel : (B.symm.trans B).Homotopy (Path.refl c) := by
    simpa only [Path.symm_symm] using (Path.Homotopy.reflTransSymm B.symm).symm
  exact (J.hcomp (Path.Homotopy.refl B)).trans
    ((Path.Homotopy.transAssoc A B.symm B).trans
      (((Path.Homotopy.refl A).hcomp cancel).trans (Path.Homotopy.transRefl A)))

/-- The original boundary rotation and compact-square descent. -/
def squareOfBoundary {X : Type*} [TopologicalSpace X] {a b c d e f : X}
    {H : Path a b} {L : Path a c} {P : Path c d}
    {K : Path d f} {M : Path e f} {N : Path b e}
    (J : H.Homotopy ((L.trans (P.trans (K.trans M.symm))).trans N.symm)) :
    CarrierPathSquare.Square (H.trans N) (P.trans K) L M :=
  CarrierPathSquare.boundarySquare
    ((closeRight J).trans
      (((Path.Homotopy.refl L).hcomp (Path.Homotopy.transAssoc P K M.symm).symm).trans
        (Path.Homotopy.transAssoc L (P.trans K) M.symm).symm))

/-- Map the two-piece/three-piece comparison using only abstract concatenation laws. -/
def mapRecipe {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {a c d o m : X} (L : Path a c) (P : Path c d) (A : Path a o)
    (T : Path o m) (K : Path m d) (J : (L.trans P).Homotopy (A.trans (T.trans K)))
    (f : C(X, Y)) :
    ((L.map f.continuous).trans (P.map f.continuous)).Homotopy
      ((A.map f.continuous).symm.symm.trans
        ((T.map f.continuous).trans (K.map f.continuous))) :=
  (J.map f).cast (Path.map_trans L P f.continuous)
    (by simp only [Path.map_trans, Path.symm_symm])

/-- Reversing the reversed outer edge changes only its endpoint presentation. -/
def reverseFirst {X : Type*} [TopologicalSpace X] {a c d o m : X}
    (L : Path a c) (P : Path c d) (A : Path a o) (T : Path o m) (K : Path m d)
    (J : (L.trans P).Homotopy (A.trans (T.trans K))) :
    (L.trans P).Homotopy (A.symm.symm.trans (T.trans K)) :=
  J.cast rfl (by rw [Path.symm_symm])

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b b' c : Under R}
  (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ b') (q' : b' ⟶ c) (h : p ≫ q = p' ≫ q')

/-- The actual continuous transport of whole seed paths. -/
abbrev Φ := pathMap P p q p' q' h
/-- The transported original common J0 path. -/
abbrev T₀ :=
  (surfacePath (CoefficientBassCompositeJ0Conjugation.reverseComparison P p q).toHomotopy).map
    (Φ P p q p' q' h).continuous
/-- The second original common J0 path. -/
abbrev T :=
  surfacePath (CoefficientBassCompositeJ0Conjugation.reverseComparison P p' q').toHomotopy
/-- The reversed transported C0 edge. -/
abbrev D₀ :=
  ((surfacePath (CoefficientBassCompositeActualRightRoute.c0 P p q)).map
    (Φ P p q p' q' h).continuous).symm
/-- The transported original C1 edge. -/
abbrev K₀ :=
  (surfacePath (CoefficientBassCompositeActualRightRoute.c1 P p q)).map
    (Φ P p q p' q' h).continuous
/-- The transported original middle comparison edge. -/
abbrev L :=
  (surfacePath (CoefficientBassCompositeActualLeftRoute.middle P p q)).map
    (Φ P p q p' q' h).continuous
/-- The transported original first comparison edge. -/
abbrev M :=
  (surfacePath (CoefficientBassCompositeActualLeftRoute.first P p q)).map
    (Φ P p q p' q' h).continuous

/-- The first selected cube, mapped and endpoint-cast only to the actual shared J0 path. -/
def firstComparison :
    ((L P p q p' q' h).trans (M P p q p' q' h)).Homotopy
      (((D₀ P p q p' q' h).cast
        (sharedSource (T₀ P p q p' q' h) (T P p' q') (shared_path P p q p' q' h)) rfl).symm.trans
        ((T P p' q').trans ((K₀ P p q p' q' h).cast
          (sharedTarget (T₀ P p q p' q' h) (T P p' q') (shared_path P p q p' q' h)) rfl))) := by
  apply align (T₀ P p q p' q' h) (T P p' q') (shared_path P p q p' q' h)
  exact mapRecipe
    (surfacePath (CoefficientBassCompositeActualLeftRoute.middle P p q))
    (surfacePath (CoefficientBassCompositeActualLeftRoute.first P p q))
    (surfacePath (CoefficientBassCompositeActualRightRoute.c0 P p q))
    (surfacePath (CoefficientBassCompositeJ0Conjugation.reverseComparison P p q).toHomotopy)
    (surfacePath (CoefficientBassCompositeActualRightRoute.c1 P p q))
    (comparison P p q) (Φ P p q p' q' h)

/-- The literal projection-pasting word consumes both original cubes without reselection. -/
def boundary :=
  Path.Homotopy.pasteProjectionSquares
    (Dp := (D₀ P p q p' q' h).cast
      (sharedSource (T₀ P p q p' q' h) (T P p' q') (shared_path P p q p' q' h)) rfl)
    (Dm := (surfacePath (CoefficientBassCompositeActualRightRoute.c0 P p' q')).symm)
    (T := T P p' q')
    (Lp := L P p q p' q' h) (Pp := M P p q p' q' h)
    (Kp := (K₀ P p q p' q' h).cast
      (sharedTarget (T₀ P p q p' q' h) (T P p' q') (shared_path P p q p' q' h)) rfl)
    (Lm := surfacePath (CoefficientBassCompositeActualLeftRoute.middle P p' q'))
    (Pm := surfacePath (CoefficientBassCompositeActualLeftRoute.first P p' q'))
    (Km := surfacePath (CoefficientBassCompositeActualRightRoute.c1 P p' q'))
    (firstComparison P p q p' q' h)
    (reverseFirst
      (surfacePath (CoefficientBassCompositeActualLeftRoute.middle P p' q'))
      (surfacePath (CoefficientBassCompositeActualLeftRoute.first P p' q'))
      (surfacePath (CoefficientBassCompositeActualRightRoute.c0 P p' q'))
      (T P p' q') (surfacePath (CoefficientBassCompositeActualRightRoute.c1 P p' q'))
      (comparison P p' q'))

/-- The original boundary-pasting rotations give the actual four-sided carrier face. -/
def square := squareOfBoundary (boundary P p q p' q' h)

end Quillen.PerfectComplexes.CoefficientBassSeedChosenProjectionPaste
