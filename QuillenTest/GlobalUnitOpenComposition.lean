/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitOpenComposition

/-! Original flat-unit composition tracks, independent times and all connective input degrees. -/
public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace QuillenTest.GlobalUnitOpenComposition
variable {U X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (i : U ⟶ X) [IsOpenImmersion i]
  (q : (Γ(X, ⊤))ˣ)

/-- The entire original categorical square precedes any induced group operation. -/
theorem original_transformation :
    Functor.whiskerRight (perfectFlatPullbackUnitIso f q).hom (perfectRestrict i) ≫
        (perfectFlatOpenCompositionIso f i).hom =
      (perfectFlatOpenCompositionIso f i).hom ≫
        (perfectFlatPullbackUnitIso (i ≫ f)
          (Units.map i.appTop.hom.toMonoidHom q)).hom :=
  perfectFlatUnitOpenCompositionTransformation f i q

/-- The initial whole comparison face retains the original restricted unit track. -/
theorem original_first_face (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (perfectWaldhausen Y)).space n) :
    (perfectFlatUnitOpenCompositionTrack f i q).level n (0, (s, x)) =
      (((perfectFlatUnitHomotopy f q).postcomp
        (exactOriginalPrespectrumMap _ _ (perfectRestrict_waldhausenExact i))).trans
          (perfectFlatOpenCompositionHomotopy f i)).level n (s, x) :=
  ((perfectFlatUnitOpenCompositionTrack f i q).level n).apply_zero (s, x)

/-- The final whole comparison face retains the actual composite flat-unit track. -/
theorem original_last_face (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (perfectWaldhausen Y)).space n) :
    (perfectFlatUnitOpenCompositionTrack f i q).level n (1, (s, x)) =
      ((perfectFlatOpenCompositionHomotopy f i).trans
        (perfectFlatUnitHomotopy (i ≫ f)
          (Units.map i.appTop.hom.toMonoidHom q))).level n (s, x) :=
  ((perfectFlatUnitOpenCompositionTrack f i q).level n).apply_one (s, x)

/-- Both complete track times fix the original basepoint at every level. -/
theorem original_basepoint (n : ℕ) (a s : unitInterval) :
    (perfectFlatUnitOpenCompositionTrack f i q).level n
        (a, (s, (originalPrespectrum (perfectWaldhausen Y)).point n)) =
      (originalPrespectrum (perfectWaldhausen U)).point n := by
  rw [((perfectFlatUnitOpenCompositionTrack f i q).level n).eq_fst a
    (Or.inr (Or.inr rfl))]
  exact (((perfectFlatUnitHomotopy f q).postcomp
    (exactOriginalPrespectrumMap _ _ (perfectRestrict_waldhausenExact i))).trans
      (perfectFlatOpenCompositionHomotopy f i)).at_point n s

/-- Comparison, unit and structure times remain independent. -/
theorem original_structure_time (n : ℕ) (a s t : unitInterval)
    (x : (originalPrespectrum (perfectWaldhausen Y)).space n) :
    (perfectFlatUnitOpenCompositionTrack f i q).level (n + 1)
        (a, (s, (originalPrespectrum (perfectWaldhausen Y)).structureMap n x t)) =
      (originalPrespectrum (perfectWaldhausen U)).structureMap n
        ((perfectFlatUnitOpenCompositionTrack f i q).level n (a, (s, x))) t :=
  (perfectFlatUnitOpenCompositionTrack f i q).comm n a s x t

private theorem model_input_loop_time {V W : Model.{u}}
    {g h : prespectrum V ⟶ prespectrum W} {H K : Homotopy g h}
    (J : H.RelHomotopy K) (a s l : unitInterval)
    (x : Path (stagePoint 0 V) (stagePoint 0 V)) :
    J.level 1 (a, (s, x l)) =
      (show Path (stagePoint 0 W) (stagePoint 0 W) from J.level 0 (a, (s, x))) l :=
  J.comm 0 a s x l

/-- The level-zero input loop coordinate is independent of both comparison times. -/
theorem original_input_loop_time (a s l : unitInterval)
    (x : Path (stagePoint 0 (modelOf (perfectWaldhausen Y)))
      (stagePoint 0 (modelOf (perfectWaldhausen Y)))) :
    (perfectFlatUnitOpenCompositionTrack f i q).level 1 (a, (s, x l)) =
      (show Path (stagePoint 0 (modelOf (perfectWaldhausen U)))
        (stagePoint 0 (modelOf (perfectWaldhausen U))) from
          (perfectFlatUnitOpenCompositionTrack f i q).level 0 (a, (s, x))) l :=
  model_input_loop_time (V := modelOf (perfectWaldhausen Y))
    (W := modelOf (perfectWaldhausen U)) (perfectFlatUnitOpenCompositionTrack f i q) a s l x

/-- The exact original homomorphisms agree in every connective degree. -/
theorem original_homomorphism (n : ℕ) :
    (perfectKRestrict i (n + 1)).comp
        (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
          (perfectFlatUnitHomotopy f q) n) =
      originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy (i ≫ f) (Units.map i.appTop.hom.toMonoidHom q)) n :=
  perfectFlatUnitHomotopy_originalKOperation_restrict_comp f i q n

/-- An arbitrary original K-zero class retains the complete forward unit operation. -/
theorem original_k_zero (a : PerfectK Y 0) :
    perfectKRestrict i 1
        (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
          (perfectFlatUnitHomotopy f q) 0 a) =
      originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy (i ≫ f) (Units.map i.appTop.hom.toMonoidHom q)) 0 a :=
  perfectFlatUnitHomotopy_originalKOperation_restrict_comp_apply f i q 0 a

end QuillenTest.GlobalUnitOpenComposition
