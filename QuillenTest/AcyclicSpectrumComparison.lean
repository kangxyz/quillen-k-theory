/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Fibration.SpectrumComparison

/-! Original level-one fiber paths, explicit K0 control of negative-one, and
all-integer stable fibration with independent category universes. -/
@[expose] public section


noncomputable section
open CategoryTheory
open Quillen Quillen.LoopPrespectrum Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.Waldhausen.Fibration
universe u v
namespace QuillenTest.AcyclicSpectrumComparison

open Quillen
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The comparison retains the original full path under the displayed homeomorphism. -/
theorem transported_whole_path (x : (acyclicStructure N).Delooping) (t : unitInterval) :
    ((canonicalFiberPrespectrumMap N).map 1
      ((acyclicStructure N).smallModelDeloopingHomeomorph x)).1.2 t =
      N.coarse.smallModelDeloopingHomeomorph (acyclicNullhomotopy N (t,x)) :=
  acyclicPrespectrumNullhomotopy_level_one N t x

/-- A stable class in the actual K0 target has an original source-spectrum lift. -/
theorem original_stable_zero_lift (h : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (y : stableHomotopyGroup (originalPrespectrum N.coarse) 0) :
    ∃ x, (stableHomotopyFunctor 0).map (changeWeakPrespectrumMap N) x = y :=
  changeWeakPrespectrumMap_zero_surjective N h y

/-- The actual negative-one fiber group vanishes by the proved K0 surjectivity. -/
theorem original_negative_one_fiber_zero (h : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (a : stableHomotopyGroup (homotopyFiber (changeWeakPrespectrumMap N)) (-1)) : a = 0 :=
  (changeWeakPrespectrumFiber_neg_subsingleton N h (-1) (by decide)).elim _ _

/-- The original coherent comparison is bijective in every stable integer degree. -/
theorem original_all_integer_comparison (h : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (d : ℤ) : Function.Bijective ((stableHomotopyFunctor d).map (canonicalFiberPrespectrumMap N)) :=
  (ConcreteCategory.isIso_iff_bijective _).mp
    (canonicalFiberPrespectrumMap_isStableEquivalence_of_weak N h d)

/-- Structural cylinder/extension data proves the whole original spectrum theorem. -/
theorem original_structural_spectrum_fibration [N.coarse.weq.HasTwoOutOfThreeProperty]
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D) :
    IsStableEquivalence (canonicalFiberPrespectrumMap N) :=
  canonicalFiberPrespectrumMap_isStableEquivalence_general N he D hs

/-- Degree-zero stable comparison keeps the original level-one fundamental-group map. -/
theorem level_one_degree_zero_naturality {E F : LoopPrespectrum.{u}}
    (hE : E.IsOmega) (hF : F.IsOmega) (f : E ⟶ F)
    (a : HomotopyGroup.Pi 1 (E.space 1) (E.point 1)) :
    levelOneStableEquiv F hF 0 (Additive.ofMul (piMap 0 (f.map 1) (f.map_point 1) a)) =
      (stableHomotopyFunctor ((0 : ℕ) : ℤ)).map f
        (levelOneStableEquiv E hE 0 (Additive.ofMul a)) :=
  levelOneStableEquiv_naturality hE hF f 0 a

end QuillenTest.AcyclicSpectrumComparison
