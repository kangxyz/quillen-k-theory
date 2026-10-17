/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1LaurentFamily

/-! Genuine relative comparisons on the entire original Laurent summand. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1LaurentFamily
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The plus comparison preserves the old route endpoints and every native basepoint. -/
def plusComparison :
    (Homotopy.precomp (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
      (CoefficientBassSecondConeProjectionRoutes.plusLeft P u)).RelHomotopy
    (Homotopy.precomp (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
      (CoefficientBassSecondConeProjectionRoutes.plusRight P u)) where
  level n :=
    { toFun := fun z ↦ nativeFamily P u (underToLaurent R) n ((z.1, z.2.1), z.2.2)
      continuous_toFun := (nativeFamily P u (underToLaurent R) n).continuous.comp (by fun_prop)
      map_zero_left := fun z ↦ plus_zero P u n z.1 z.2
      map_one_left := fun z ↦ plus_one P u n z.1 z.2
      prop' := by
        intro r z hz
        rcases z with ⟨s, x⟩
        rcases hz with h | h | h
        · dsimp only [Prod.fst] at h
          subst s
          exact (nativeFamily_bottom P u (underToLaurent R) n r x).trans
            (plus_zero P u n 0 x)
        · dsimp only [Prod.fst] at h
          subst s
          exact (nativeFamily_top P u (underToLaurent R) n r x).trans
            (plus_zero P u n 1 x)
        · dsimp only [Prod.snd] at h
          subst x
          exact (nativeFamily_point P u (underToLaurent R) n (r, s)).trans
            ((Homotopy.precomp
              (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
              (CoefficientBassSecondConeProjectionRoutes.plusLeft P u)).at_point n s).symm }
  comm n r s x t := nativeFamily_structure P u (underToLaurent R) n (r, s) x t

/-- The minus comparison preserves the old route endpoints and every native basepoint. -/
def minusComparison :
    (Homotopy.precomp (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
      (CoefficientBassSecondConeProjectionRoutes.minusLeft P u)).RelHomotopy
    (Homotopy.precomp (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
      (CoefficientBassSecondConeProjectionRoutes.minusRight P u)) where
  level n :=
    { toFun := fun z ↦ nativeFamily P u (underToLaurentInvert R) n ((z.1, z.2.1), z.2.2)
      continuous_toFun :=
        (nativeFamily P u (underToLaurentInvert R) n).continuous.comp (by fun_prop)
      map_zero_left := fun z ↦ minus_zero P u n z.1 z.2
      map_one_left := fun z ↦ minus_one P u n z.1 z.2
      prop' := by
        intro r z hz
        rcases z with ⟨s, x⟩
        rcases hz with h | h | h
        · dsimp only [Prod.fst] at h
          subst s
          exact (nativeFamily_bottom P u (underToLaurentInvert R) n r x).trans
            (minus_zero P u n 0 x)
        · dsimp only [Prod.fst] at h
          subst s
          exact (nativeFamily_top P u (underToLaurentInvert R) n r x).trans
            (minus_zero P u n 1 x)
        · dsimp only [Prod.snd] at h
          subst x
          exact (nativeFamily_point P u (underToLaurentInvert R) n (r, s)).trans
            ((Homotopy.precomp
              (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
              (CoefficientBassSecondConeProjectionRoutes.minusLeft P u)).at_point n s).symm }
  comm n r s x t := nativeFamily_structure P u (underToLaurentInvert R) n (r, s) x t

end Quillen.PerfectComplexes.CoefficientBassRaw1LaurentFamily
