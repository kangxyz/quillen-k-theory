/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSplitExact

/-!
# Additive preservation of the original positive Bass middle row

The original common corner has its actual zero-evaluation retraction, and the actual descended
chart difference has its retraction from the literal inverse-unit splitting. Thus every additive
endofunctor of coefficient rows preserves this specific middle exactness. In particular this
applies to any composite of the original Bass contraction, without a right-exactness shortcut
or an assumed epimorphic chart difference. Polynomial/Laurent interchange is a separate step.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
variable [QuasiSeparatedSpace P.left]

/-- Every additive endofunctor preserves the actual positive-degree Bass middle row,
because both adjacent original short rows have constructed natural splittings. -/
theorem boundedFlatCoefficientMiddleSequence_map_exact (n : ℕ)
    (G : (Under R ⥤ AddCommGrpCat.{u + 1}) ⥤ (Under R ⥤ AddCommGrpCat.{u + 1}))
    [G.Additive] : ((boundedFlatCoefficientMiddleSequence P (n + 1)).map G).Exact := by
  let : Mono (G.map (boundedFlatCoefficientDifferenceDesc P (n + 1))) :=
    ((boundedFlatCoefficientBoundarySplitting P n).map G).mono_f
  let φ : (boundedFlatCoefficientCornerSequence P (n + 1)).map G ⟶
      (boundedFlatCoefficientMiddleSequence P (n + 1)).map G :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := G.map (boundedFlatCoefficientDifferenceDesc P (n + 1))
      comm₁₂ := by
        simp only [Category.id_comp, Category.comp_id]
        rfl
      comm₂₃ := by
        symm
        change G.map (cokernel.π (boundedFlatCoefficientCorner P (n + 1))) ≫
          G.map (boundedFlatCoefficientDifferenceDesc P (n + 1)) =
            𝟙 _ ≫ G.map (boundedFlatCoefficientDifference P (n + 1))
        rw [← G.map_comp, boundedFlatCoefficientDifferenceDesc_π, Category.id_comp] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp
    ((boundedFlatCoefficientCornerSplitting P (n + 1)).map G).exact

/-- Original Bass contraction preserves the actual positive middle row by its two splittings. -/
theorem boundedFlatCoefficientContractedMiddleSequence_exact (n : ℕ) :
    ((boundedFlatCoefficientMiddleSequence P (n + 1)).map
      (contractionFunctor (underToLaurent R) (underToLaurentInvert R))).Exact :=
  boundedFlatCoefficientMiddleSequence_map_exact P n
    (contractionFunctor (underToLaurent R) (underToLaurentInvert R))

end Quillen.PerfectComplexes
