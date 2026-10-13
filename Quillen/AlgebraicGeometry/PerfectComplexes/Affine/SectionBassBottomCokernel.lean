/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassBottomGroups
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassStableConnectivity
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSquareExcision
public import Quillen.KTheory.Bass.TwoChartStableCokernel
public import Quillen.KTheory.Bass.Contraction
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSuccessor

/-!
# Bottom-degree cokernels of the actual finite Bass squares

The two literal polynomial inclusions generate the bottom group of the original span.
Its actual comparison cone therefore realizes the original polynomial-difference cokernel.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes

/-- The unchanged two polynomial inclusions at the bottom degree of stage i. -/
def boundedFlatAffineSectionBassBottomSum (i : ℕ) (R : CommRingCat.{u}) :=
  biprod.desc
    ((stableHomotopyFunctor (-(i : ℤ))).map (HomotopyPushout.inl
      ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))
      ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))))
    ((stableHomotopyFunctor (-(i : ℤ))).map (HomotopyPushout.inr
      ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))
      ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))))

instance boundedFlatAffineSectionBassBottomSum_epi (i : ℕ) (R : CommRingCat.{u}) :
    Epi (boundedFlatAffineSectionBassBottomSum i R) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro z
  obtain ⟨x, y, hxy⟩ := boundedFlatAffineSectionBassSpan_bottom_generate i R z
  let P := (stableHomotopyFunctor (-(i : ℤ))).obj
    ((boundedFlatAffineSectionBassDiagram i).obj (.of (Polynomial R)))
  refine ⟨(AddCommGrpCat.biprodIsoProd P P).inv (x, y), ?_⟩
  have h := ConcreteCategory.congr_hom (AddCommGrpCat.biprodIsoProd_inv_comp_desc
    ((stableHomotopyFunctor (-(i : ℤ))).map (HomotopyPushout.inl
      ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))
      ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))))
    ((stableHomotopyFunctor (-(i : ℤ))).map (HomotopyPushout.inr
      ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))
      ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))))) (x, y)
  exact h.trans hxy

/-- The original comparison sends the two inclusions to the literal Laurent chart maps. -/
theorem boundedFlatAffineSectionBassBottomSum_comparison (i : ℕ) (R : CommRingCat.{u}) :
    boundedFlatAffineSectionBassBottomSum i R ≫ (stableHomotopyFunctor (-(i : ℤ))).map
      (StrictSquare.comparison
        ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj (laurentSquare R))) =
    biprod.desc
      ((boundedFlatAffineSectionBassBottomFunctor i).map (Quillen.Bass.plus.app R))
      ((boundedFlatAffineSectionBassBottomFunctor i).map (Quillen.Bass.minus.app R)) := by
  apply biprod.hom_ext'
  · simp only [boundedFlatAffineSectionBassBottomSum, biprod.inl_desc_assoc,
      biprod.inl_desc, ← Functor.map_comp, StrictSquare.comparison]
    rfl
  · simp only [boundedFlatAffineSectionBassBottomSum, biprod.inr_desc_assoc,
      biprod.inr_desc, ← Functor.map_comp, StrictSquare.comparison]
    rfl

/-- The original bottom-degree polynomial-difference cokernel is the actual square-cone group. -/
def boundedFlatAffineSectionBassBottomConeIso (i : ℕ) (R : CommRingCat.{u}) :
    (Quillen.Bass.contraction (boundedFlatAffineSectionBassBottomFunctor i)).obj R ≅
      (boundedFlatAffineSectionBassConeDiagram i ⋙
        stableHomotopyFunctor (-(i : ℤ))).obj R := by
  let : Subsingleton (stableHomotopyGroup (StrictSquare.span
      ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj (laurentSquare R)))
      (-(i : ℤ) - 1)) :=
    boundedFlatAffineSectionBassSpan_stable_subsingleton_of_lt
      i R (-(i : ℤ) - 1) (by omega)
  exact Quillen.Bass.chartDifferenceConeDegreeCokernelIso _
    (boundedFlatAffineSectionBass_square_coneFiber_isStableEquivalence i (laurentSquare R))
    (-(i : ℤ)) (boundedFlatAffineSectionBassBottomSum i R)
    ((boundedFlatAffineSectionBassBottomFunctor i).map (Quillen.Bass.plus.app R))
    ((boundedFlatAffineSectionBassBottomFunctor i).map (Quillen.Bass.minus.app R))
    (boundedFlatAffineSectionBassBottomSum_comparison i R)

/-- The cokernel projection is the unchanged Laurent inclusion into the actual cone. -/
@[reassoc]
theorem boundedFlatAffineSectionBassBottomConeIso_π (i : ℕ) (R : CommRingCat.{u}) :
    (Quillen.Bass.contractionπ (boundedFlatAffineSectionBassBottomFunctor i)).app R ≫
      (boundedFlatAffineSectionBassBottomConeIso i R).hom =
    (stableHomotopyFunctor (-(i : ℤ))).map (mappingConeInclusion
      (StrictSquare.comparison
        ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj (laurentSquare R)))) := by
  let : Subsingleton (stableHomotopyGroup (StrictSquare.span
      ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj (laurentSquare R)))
      (-(i : ℤ) - 1)) :=
    boundedFlatAffineSectionBassSpan_stable_subsingleton_of_lt
      i R (-(i : ℤ) - 1) (by omega)
  exact Quillen.Bass.chartDifferenceConeDegreeCokernelIso_π _
    (boundedFlatAffineSectionBass_square_coneFiber_isStableEquivalence i (laurentSquare R))
    (-(i : ℤ)) (boundedFlatAffineSectionBassBottomSum i R)
    ((boundedFlatAffineSectionBassBottomFunctor i).map (Quillen.Bass.plus.app R))
    ((boundedFlatAffineSectionBassBottomFunctor i).map (Quillen.Bass.minus.app R))
    (boundedFlatAffineSectionBassBottomSum_comparison i R)

/-- Original Laurent cone inclusions commute with the unchanged coefficient cone maps. -/
@[reassoc]
theorem boundedFlatAffineSectionBassConeDiagram_inclusion_naturality (i : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    mappingConeInclusion (StrictSquare.comparison
      ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj (laurentSquare R))) ≫
      (boundedFlatAffineSectionBassConeDiagram i).map f =
    (boundedFlatAffineSectionBassDiagram i).map (laurentMap f) ≫
      mappingConeInclusion (StrictSquare.comparison
        ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj (laurentSquare S))) := by
  apply Hom.ext
  funext n
  rfl

/-- The actual cone-cokernel identification retains all original coefficient maps. -/
@[reassoc]
theorem boundedFlatAffineSectionBassBottomConeIso_naturality (i : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (Quillen.Bass.contraction (boundedFlatAffineSectionBassBottomFunctor i)).map f ≫
      (boundedFlatAffineSectionBassBottomConeIso i S).hom =
    (boundedFlatAffineSectionBassBottomConeIso i R).hom ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((boundedFlatAffineSectionBassConeDiagram i).map f) := by
  apply (cancel_epi ((Quillen.Bass.contractionπ
    (boundedFlatAffineSectionBassBottomFunctor i)).app R)).mp
  rw [← Category.assoc, ← (Quillen.Bass.contractionπ
    (boundedFlatAffineSectionBassBottomFunctor i)).naturality f, Category.assoc,
    boundedFlatAffineSectionBassBottomConeIso_π, ← Category.assoc,
    boundedFlatAffineSectionBassBottomConeIso_π, ← Functor.map_comp]
  rw [boundedFlatAffineSectionBassConeDiagram_inclusion_naturality, Functor.map_comp]
  rfl

/-- The genuine bottom contraction is naturally the actual square-cone stable group. -/
def boundedFlatAffineSectionBassBottomConeNatIso (i : ℕ) :
    Quillen.Bass.contraction (boundedFlatAffineSectionBassBottomFunctor i) ≅
      boundedFlatAffineSectionBassConeDiagram i ⋙ stableHomotopyFunctor (-(i : ℤ)) :=
  NatIso.ofComponents (boundedFlatAffineSectionBassBottomConeIso i)
    (fun f => boundedFlatAffineSectionBassBottomConeIso_naturality i f)

end Quillen.PerfectComplexes
