/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.SmallChainExcision

/-!
# Mayer--Vietoris for genuine local coefficients

The connecting map is constructed from the proved short exact gluing sequence
and the inverse of the original small-chain homology isomorphism. Exactness
therefore concerns the actual local-coefficient singular homology, not an
assumed homology theory or an ordinary-coefficient replacement.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

universe u v w

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {κ : Type w}
variable (U : ι → Set X) (V : κ → Set X) (A : System.{u, u} X)

/-- Sum of the original two inclusions into all ambient twisted chains. -/
def mayerVietorisAssembly : smallChainComplex U A ⊞ smallChainComplex V A ⟶
    singularChainComplex A :=
  smallChainGluingSum U V A ≫ smallChainComplexInclusion (unionCover U V) A

@[reassoc (attr := simp)]
theorem smallChainGluingDifference_assembly :
    smallChainGluingDifference U V A ≫ mayerVietorisAssembly U V A = 0 := by
  simp [mayerVietorisAssembly, ← Category.assoc]

variable (hU : ∀ i, IsOpen (U i)) (hV : ∀ j, IsOpen (V j))
  (hcover : ∀ x, (∃ i, x ∈ U i) ∨ (∃ j, x ∈ V j))

/-- Homology comparison for the original combined small-chain inclusion. -/
def unionCoverHomologyIso (n : ℕ) :
    (smallChainComplex (unionCover U V) A).homology n ≅
      (singularChainComplex A).homology n :=
  smallChainHomologyIso (unionCover U V)
    (by
      rintro (i | j)
      · exact hU i
      · exact hV j)
    (by
      intro x
      rcases hcover x with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact ⟨Sum.inl i, hi⟩
      · exact ⟨Sum.inr j, hj⟩) A n

/-- The actual twisted Mayer--Vietoris connecting homomorphism. -/
def mayerVietorisBoundary (n : ℕ) :
    (singularChainComplex A).homology (n + 1) ⟶
      (smallChainComplex (intersectionCover U V) A).homology n :=
  (unionCoverHomologyIso U V A hU hV hcover (n + 1)).inv ≫
    (smallChainGluingSequence_shortExact U V A).δ (n + 1) n rfl

@[reassoc (attr := simp)]
theorem mayerVietorisAssembly_boundary (n : ℕ) :
    HomologicalComplex.homologyMap (mayerVietorisAssembly U V A) (n + 1) ≫
      mayerVietorisBoundary U V A hU hV hcover n = 0 := by
  rw [mayerVietorisAssembly, HomologicalComplex.homologyMap_comp]
  change (HomologicalComplex.homologyMap (smallChainGluingSum U V A) (n + 1) ≫
    (unionCoverHomologyIso U V A hU hV hcover (n + 1)).hom) ≫
      ((unionCoverHomologyIso U V A hU hV hcover (n + 1)).inv ≫ _) = 0
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (smallChainGluingSequence_shortExact U V A).comp_δ (n + 1) n rfl

@[reassoc (attr := simp)]
theorem mayerVietorisBoundary_difference (n : ℕ) :
    mayerVietorisBoundary U V A hU hV hcover n ≫
      HomologicalComplex.homologyMap (smallChainGluingDifference U V A) n = 0 := by
  have h := (smallChainGluingSequence_shortExact U V A).δ_comp (n + 1) n rfl
  change _ ≫ HomologicalComplex.homologyMap (smallChainGluingDifference U V A) n = 0 at h
  rw [mayerVietorisBoundary, Category.assoc, h, comp_zero]

include hU hV hcover in
/-- Exactness at the homology of the direct sum of the actual small-chain complexes. -/
theorem mayerVietoris_exact_pair (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (smallChainGluingDifference U V A) n)
      (HomologicalComplex.homologyMap (mayerVietorisAssembly U V A) n)
      (by rw [← HomologicalComplex.homologyMap_comp,
        smallChainGluingDifference_assembly, HomologicalComplex.homologyMap_zero])).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((smallChainGluingSequence_shortExact U V A).homology_exact₂ n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (unionCoverHomologyIso U V A hU hV hcover n) (by simp [smallChainGluingSequence]) ?_
  simp only [Iso.refl_hom, Category.id_comp, mayerVietorisAssembly,
    HomologicalComplex.homologyMap_comp]
  rfl

/-- Exactness at actual ambient singular homology. -/
theorem mayerVietoris_exact_ambient (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (mayerVietorisAssembly U V A) (n + 1))
      (mayerVietorisBoundary U V A hU hV hcover n)
      (mayerVietorisAssembly_boundary U V A hU hV hcover n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((smallChainGluingSequence_shortExact U V A).homology_exact₃ (n + 1) n rfl)
  refine ShortComplex.isoMk (Iso.refl _)
    (unionCoverHomologyIso U V A hU hV hcover (n + 1)) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, mayerVietorisAssembly,
      HomologicalComplex.homologyMap_comp]
    rfl
  · simp [mayerVietorisBoundary]

/-- Exactness at the actual homology of the intersection-small chains. -/
theorem mayerVietoris_exact_intersection (n : ℕ) :
    (ShortComplex.mk (mayerVietorisBoundary U V A hU hV hcover n)
      (HomologicalComplex.homologyMap (smallChainGluingDifference U V A) n)
      (mayerVietorisBoundary_difference U V A hU hV hcover n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((smallChainGluingSequence_shortExact U V A).homology_exact₁ (n + 1) n rfl)
  refine ShortComplex.isoMk
    (unionCoverHomologyIso U V A hU hV hcover (n + 1))
    (Iso.refl _) (Iso.refl _) ?_ (by simp [smallChainGluingSequence])
  simp [mayerVietorisBoundary]

end Quillen.LocalCoefficients
