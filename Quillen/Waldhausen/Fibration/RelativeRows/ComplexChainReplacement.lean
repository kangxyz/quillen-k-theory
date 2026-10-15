/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Waldhausen.Fibration.RelativeRows.ChainReplacement
public import Quillen.Waldhausen.Fibration.Rows.ComplexFactorization
public import Quillen.Waldhausen.SplitComplexes.Approximation

/-! # Genuine relative completion of mixed chains of actual complex rows

The cylinder input is the proved identity-cone row factorization. Its genuine
Reedy cofibration evidence and exact fine-map preservation are used unchanged.
Every projection component is a genuine quasi-isomorphism. Cone and shift
closure are precisely the hypotheses of that proved joint-cylinder input.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.RelativeRows
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

local instance complexChainCompletion_rowSaturated (m : SimplexCategory) :
    (RowWeakEquivalences.nested (complexSubcategoryNested P)
      m).coarse.weq.HasTwoOutOfThreeProperty :=
  @RowWeakEquivalences.coarseStructure_twoOutOfThree _ _ _ (complexSubcategoryNested P) m
    (complexSubcategory_saturated P)

/-- The actual inner-row cylinder followed by the genuine relative-row completion. -/
def complexRowRelativeReplacement (m n : SimplexCategory) :
    CoarseWeakChain (RowWeakEquivalences.nested (complexSubcategoryNested P) m) n ⥤
      Obj (RowWeakEquivalences.nested (complexSubcategoryNested P) m) n :=
  relativeReplacement (RowWeakEquivalences.nested (complexSubcategoryNested P) m)
    (complexRowFactorization P hcone hshift m) n

/-- The unchanged displayed coarse projection on the actual inner-row chains. -/
def complexRowRelativeProjection (m n : SimplexCategory) :
    complexRowRelativeReplacement P hcone hshift m n ⋙
      initialFiltrationFunctor (RowWeakEquivalences.nested (complexSubcategoryNested P) m) n ⟶
      (coarseWeakChains (RowWeakEquivalences.nested (complexSubcategoryNested P) m) n).ι :=
  relativeReplacementProjection (RowWeakEquivalences.nested (complexSubcategoryNested P) m)
    (complexRowFactorization P hcone hshift m) n

/-- Each original projection component, at each genuine inner interval, is a quasi-isomorphism. -/
theorem complexRowRelativeProjection_quasi (m n : SimplexCategory)
    (F : CoarseWeakChain (RowWeakEquivalences.nested (complexSubcategoryNested P) m) n)
    (i : Fin (n.len + 1)) (p : Interval m) :
    QuasiIso (((((complexRowRelativeProjection P hcone hshift m n).app F).app i).hom.app p).hom) :=
  relativeReplacementProjection_coarse (RowWeakEquivalences.nested (complexSubcategoryNested P) m)
    (complexRowFactorization P hcone hshift m) n F i p

/-- Original fine transformations remain fine on the entire actual completed row of rows. -/
theorem complexRowRelativeReplacement_fine (m n : SimplexCategory)
    {F G : CoarseWeakChain (RowWeakEquivalences.nested (complexSubcategoryNested P) m) n}
    (f : F ⟶ G) (hf : ∀ i p, IsIso (((f.hom.app i).hom.app p))) :
    (waldhausenStructure (RowWeakEquivalences.nested (complexSubcategoryNested P) m) n).weq
      ((complexRowRelativeReplacement P hcone hshift m n).map f) :=
  relativeReplacement_fine (RowWeakEquivalences.nested (complexSubcategoryNested P) m)
    (complexRowFactorization P hcone hshift m) (complexRowFactorization_fineSquares P hcone
      hshift m) f hf

end Quillen.Waldhausen.Fibration.RelativeRows
