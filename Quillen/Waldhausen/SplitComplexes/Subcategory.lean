import Quillen.Waldhausen.SplitComplexes.Basic
import Quillen.Waldhausen.SubcategoryInclusion

/-!
# Degreewise split Waldhausen subcategories of complexes

For a replete extension-closed full subcategory containing zero, retain
exactly the inherited cofibrations which split in every degree. Thus the
quotient must still lie in the chosen subcategory. All Waldhausen axioms
are derived from the ambient pushout and quasi-isomorphism gluing theorems.
The identity comparison to the ambient-monomorphism convention and
inclusions between such subcategories are actual exact functors.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Waldhausen

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- Inherited cofibrations with termwise splittings. The inherited condition
requires that the actual quotient belong to the full subcategory. -/
def splitSubcategoryCofibrations : MorphismProperty P.FullSubcategory :=
  subcategoryCofibrations P ⊓ degreewiseSplitMono.inverseImage P.ι

/-- The degreewise split, quasi-isomorphism Waldhausen structure on an actual
extension-closed full subcategory of complexes. -/
def splitComplexSubcategory : Structure P.FullSubcategory :=
  { complexSubcategory P with
    cof := splitSubcategoryCofibrations P
    cof_multiplicative := by
      let : (subcategoryCofibrations P).IsMultiplicative :=
        (complexSubcategory P).cof_multiplicative
      unfold splitSubcategoryCofibrations
      infer_instance
    cof_iso := by
      intro K L f hf
      let : IsIso f := hf
      exact ⟨(complexSubcategory P).cof_iso f hf, degreewiseSplitMono_of_isIso f.hom⟩
    cof_zero K := ⟨(complexSubcategory P).cof_zero K,
      degreewiseSplitMono_of_isZero (P.ι.map_isZero (complexSubcategory P).isZero) _⟩
    pushout_exists i f hi := (complexSubcategory P).pushout_exists i f hi.1
    cof_pushout hi h := ⟨(complexSubcategory P).cof_pushout hi.1 h,
      degreewiseSplitMono_pushout hi.2 (fullSubcategory_map_pushout _ P hi.1 h)⟩
    gluing a b d p hi hi' h h' ei ef eg ej ha hb hd :=
      (complexSubcategory P).gluing a b d p hi.1 hi'.1 h h' ei ef eg ej ha hb hd }

/-- The canonical identity comparison changes only the cofibration convention. -/
theorem splitComplexSubcategory_to_complexSubcategory_exact :
    IsExact (splitComplexSubcategory P).cof (splitComplexSubcategory P).weq
      (complexSubcategory P).cof (complexSubcategory P).weq (𝟭 P.FullSubcategory) where
  zero h := h
  cofibration _ h := h.1
  weak _ h := h
  pushout _ h := h

/-- The actual full inclusion into all complexes with split cofibrations. -/
theorem splitComplexSubcategory_inclusion_exact :
    IsExact (splitComplexSubcategory P).cof (splitComplexSubcategory P).weq
      (splitComplexes A).cof (splitComplexes A).weq P.ι where
  zero h := P.ι.map_isZero h
  cofibration _ h := h.2
  weak _ h := h
  pushout hi h := fullSubcategory_map_pushout _ P hi.1 h

/-- The canonical comparison between the genuine K-groups for the two
cofibration conventions. This construction does not claim it is an isomorphism. -/
def splitComplexSubcategoryKMap (n : ℕ) :
    (splitComplexSubcategory P).K n →* (complexSubcategory P).K n :=
  KMap (splitComplexSubcategory_to_complexSubcategory_exact P) n

variable (Q : ObjectProperty (CochainComplex A ℤ))
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts] (h : P ≤ Q)

/-- Inclusion of object properties preserves split cofibrations, actual
quasi-isomorphisms, and the required pushouts. -/
theorem splitSubcategoryInclusion_exact :
    IsExact (splitComplexSubcategory P).cof (splitComplexSubcategory P).weq
      (splitComplexSubcategory Q).cof (splitComplexSubcategory Q).weq
      (ObjectProperty.ιOfLE h) where
  zero hZ := (ObjectProperty.ιOfLE h).map_isZero hZ
  cofibration f hf := ⟨(subcategoryInclusion_exact P Q h).cofibration f hf.1, hf.2⟩
  weak _ hf := hf
  pushout hi hs := (subcategoryInclusion_exact P Q h).pushout hi.1 hs

/-- The genuine split-cofibration K-map attached to a subcategory inclusion. -/
def splitSubcategoryKMap (n : ℕ) :
    (splitComplexSubcategory P).K n →* (splitComplexSubcategory Q).K n :=
  KMap (splitSubcategoryInclusion_exact P Q h) n

end Quillen.Waldhausen
