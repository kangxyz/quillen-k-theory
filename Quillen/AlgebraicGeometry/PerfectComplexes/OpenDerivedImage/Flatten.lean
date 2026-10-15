/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Structure
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Dense
public import Quillen.Waldhausen.Cofinality.GeneralDense
public import Quillen.Waldhausen.Functoriality.ExactEquivalence

/-!
# Exact flattening of the original derived-image categories

The nested original perfect-object subcategory and the corresponding direct
complex subcategory are genuinely equivalent, with literal original objects,
chain maps and inclusion functors. Actual quotient membership proves equality
of their inherited cofibration classes. The exact equivalence preserves the
original K-inclusion and its range in every degree. Genuine dense cofinality
then gives positive bijectivity and degree-zero injectivity for that same
flattened inclusion, under the displayed density and joint-cylinder data.
The actual qc-affine instance is exercised by maintained consumers; the
relative-source-to-image K comparison is a separate theorem.
-/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Forget only the redundant perfect-object wrapper. -/
def flatten : Obj j ⥤ ComplexObj j where
  obj A := ⟨A.obj.obj, A.property⟩
  map f := (complexObjects j).homMk f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restore the proved local perfectness of the same original complex. -/
def nest : ComplexObj j ⥤ Obj j where
  obj A := ⟨⟨A.obj, locallyPerfect_of_mem j A.property⟩, A.property⟩
  map f := (objects j).homMk ((locallyPerfect U).homMk f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem flatten_comp_nest : flatten j ⋙ nest j = 𝟭 (Obj j) := rfl
@[simp] theorem nest_comp_flatten : nest j ⋙ flatten j = 𝟭 (ComplexObj j) := rfl

/-- A genuine equivalence on unchanged original complexes and chain maps. -/
def flattenEquivalence : Obj j ≌ ComplexObj j where
  functor := flatten j
  inverse := nest j
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

local instance : (flatten j).IsEquivalence := (flattenEquivalence j).isEquivalence_functor
local instance : (nest j).IsEquivalence := (flattenEquivalence j).isEquivalence_inverse

/-- Flattening retains the literal original perfect-complex inclusion. -/
@[simp] theorem flatten_comp_inclusion : flatten j ⋙ inclusion j = (objects j).ι := rfl
@[simp] theorem nest_comp_inclusion : nest j ⋙ (objects j).ι = inclusion j := rfl

variable [Fact (HasDerivedRoofs j)] [HasBinaryCoproducts (Perfect U)]
  (h : Cofinality.DenseCofiberData (perfectWaldhausen U) (objects j))

/-- The inherited perfect cofibrations are exactly those on the flattened image. -/
theorem flatten_exact : IsExact h.waldhausenStructure.cof h.waldhausenStructure.weq
    (complexWaldhausen j).cof (complexWaldhausen j).weq (flatten j) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (nest j) _ hz
  cofibration f hf := (inclusion_cof_iff j ((flatten j).map f)).mp hf
  weak _ hf := hf
  pushout _ hp := hp.map (flatten j)

/-- The genuine inverse is exact for the same original weak arrows and cofibrations. -/
theorem nest_exact : IsExact (complexWaldhausen j).cof (complexWaldhausen j).weq
    h.waldhausenStructure.cof h.waldhausenStructure.weq (nest j) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (flatten j) _ hz
  cofibration f hf := (inclusion_exact j).cofibration f hf
  weak _ hf := hf
  pushout _ hp := hp.map (nest j)

/-- All connective K-groups agree by an actual exact equivalence. -/
def flattenKEquiv (n : ℕ) : h.waldhausenStructure.K n ≃* (complexWaldhausen j).K n :=
  KEquivOfExactEquivalence _ _ (flattenEquivalence j) (flatten_exact j h) (nest_exact j h) n

/-- The forward K comparison is the actual original flattening map. -/
@[simp] theorem flattenKEquiv_toMonoidHom (n : ℕ) :
    (flattenKEquiv j h n :
      h.waldhausenStructure.K n →* (complexWaldhausen j).K n) = KMap (flatten_exact j h) n := rfl

/-- Original inclusion commutes with the flattening K comparison. -/
theorem flattenKEquiv_inclusion (n : ℕ) :
    (KMap (inclusion_exact j) n).comp (flattenKEquiv j h n) =
      KMap h.inclusion_exact n := by
  rw [flattenKEquiv_toMonoidHom, Quillen.Waldhausen.KMap_comp_KMap]

include h in
/-- Cofinality of the original dense image gives the original flattened inclusion in positive
  degrees. -/
theorem inclusion_KMap_succ_bijective
    (D : Fibration.RowFactorization.JointData (.refl (perfectWaldhausen U)))
    (hs : Fibration.RowFactorization.SecondEndpointSection (.refl (perfectWaldhausen U)) D)
    (n : ℕ) : Function.Bijective (KMap (inclusion_exact j) (n+1)) := by
  have hcomp := h.inclusion_KMap_succ_bijective_general D hs n
  rw [← flattenKEquiv_inclusion j h (n+1)] at hcomp
  exact ((flattenKEquiv j h (n+1)).bijective.of_comp_iff _).mp hcomp

include h in
/-- The original flattened inclusion is injective in every connective degree, including zero. -/
theorem inclusion_KMap_injective
    (D : Fibration.RowFactorization.JointData (.refl (perfectWaldhausen U)))
    (hs : Fibration.RowFactorization.SecondEndpointSection (.refl (perfectWaldhausen U)) D)
    (n : ℕ) : Function.Injective (KMap (inclusion_exact j) n) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (flattenKEquiv j h n).surjective x
  obtain ⟨b, rfl⟩ := (flattenKEquiv j h n).surjective y
  apply congrArg (flattenKEquiv j h n)
  apply h.inclusion_KMap_injective_general D hs n
  change ((KMap (inclusion_exact j) n).comp (flattenKEquiv j h n)) a =
    ((KMap (inclusion_exact j) n).comp (flattenKEquiv j h n)) b at hxy
  rwa [flattenKEquiv_inclusion] at hxy

/-- The inverse flattening comparison retains the same original inclusion homomorphism. -/
theorem flattenKEquiv_symm_inclusion (n : ℕ) :
    (KMap h.inclusion_exact n).comp (flattenKEquiv j h n).symm.toMonoidHom =
      KMap (inclusion_exact j) n := by
  ext x
  have hx := DFunLike.congr_fun (flattenKEquiv_inclusion j h n) ((flattenKEquiv j h n).symm x)
  exact hx.symm.trans (congrArg (KMap (inclusion_exact j) n)
    ((flattenKEquiv j h n).apply_symm_apply x))

/-- Flattening preserves the entire actual inclusion range in every degree. -/
theorem flatten_inclusion_range (n : ℕ) :
    (KMap (inclusion_exact j) n).range = (KMap h.inclusion_exact n).range := by
  have hr : (flattenKEquiv j h n :
      h.waldhausenStructure.K n →* (complexWaldhausen j).K n).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (flattenKEquiv j h n).surjective
  rw [← flattenKEquiv_inclusion j h n, MonoidHom.range_comp, hr, Subgroup.map_top]

end Quillen.PerfectComplexes.OpenDerivedImage
