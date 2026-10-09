import Quillen.Devissage.Filtration
import Quillen.CategoryTheory.ExactCategory.Abelian
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-!
# Filtrations from successive kernels of an epimorphic unit

The filtration stores genuine short exact sequences. Eventual vanishing of
iterated kernels is an algebraic nilpotence condition, not a K-equivalence
hypothesis. The accompanying adjunction lemma derives full faithfulness from
a faithful right adjoint and epimorphic unit.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace Quillen.ReflectorDevissage

section Filtration
variable {C : Type u} [Category.{v} C] [Abelian C]
  {T : C ⥤ C} (η : 𝟭 C ⟶ T)
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The actual kernel of one component of the unit. -/
abbrev kernelStep (X : C) := kernel (η.app X)

/-- Repeated kernels, with the original object at stage zero. -/
def kernelIterate : ℕ → C → C
  | 0, X => X
  | n + 1, X => kernelIterate n (kernelStep η X)

variable (P : ObjectProperty C) [∀ X, Epi (η.app X)]
  (hP : ∀ X, P (T.obj X))

/-- The actual finite filtration obtained by unwinding eventual kernel
vanishing, using the epimorphic unit at each step. -/
def filtrationOfKernelIterateZero : ∀ (n : ℕ) (X : C),
    IsZero (kernelIterate η n X) → (abelianExactStructure C).Filtration P X
  | 0, X, h => .zero h
  | n + 1, X, h => .step
      (ShortComplex.mk (kernel.ι (η.app X)) (η.app X) (kernel.condition (η.app X)))
      { exact := ShortComplex.kernelSequence_exact (η.app X) }
      (filtrationOfKernelIterateZero n (kernelStep η X) h) (hP X)

include hP in
/-- Every object whose kernel iteration terminates admits a genuine finite
filtration with factors in the image of the reflector. -/
theorem exists_filtration_of_eventually_zero (X : C)
    (h : ∃ n, IsZero (kernelIterate η n X)) :
    Nonempty ((abelianExactStructure C).Filtration P X) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨filtrationOfKernelIterateZero η P hP n X hn⟩
end Filtration

section Adjunction
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [Balanced D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [R.Faithful] [∀ X, Epi (adj.unit.app X)]

/-- An epimorphic unit is an isomorphism on the right adjoint's image,
by the actual triangle identity. -/
theorem unit_obj_isIso (Y : D) : IsIso (adj.unit.app (R.obj Y)) := by
  letI : IsSplitMono (adj.unit.app (R.obj Y)) :=
    ⟨⟨{ retraction := R.map (adj.counit.app Y), id := adj.right_triangle_components Y }⟩⟩
  exact isIso_of_epi_of_isSplitMono _

/-- A faithful right adjoint with epimorphic unit has invertible counit;
no exactness or equivalence is assumed. -/
theorem counit_app_isIso (Y : D) : IsIso (adj.counit.app Y) := by
  letI := unit_obj_isIso adj Y
  have heq : R.map (adj.counit.app Y) = inv (adj.unit.app (R.obj Y)) :=
    (IsIso.inv_eq_of_hom_inv_id (adj.right_triangle_components Y)).symm
  haveI : IsIso (R.map (adj.counit.app Y)) := by rw [heq]; infer_instance
  exact isIso_of_reflects_iso (adj.counit.app Y) R

/-- Full faithfulness is derived from the unit hypothesis and faithfulness. -/
def fullyFaithfulRight : R.FullyFaithful := by
  letI : ∀ Y, IsIso (adj.counit.app Y) := counit_app_isIso adj
  letI : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  exact adj.fullyFaithfulROfIsIsoCounit

include adj in
/-- The essential image is closed under ambient subobjects when the unit is
an epimorphism. Naturality makes its component on the subobject monic too. -/
theorem essImage_of_mono [Balanced C] {X Y : C} (f : X ⟶ Y) [Mono f]
    (hY : R.essImage Y) : R.essImage X := by
  letI : R.Full := (fullyFaithfulRight adj).full
  letI : IsIso (adj.unit.app Y) := (adj.isIso_unit_app_iff_mem_essImage).2 hY
  haveI : Mono (adj.unit.app X) := mono_of_mono_fac (adj.unit.naturality f).symm
  letI : IsIso (adj.unit.app X) := isIso_of_mono_of_epi _
  exact adj.mem_essImage_of_unit_isIso X

end Adjunction
section Converse
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R) [R.Full] [R.Faithful]

/-- The unit's universal property is injective on maps into the actual
right-adjoint essential image. No strict choice of image object is needed. -/
theorem unit_precomp_injective (X : C) {Z : C} (hZ : R.essImage Z) :
    Function.Injective (fun f : (L ⋙ R).obj X ⟶ Z => adj.unit.app X ≫ f) := by
  obtain ⟨Y, ⟨e⟩⟩ := hZ
  intro f g h
  obtain ⟨a, ha⟩ := R.map_surjective (f ≫ e.inv)
  obtain ⟨b, hb⟩ := R.map_surjective (g ≫ e.inv)
  have hab : a = b := (adj.homEquiv X Y).injective (by
    simpa only [Adjunction.homEquiv_unit, ha, hb, Category.assoc] using
      congrArg (fun k => k ≫ e.inv) h)
  apply (cancel_mono e.inv).1
  exact ha.symm.trans ((congrArg R.map hab).trans hb)

/-- A quotient-closed reflective essential image has epimorphic unit.
The proof annihilates the actual cokernel projection by adjunction. -/
theorem unit_epi_of_essImage_quotient_closed
    [(R.essImage).IsClosedUnderQuotients] (X : C) : Epi (adj.unit.app X) := by
  have hC : R.essImage (cokernel (adj.unit.app X)) :=
    R.essImage.prop_of_epi (cokernel.π (adj.unit.app X)) (R.obj_mem_essImage _)
  apply Abelian.epi_of_cokernel_π_eq_zero
  apply unit_precomp_injective adj X hC
  simp only [cokernel.condition, comp_zero]
end Converse
end Quillen.ReflectorDevissage
