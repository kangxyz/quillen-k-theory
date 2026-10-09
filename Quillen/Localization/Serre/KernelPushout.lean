import Quillen.Localization.Serre.AuxiliaryKernel

/-!
# Pushing out an auxiliary epimorphism along its kernel

This constructs the actual enlarged extension used in the kernel-comma
reflection. The new kernel, quotient, epimorphism, and Serre membership are
proved from pushout and cokernel universal properties.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]

/-- The pullback model has its actual kernel inclusion. -/
abbrev overKernelι {N : C} (X : Over N) : (overKernel N).obj X ⟶ X.left :=
  pullback.fst X.hom (0 : (0 : C) ⟶ N)

@[reassoc (attr := simp)]
lemma overKernel_condition {N : C} (X : Over N) : overKernelι X ≫ X.hom = 0 := by
  rw [pullback.condition]
  simp

/-- The base-change model is genuinely a limiting kernel fork. -/
def overKernelIsKernel {N : C} (X : Over N) :
    IsLimit (KernelFork.ofι (overKernelι X) (overKernel_condition X)) :=
  KernelFork.IsLimit.ofι _ _
    (fun g hg => pullback.lift (f := X.hom) (g := (0 : (0 : C) ⟶ N)) g 0 (by simpa using hg))
    (fun g hg => pullback.lift_fst _ _ _)
    (fun g hg m hm => by
      apply pullback.hom_ext
      · simpa using hm
      · exact (isZero_zero C).eq_of_tgt _ _)

variable {N : C} (X : Over N) {U : C} (i : (overKernel N).obj X ⟶ U)

/-- The enlarged middle object is an actual pushout of the old kernel inclusion. -/
abbrev kernelPushoutObj := pushout (overKernelι X) i

/-- The enlarged middle object still maps to the same quotient `N`. -/
def kernelPushoutMap : kernelPushoutObj X i ⟶ N :=
  pushout.desc X.hom 0 (by simp)

@[reassoc (attr := simp)]
lemma kernelPushout_inl_map : pushout.inl (overKernelι X) i ≫ kernelPushoutMap X i = X.hom := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma kernelPushout_inr_map : pushout.inr (overKernelι X) i ≫ kernelPushoutMap X i = 0 := by
  exact pushout.inr_desc _ _ _

instance kernelPushoutMap_epi [Epi X.hom] : Epi (kernelPushoutMap X i) :=
  epi_of_epi_fac (kernelPushout_inl_map X i)

/-- The enlarged epimorphism is the cokernel of the new kernel inclusion. -/
def kernelPushoutIsCokernel [Epi X.hom] :
    IsColimit (CokernelCofork.ofπ (kernelPushoutMap X i) (kernelPushout_inr_map X i)) := by
  let hc := Abelian.epiIsCokernelOfKernel _ (overKernelIsKernel X)
  apply CokernelCofork.IsColimit.ofπ'
  intro Z g hg
  have hg0 : overKernelι X ≫ (pushout.inl (overKernelι X) i ≫ g) = 0 := by
    rw [← Category.assoc, pushout.condition, Category.assoc, hg, comp_zero]
  let d := CokernelCofork.IsColimit.desc' hc (pushout.inl (overKernelι X) i ≫ g) hg0
  refine ⟨d.val, ?_⟩
  apply pushout.hom_ext
  · rw [← Category.assoc, kernelPushout_inl_map]
    exact d.property
  · rw [← Category.assoc, kernelPushout_inr_map, zero_comp, hg]

/-- The pushout of a kernel inclusion is still the actual kernel of the new epi. -/
def kernelPushoutIsKernel [Epi X.hom] :
    IsLimit (KernelFork.ofι (pushout.inr (overKernelι X) i) (kernelPushout_inr_map X i)) :=
  Abelian.monoIsKernelOfCokernel _ (kernelPushoutIsCokernel X i)

/-- Canonical identification of the prescribed enlarged kernel with the
pullback kernel used by the auxiliary Q-functor. -/
def kernelPushoutIso [Epi X.hom] :
    U ≅ (overKernel N).obj (Over.mk (kernelPushoutMap X i)) :=
  (kernelPushoutIsKernel X i).conePointUniqueUpToIso
    (overKernelIsKernel (Over.mk (kernelPushoutMap X i)))

@[reassoc (attr := simp)]
lemma kernelPushoutIso_hom_ι [Epi X.hom] :
    (kernelPushoutIso X i).hom ≫ overKernelι (Over.mk (kernelPushoutMap X i)) =
      pushout.inr (overKernelι X) i :=
  (kernelPushoutIsKernel X i).conePointUniqueUpToIso_hom_comp
    (overKernelIsKernel (Over.mk (kernelPushoutMap X i))) .zero

/-- The old middle object maps into the enlarged extension over the same base. -/
def kernelPushoutOverHom : X ⟶ Over.mk (kernelPushoutMap X i) :=
  Over.homMk (pushout.inl (overKernelι X) i) (kernelPushout_inl_map X i)

/-- The induced kernel map is exactly the prescribed kernel map, followed
by the proved canonical identification of the new kernel. -/
lemma kernelPushoutOverHom_kernel [Epi X.hom] :
    (overKernel N).map (kernelPushoutOverHom X i) = i ≫ (kernelPushoutIso X i).hom := by
  apply (cancel_mono (overKernelι (Over.mk (kernelPushoutMap X i)))).1
  rw [Category.assoc, kernelPushoutIso_hom_ι]
  change (overKernel N).map (kernelPushoutOverHom X i) ≫
    pullback.fst (kernelPushoutMap X i) (0 : (0 : C) ⟶ N) = _
  exact (overKernel_map_isPullback (kernelPushoutOverHom X i)).w.trans pushout.condition

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- Enlarging the kernel to a Serre object preserves the Serre-isomorphism
condition, with no extension-lifting hypothesis. -/
theorem kernelPushoutMap_isoModSerre [Epi X.hom] (hU : P U) :
    P.isoModSerre (kernelPushoutMap X i) := by
  rw [ObjectProperty.isoModSerre_iff_of_epi]
  let e := (kernelPushoutIsKernel X i).conePointUniqueUpToIso (kernelIsKernel (kernelPushoutMap X i))
  exact P.prop_of_iso e hU

/-- The actual enlarged object belongs to the epimorphic auxiliary category. -/
def kernelPushoutAuxiliary [Epi X.hom] (hU : P U) : EpiAuxiliaryKernel P N :=
  ⟨Q.of _ _ (Over.mk (kernelPushoutMap X i)), kernelPushoutMap_isoModSerre X i P hU,
    inferInstanceAs (Epi (kernelPushoutMap X i))⟩

end Quillen.SerreLocalization
