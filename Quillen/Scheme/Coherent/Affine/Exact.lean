import Quillen.Scheme.Coherent.Affine.Basic
import Quillen.CategoryTheory.ExactCategory.Functor
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Exactness of the actual affine sheaf functors

The tilde functor preserves monomorphisms because its sections are locally
fractional families and localization preserves injectivity. Together with its
existing left adjoint structure, this proves exactness. Thus the abelian
structure on affine quasicoherent sheaves agrees with the ambient sheaf exact
structure, rather than merely being an abstractly transported structure.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme
variable (R : CommRingCat.{u})

lemma tilde_map_app_injective {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Injective f) (U : (Spec R).Opens) :
    Function.Injective ((tilde.map f).app U) := by
  intro s t h
  apply Subtype.ext
  funext x
  apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N) f.hom hf
  exact congrArg (fun a => a.val x) h

instance tilde_preservesMonomorphisms : (tilde.functor R).PreservesMonomorphisms where
  preserves {M N} f hf := by
    constructor
    intro P g h hgh
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    apply tilde_map_app_injective R f ((ModuleCat.mono_iff_injective f).mp hf) U
    exact congrArg (fun a => a.app U s) hgh

instance tilde_preservesHomology : (tilde.functor R).PreservesHomology :=
  (tilde.functor R).preservesHomology_of_preservesMonos_and_cokernels

instance tilde_preservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) :=
  (tilde.functor R).preservesFiniteLimits_of_preservesHomology

/-- The comparison identifies the composite tilde after global sections with
 the actual inclusion of quasicoherent sheaves. -/
def affineQuasicoherentToSheavesIso :
    (tildeEquiv (R := R)).inverse ⋙ tilde.functor R ≅
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι :=
  (Functor.associator (tildeEquiv (R := R)).inverse (tildeEquiv (R := R)).functor
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι).symm ≪≫
    Functor.isoWhiskerRight (tildeEquiv (R := R)).counitIso _ ≪≫ Functor.leftUnitor _

instance affineQuasicoherentToSheaves_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι := by
  have : PreservesFiniteLimits ((tildeEquiv (R := R)).inverse ⋙ tilde.functor R) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (affineQuasicoherentToSheavesIso R)

instance affineQuasicoherentToSheaves_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι := by
  have : PreservesFiniteColimits ((tildeEquiv (R := R)).inverse ⋙ tilde.functor R) :=
    comp_preservesFiniteColimits _ _
  exact preservesFiniteColimits_of_natIso (affineQuasicoherentToSheavesIso R)

variable [IsNoetherianRing R]

instance affineCoherentToQuasicoherent_preservesFiniteLimits :
    PreservesFiniteLimits (affineFiniteType R).ι := by
  have := (affineFiniteType R).preservesKernels_ι
  exact Functor.preservesFiniteLimits_of_preservesKernels _

instance affineCoherentToQuasicoherent_preservesFiniteColimits :
    PreservesFiniteColimits (affineFiniteType R).ι := by
  have := (affineFiniteType R).preservesCokernels_ι
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

instance affineCoherentToSheaves_preservesFiniteLimits :
    PreservesFiniteLimits (affineCoherentToSheaves R) :=
  comp_preservesFiniteLimits (affineFiniteType R).ι
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι

instance affineCoherentToSheaves_preservesFiniteColimits :
    PreservesFiniteColimits (affineCoherentToSheaves R) :=
  comp_preservesFiniteColimits (affineFiniteType R).ι
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι

instance affineCoherentToSheaves_additive : (affineCoherentToSheaves R).Additive :=
  inferInstanceAs (Functor.Additive (_ ⋙ _))

/-- The actual inclusion of affine coherent sheaves preserves sheaf short
exact sequences and therefore is an exact functor. -/
def affineCoherentInclusion :
    ExactFunctor (affineCoherentExactStructure R) (abelianExactStructure (Spec R).Modules) where
  toFunctor := affineCoherentToSheaves R
  map_conflation _ h := h.map_of_exact _

/-- Exactness in the coherent category is exactly ambient sheaf exactness. -/
theorem affineCoherent_shortExact_iff (S : ShortComplex (AffineCoherent R)) :
    S.ShortExact ↔ (S.map (affineCoherentToSheaves R)).ShortExact := by
  constructor
  · exact fun h => h.map_of_exact _
  · intro h
    have := h.mono_f
    have := h.epi_g
    exact { exact := Functor.reflects_exact_of_faithful (affineCoherentToSheaves R) S h.exact
            mono_f := Functor.mono_of_mono_map (affineCoherentToSheaves R) h.mono_f
            epi_g := Functor.epi_of_epi_map (affineCoherentToSheaves R) h.epi_g }

end Quillen.CoherentScheme
