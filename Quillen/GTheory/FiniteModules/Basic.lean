import Quillen.Localization.Serre.FiniteProducts
import Quillen.CategoryTheory.ExactCategory.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finite modules over a noetherian ring

The object property here is genuine finite generation of modules. Over a
noetherian ring it is a Serre class, so its full subcategory is abelian. This
provides the algebraic affine chart for coherent sheaves, rather than assuming
an abelian structure on a category given an unrelated name.
-/

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

variable (R : Type u) [Ring R]

/-- The property of being a finitely generated `R`-module. -/
abbrev finiteModule : ObjectProperty (ModuleCat.{v} R) := ModuleCat.isFG R

/-- The actual full subcategory of finitely generated modules. -/
abbrev FiniteModule := (finiteModule.{u, v} R).FullSubcategory

instance (M : FiniteModule.{u, v} R) : Module.Finite R M.obj := M.property

instance finiteModule_isoClosed : (finiteModule.{u, v} R).IsClosedUnderIsomorphisms where
  of_iso e h := by
    let : Module.Finite R _ := h
    exact Module.Finite.equiv e.toLinearEquiv

instance finiteModule_containsZero : (finiteModule.{u, v} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R (ULift.{v} PUnit),
    ModuleCat.isZero_of_subsingleton _, by dsimp [finiteModule, ModuleCat.isFG]; infer_instance⟩

instance finiteModule_quotients : (finiteModule.{u, v} R).IsClosedUnderQuotients where
  prop_of_epi f hf h := by
    let : Module.Finite R _ := h
    exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp hf)

instance finiteModule_extensions : (finiteModule.{u, v} R).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    let : Module.Finite R _ := h₁
    let : Module.Finite R _ := h₃
    exact Module.Finite.of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
      hS.moduleCat_surjective_g

/-- Finite modules admit a genuine small model, represented by quotients of finite free modules. -/
instance finiteModule_essentiallySmall : EssentiallySmall.{u} (FiniteModule.{u, v} R) :=
  inferInstanceAs (EssentiallySmall.{u} (FGModuleCat.{v} R))

variable [IsNoetherianRing R]

instance finiteModule_subobjects : (finiteModule.{u, v} R).IsClosedUnderSubobjects where
  prop_of_mono f hf h := by
    let : Module.Finite R _ := h
    exact Module.Finite.of_injective f.hom ((ModuleCat.mono_iff_injective f).mp hf)

/-- Finite modules form a Serre class over a noetherian ring. -/
instance finiteModule_isSerreClass : (finiteModule.{u, v} R).IsSerreClass where

/-- The usual category of finite modules over a noetherian ring is abelian. -/
instance finiteModule_abelian : Abelian (FiniteModule.{u, v} R) := inferInstance

/-- Its exact structure consists of all short exact sequences. -/
def finiteModuleExactStructure : ExactStructure (FiniteModule.{u, v} R) :=
  abelianExactStructure _

end Quillen.CoherentScheme
