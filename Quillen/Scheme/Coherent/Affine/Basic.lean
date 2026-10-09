import Quillen.GTheory.FiniteModules.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Coherent sheaves on a noetherian affine scheme

We use the actual full subcategory of quasicoherent `𝒪_{Spec R}`-modules and
its equivalence with `R`-modules. Coherence on a noetherian affine scheme is
expressed by finite generation of the global-sections module. In particular,
these objects contain an actual sheaf on `Spec R`, and their morphisms are
actual morphisms of sheaves.

The coherent objects form a Serre class in quasicoherent sheaves. No claim
is made that they form a Serre class in all sheaves of modules: arbitrary
subsheaves need not be quasicoherent. General non-affine noetherian schemes
and the comparison with locally finitely presented sheaves require further
local-to-global results.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

variable (R : CommRingCat.{u})

/-- The actual quasicoherent sheaves on `Spec R`. -/
abbrev AffineQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory

instance affineQuasicoherent_hasFiniteLimits : HasFiniteLimits (AffineQuasicoherent R) where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (tildeEquiv (R := R)).inverse

/-- Quasicoherent sheaves on an affine scheme are an abelian category. -/
instance affineQuasicoherent_abelian : Abelian (AffineQuasicoherent R) :=
  abelianOfEquivalence (tildeEquiv (R := R)).inverse

/-- The condition that the global-sections module of an affine quasicoherent
sheaf is finite. This becomes coherence when the base ring is noetherian. -/
def affineFiniteType : ObjectProperty (AffineQuasicoherent R) :=
  (finiteModule R).inverseImage (tildeEquiv (R := R)).inverse

@[simp]
lemma affineFiniteType_iff (M : AffineQuasicoherent R) :
    affineFiniteType R M ↔ Module.Finite R (moduleSpecΓFunctor.obj M.obj) := Iff.rfl

instance affineFiniteType_isoClosed : (affineFiniteType R).IsClosedUnderIsomorphisms := by
  change ((finiteModule R).inverseImage (tildeEquiv (R := R)).inverse).IsClosedUnderIsomorphisms
  infer_instance

variable [IsNoetherianRing R]

/-- The category of coherent sheaves on the noetherian affine scheme `Spec R`.
It is a full subcategory of the actual category of quasicoherent sheaves. -/
abbrev AffineCoherent (R : CommRingCat.{u}) [IsNoetherianRing R] :=
  (affineFiniteType R).FullSubcategory

/-- On a noetherian affine scheme, coherent sheaves form a Serre class inside
quasicoherent sheaves. -/
instance affineFiniteType_isSerreClass : (affineFiniteType R).IsSerreClass := by
  change ((finiteModule R).inverseImage (tildeEquiv (R := R)).inverse).IsSerreClass
  infer_instance

/-- The category of coherent sheaves on a noetherian affine scheme is abelian. -/
instance affineCoherent_abelian : Abelian (AffineCoherent R) := inferInstance

/-- The fully faithful inclusion into all sheaves of modules on `Spec R`. -/
def affineCoherentToSheaves : AffineCoherent R ⥤ (Spec R).Modules :=
  (affineFiniteType R).ι ⋙ (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι

instance : (affineCoherentToSheaves R).Full := inferInstanceAs (Functor.Full (_ ⋙ _))
instance : (affineCoherentToSheaves R).Faithful := inferInstanceAs (Functor.Faithful (_ ⋙ _))

instance (M : AffineCoherent R) :
    ((affineCoherentToSheaves R).obj M).IsQuasicoherent := M.obj.property

instance (M : AffineCoherent R) :
    Module.Finite R (moduleSpecΓFunctor.obj ((affineCoherentToSheaves R).obj M)) := M.property

/-- Global sections and tilde give an explicit equivalence between coherent
sheaves on `Spec R` and finite `R`-modules. -/
def affineCoherentEquivalence : AffineCoherent R ≌ FiniteModule.{u, u} R :=
  (tildeEquiv (R := R)).symm.congrFullSubcategory rfl

/-- Coherent sheaves on an affine noetherian scheme have a small model in the
universe of the base ring. This uses actual finite module representatives. -/
instance affineCoherent_essentiallySmall : EssentiallySmall.{u} (AffineCoherent R) :=
  essentiallySmall_of_fully_faithful (affineCoherentEquivalence R).functor

/-- The genuine abelian exact structure on affine coherent sheaves. -/
def affineCoherentExactStructure : ExactStructure (AffineCoherent R) :=
  abelianExactStructure _

end Quillen.CoherentScheme
