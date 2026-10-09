import Quillen.Scheme.VectorBundle.Exact
import Quillen.CategoryTheory.SmallModel.Exact

/-!
# Quillen K-theory of an actual scheme

For an arbitrary scheme `X : Scheme.{u}`, define `SchemeK X n` using the exact
category of finite locally free `𝒪_X`-module sheaves, with all ambient short
exact sequences as conflations. We use the genuine categorical small model
in the explicitly enlarged universe `u + 1`. This requires neither a
noetherian hypothesis nor an unproved essential-smallness theorem in the
smaller universe `u`.

This file does not identify realizations across universe changes. Independence
of exact presentations within the chosen universe is provided by
`ExactStructure.presentationKEquiv`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.SchemeSheaf

/-- The actual vector-bundle category is essentially small in `u + 1`. -/
instance vectorBundle_essentiallySmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} (FiniteLocallyFree X) := by
  infer_instance

/-- A genuine small category equivalent to finite locally free sheaves. -/
abbrev SmallVectorBundle (X : Scheme.{u}) : Type (u + 1) :=
  SmallModel.{u + 1} (FiniteLocallyFree X)

/-- The exact structure transported to the actual categorical small model. -/
abbrev smallVectorBundleExactStructure (X : Scheme.{u}) :
    ExactStructure (SmallVectorBundle X) :=
  ExactStructure.smallModel.{u + 1} (vectorBundleExactStructure X)

/-- The exact realization of small-model objects as actual vector bundles. -/
def smallVectorBundleToSheaves (X : Scheme.{u}) :
    ExactFunctor (smallVectorBundleExactStructure X) (sheafExactStructure X) :=
  (ExactStructure.smallModelToOriginal.{u + 1} (vectorBundleExactStructure X)).comp
    (vectorBundleExactInclusion X)

/-- A small-model conflation is precisely an actual short exact sequence of
its associated module sheaves. -/
@[simp]
theorem smallVectorBundleExactStructure_conflation {X : Scheme.{u}}
    (S : ShortComplex (SmallVectorBundle X)) :
    (smallVectorBundleExactStructure X).conflation S ↔
      (S.map (smallVectorBundleToSheaves X).toFunctor).ShortExact := by
  rfl

/-- Genuine scheme K-theory, formed from finite locally free sheaves and their
ambient short exact sequences in the explicitly enlarged small universe. -/
abbrev SchemeK (X : Scheme.{u}) (n : ℕ) : Type (u + 1) :=
  ExactStructure.SmallK.{u + 1} (vectorBundleExactStructure X) n

/-- The ambient sheaf inclusion induces its canonical map on K-groups.
The target is K-theory of all module sheaves, not coherent G-theory. -/
def schemeKToModuleSheafK (X : Scheme.{u}) (n : ℕ) :
    SchemeK X n →* ExactStructure.SmallK.{u + 1} (sheafExactStructure X) n :=
  (vectorBundleExactInclusion X).smallKMap n

end Quillen.SchemeSheaf
