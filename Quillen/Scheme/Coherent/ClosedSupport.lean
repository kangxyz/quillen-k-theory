import Quillen.Scheme.Coherent.Restriction
import Quillen.Scheme.Sheaf.AffineSupport

/-!
# Closed stalk support of actual global coherent sheaves

Finite global sections on each actual affine chart give closed support on
that chart. Since affine open charts cover the scheme, the ordinary global
stalk support is closed. This is proved directly from the affine-local
condition, without a global finiteness or separatedness hypothesis.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Quillen.CoherentScheme

/-- The ordinary stalk support of a sheaf satisfying the actual affine-local
finite quasicoherent condition is closed. -/
theorem isClosed_support_of_coherent {X : Scheme.{u}} {M : X.Modules} (hM : coherent X M) :
    IsClosed (SchemeSheaf.support M) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  let i := X.affineOpenCover.idx x
  let j := X.affineOpenCover.f i
  obtain ⟨y, hy⟩ := X.affineOpenCover.covers x
  have hC := hM (X.affineOpenCover.X i) j
  have : ((Scheme.Modules.restrictFunctor j).obj M).IsQuasicoherent := hC.1
  have : Module.Finite (X.affineOpenCover.X i)
      (moduleSpecΓFunctor.obj ((Scheme.Modules.restrictFunctor j).obj M)) := hC.2
  have hc : IsClosed (j ⁻¹' SchemeSheaf.support M) := by
    rw [← SchemeSheaf.support_restrict j M]
    exact SchemeSheaf.isClosed_support_of_finite_globalSections _
  have ho : IsOpen (j '' (j ⁻¹' SchemeSheaf.support M)ᶜ) :=
    j.isOpenEmbedding.isOpenMap _ hc.isOpen_compl
  apply Filter.mem_of_superset (ho.mem_nhds ?_) ?_
  · refine ⟨y, ?_, hy⟩
    change j y ∉ SchemeSheaf.support M
    rw [show j y = x from hy]
    exact hx
  · rintro z ⟨w, hw, rfl⟩
    exact hw

/-- Global coherent sheaf objects have ordinary closed support. -/
theorem coherent_support_isClosed {X : Scheme.{u}} [IsLocallyNoetherian X] (M : Coherent X) :
    IsClosed (SchemeSheaf.support M.obj) := isClosed_support_of_coherent M.property

end Quillen.CoherentScheme
