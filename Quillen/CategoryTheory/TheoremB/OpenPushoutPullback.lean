import Quillen.CategoryTheory.TheoremB.OpenEmbeddingPushout

/-!
# Base change of genuine open-gluing pushouts

An arbitrary pullback preserves a topological pushout when both gluing maps
are open embeddings. The proof uses the resulting open cover and its actual
product-subspace pullbacks. No claim is made for general quotient pushouts.
-/
noncomputable section
open CategoryTheory Limits Topology
open scoped Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.OpenPushoutPullback
variable {A B C D X : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C}
  {g : B ⟶ D} {j : C ⟶ D}
  (sq : IsPushout i f g j) (a : X ⟶ D)

abbrev Source := {z : X × A // a z.1 = g (i z.2)}
abbrev Left := {z : X × B // a z.1 = g z.2}
abbrev Right := {z : X × C // a z.1 = j z.2}

def leftLeg : TopCat.of (Source (i := i) (g := g) a) ⟶ TopCat.of (Left (g := g) a) :=
  TopCat.ofHom ⟨fun z ↦ ⟨(z.1.1, i z.1.2), z.2⟩, by fun_prop⟩
def rightLeg : TopCat.of (Source (i := i) (g := g) a) ⟶ TopCat.of (Right (j := j) a) :=
  TopCat.ofHom ⟨fun z ↦ ⟨(z.1.1, f z.1.2), z.2.trans (ConcreteCategory.congr_hom sq.w z.1.2)⟩,
    by fun_prop⟩
def leftInclusion : TopCat.of (Left (g := g) a) ⟶ X := TopCat.pullbackFst a g
def rightInclusion : TopCat.of (Right (j := j) a) ⟶ X := TopCat.pullbackFst a j

theorem square : leftLeg (i := i) (g := g) a ≫ leftInclusion a =
    rightLeg sq a ≫ rightInclusion a := rfl

variable (hi : IsOpenEmbedding i) (hf : IsOpenEmbedding f)

/-- The left pullback is exactly the inverse image of its open chart. -/
def leftHomeomorph : Left (g := g) a ≃ₜ a ⁻¹' Set.range g :=
  TopCat.pullbackHomeoPreimage a a.hom.continuous g
    (pushout_inl_isOpenEmbedding sq hi hf).isEmbedding
/-- The right pullback is exactly the inverse image of its open chart. -/
def rightHomeomorph : Right (j := j) a ≃ₜ a ⁻¹' Set.range j :=
  TopCat.pullbackHomeoPreimage a a.hom.continuous j
    (pushout_inr_isOpenEmbedding sq hi hf).isEmbedding

include sq hi hf in
/-- Each pulled-back chart is again an actual open embedding. -/
theorem left_isOpenEmbedding : IsOpenEmbedding (leftInclusion (g := g) a) :=
  (((pushout_inl_isOpenEmbedding sq hi hf).isOpen_range.preimage a.hom.continuous).isOpenEmbedding_subtypeVal).comp (leftHomeomorph sq a hi hf).isOpenEmbedding
include sq hi hf in
theorem right_isOpenEmbedding : IsOpenEmbedding (rightInclusion (j := j) a) :=
  (((pushout_inr_isOpenEmbedding sq hi hf).isOpen_range.preimage a.hom.continuous).isOpenEmbedding_subtypeVal).comp (rightHomeomorph sq a hi hf).isOpenEmbedding

section Desc
variable {Z : TopCat.{u}} (b : TopCat.of (Left (g := g) a) ⟶ Z)
  (c : TopCat.of (Right (j := j) a) ⟶ Z)
  (h : leftLeg (i := i) (g := g) a ≫ b = rightLeg sq a ≫ c)

def leftPart : C(a ⁻¹' Set.range g, Z) := b.hom.comp ((leftHomeomorph sq a hi hf).symm : C(_, _))
def rightPart : C(a ⁻¹' Set.range j, Z) := c.hom.comp ((rightHomeomorph sq a hi hf).symm : C(_, _))

include h in
theorem parts_agree (x : X) (hx : a x ∈ Set.range g) (hy : a x ∈ Set.range j) :
    leftPart sq a hi hf b ⟨x, hx⟩ = rightPart sq a hi hf c ⟨x, hy⟩ := by
  let xb := (leftHomeomorph sq a hi hf).symm ⟨x, hx⟩
  let xc := (rightHomeomorph sq a hi hf).symm ⟨x, hy⟩
  have hb : xb.1.1 = x := rfl
  have hc : xc.1.1 = x := rfl
  have he : g xb.1.2 = j xc.1.2 := xb.2.symm.trans xc.2
  obtain ⟨y, hiy, hfy⟩ :=
    (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      (sq.map (forget TopCat)).isColimit hi.injective _ _).mp he
  change i y = xb.1.2 at hiy
  change f y = xc.1.2 at hfy
  let xy : Source (i := i) (g := g) a := ⟨(x, y), by rw [hiy]; exact xb.2⟩
  have hl : leftLeg a xy = xb := by
    apply Subtype.ext
    exact Prod.ext hb.symm hiy
  have hr : rightLeg sq a xy = xc := by
    apply Subtype.ext
    exact Prod.ext hc.symm hfy
  change b xb = c xc
  rw [← hl, ← hr]
  exact ConcreteCategory.congr_hom h xy

def coverSet (k : Bool) : Set X := if k then a ⁻¹' Set.range g else a ⁻¹' Set.range j

def parts (k : Bool) : C(coverSet (g := g) (j := j) a k, Z) := by
  cases k
  · exact rightPart sq a hi hf c
  · exact leftPart sq a hi hf b

include h in
theorem parts_compatible (k m : Bool) (x : X)
    (hk : x ∈ coverSet (g := g) (j := j) a k)
    (hm : x ∈ coverSet (g := g) (j := j) a m) :
    parts sq a hi hf b c k ⟨x, hk⟩ = parts sq a hi hf b c m ⟨x, hm⟩ := by
  cases k <;> cases m
  · rfl
  · exact (parts_agree sq a hi hf b c h x hm hk).symm
  · exact parts_agree sq a hi hf b c h x hk hm
  · rfl

include sq hi hf in
theorem coverNeighborhood (x : X) :
    ∃ k : Bool, coverSet (g := g) (j := j) a k ∈ nhds x := by
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) (a x) with hx | hx
  · exact ⟨true, ((pushout_inl_isOpenEmbedding sq hi hf).isOpen_range.preimage
      a.hom.continuous).mem_nhds hx⟩
  · exact ⟨false, ((pushout_inr_isOpenEmbedding sq hi hf).isOpen_range.preimage
      a.hom.continuous).mem_nhds hx⟩

/-- The actual continuous map glued from maps on both pulled-back charts. -/
def desc : X ⟶ Z := TopCat.ofHom (ContinuousMap.liftCover (coverSet (g := g) (j := j) a)
  (parts sq a hi hf b c) (parts_compatible sq a hi hf b c h) (coverNeighborhood sq a hi hf))

@[reassoc (attr := simp)] theorem left_desc : leftInclusion (g := g) a ≫ desc sq a hi hf b c h = b := by
  ext x
  have hh := ContinuousMap.liftCover_coe
    (φ := parts sq a hi hf b c) (hφ := parts_compatible sq a hi hf b c h)
    (hS := coverNeighborhood sq a hi hf) (i := true) (leftHomeomorph sq a hi hf x)
  change desc sq a hi hf b c h x.1.1 = b x
  exact hh.trans (congrArg b ((leftHomeomorph sq a hi hf).symm_apply_apply x))

@[reassoc (attr := simp)] theorem right_desc : rightInclusion (j := j) a ≫ desc sq a hi hf b c h = c := by
  ext x
  have hh := ContinuousMap.liftCover_coe
    (φ := parts sq a hi hf b c) (hφ := parts_compatible sq a hi hf b c h)
    (hS := coverNeighborhood sq a hi hf) (i := false) (rightHomeomorph sq a hi hf x)
  change desc sq a hi hf b c h x.1.1 = c x
  exact hh.trans (congrArg c ((rightHomeomorph sq a hi hf).symm_apply_apply x))
end Desc

include sq in
theorem hom_ext {Z : TopCat.{u}} {m n : X ⟶ Z}
    (hl : leftInclusion (g := g) a ≫ m = leftInclusion a ≫ n)
    (hr : rightInclusion (j := j) a ≫ m = rightInclusion a ≫ n) : m = n := by
  ext x
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) (a x) with ⟨b, hb⟩ | ⟨c, hc⟩
  · exact ConcreteCategory.congr_hom hl ⟨(x, b), hb.symm⟩
  · exact ConcreteCategory.congr_hom hr ⟨(x, c), hc.symm⟩

include hi hf in
/-- Base change really preserves a pushout of two open embeddings, with
its ordinary topological pullback spaces and canonical projection maps. -/
theorem isPushout : IsPushout (leftLeg (i := i) (g := g) a) (rightLeg sq a)
    (leftInclusion (g := g) a) (rightInclusion (j := j) a) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (square sq a))
  refine PushoutCocone.IsColimit.mk (square sq a)
    (fun s ↦ desc sq a hi hf s.inl s.inr s.condition)
    (fun s ↦ left_desc sq a hi hf s.inl s.inr s.condition)
    (fun s ↦ right_desc sq a hi hf s.inl s.inr s.condition) ?_
  intro s m hm₁ hm₂
  exact hom_ext sq a
    (hm₁.trans (left_desc sq a hi hf s.inl s.inr s.condition).symm)
    (hm₂.trans (right_desc sq a hi hf s.inl s.inr s.condition).symm)

end Quillen.OpenPushoutPullback
