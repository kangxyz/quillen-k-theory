import Quillen.CategoryTheory.TheoremA.RealizationPushoutCylinder
import Quillen.CategoryTheory.TheoremA.IntervalEndpoints

/-!
# Homotopy invariance of cofibrant pushouts

The initial endpoint of every mapping cylinder has HEP. Factoring an actual
homotopy equivalence through this endpoint and using the cylinder-collapse
comparison proves homotopy invariance of cobase change along an HEP map.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

universe u

namespace Quillen.TheoremA

/-- The initial endpoint of an arbitrary mapping cylinder has HEP. -/
theorem homotopyExtensionProperty_mappingCylinderStart
    {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) :
    homotopyExtensionProperty (TopCat.ι₀ ≫ l) := by
  intro Z k H hH₀
  let J : TopCat.of (A ⊕ A) ⊗ TopCat.I ⟶ Z := TopCat.ofHom
    ⟨fun p ↦ Sum.elim (fun a ↦ H (a, p.2)) (fun a ↦ k (c (f a))) p.1,
      by
        convert (H.hom.continuous.sumElim
          ((k.hom.continuous.comp (c.hom.continuous.comp f.hom.continuous)).comp
            continuous_fst)).comp Homeomorph.sumProdDistrib.continuous using 1
        ext ⟨a, t⟩
        cases a <;> rfl⟩
  have hJ₀ : TopCat.ι₀ ≫ J = intervalEndpoints A ≫ l ≫ k := by
    ext a
    cases a with
    | inl a => exact ConcreteCategory.congr_hom hH₀ a
    | inr a => exact congrArg k (ConcreteCategory.congr_hom sq.w a).symm
  obtain ⟨K, hK₀, hK⟩ := homotopyExtensionProperty_intervalEndpoints A Z (l ≫ k) J hJ₀
  have hK₁ : (TopCat.ι₁ ▷ TopCat.I) ≫ K = (f ▷ TopCat.I) ≫ fst C TopCat.I ≫ c ≫ k := by
    ext ⟨a, t⟩
    exact ConcreteCategory.congr_hom hK (Sum.inr a, t)
  let sqI := sq.map (tensorRight TopCat.I)
  let L := sqI.desc K (fst C TopCat.I ≫ c ≫ k) hK₁
  have hlL : (l ▷ TopCat.I) ≫ L = K := sqI.inl_desc _ _ _
  have hcL : (c ▷ TopCat.I) ≫ L = fst C TopCat.I ≫ c ≫ k := sqI.inr_desc _ _ _
  refine ⟨L, ?_, ?_⟩
  · apply sq.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hlL, hK₀]
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hcL,
        ← Category.assoc, TopCat.ι₀_fst, Category.id_comp]
  · rw [comp_whiskerRight, Category.assoc, hlL]
    ext ⟨a, t⟩
    exact ConcreteCategory.congr_hom hK (Sum.inl a, t)

/-- Cobase change of any actual homotopy equivalence along a map with HEP
is an actual homotopy equivalence. Its forward map is the canonical map
from the other corner into the pushout. -/
def pushoutHomotopyEquivAlongCofibration {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (hi : homotopyExtensionProperty i)
    (e : ContinuousMap.HomotopyEquiv A C) (he : e.toFun = f.hom) :
    ContinuousMap.HomotopyEquiv B D := by
  let M := pushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f
  let l : A ⊗ TopCat.I ⟶ M := pushout.inl _ _
  let c : C ⟶ M := pushout.inr _ _
  let sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c := IsPushout.of_hasPushout _ _
  let Q := pushout i (TopCat.ι₀ ≫ l)
  let b : B ⟶ Q := pushout.inl _ _
  let m : M ⟶ Q := pushout.inr _ _
  let sqQ : IsPushout i (TopCat.ι₀ ≫ l) b m := IsPushout.of_hasPushout _ _
  let e₀ := mappingCylinderStartHomotopyEquiv sqM e he
  let e₁ := pushoutHomotopyEquivOfCofibration sqQ.flip
    (homotopyExtensionProperty_mappingCylinderStart sqM) e₀ rfl
  let e₂ := mappingCylinderPushoutCollapseHomotopyEquiv sqM sqQ sq hi
  let E := e₁.trans e₂
  have hE : E.toFun = g.hom := by
    change (b ≫ sqQ.desc g (mappingCylinderProjection sqM ≫ j) _).hom = g.hom
    rw [sqQ.inl_desc]
  exact { E with
    toFun := g.hom
    left_inv := by simpa only [hE] using E.left_inv
    right_inv := by simpa only [hE] using E.right_inv }

@[simp]
theorem pushoutHomotopyEquivAlongCofibration_toFun {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (hi : homotopyExtensionProperty i)
    (e : ContinuousMap.HomotopyEquiv A C) (he : e.toFun = f.hom) :
    (pushoutHomotopyEquivAlongCofibration sq hi e he).toFun = g.hom := rfl

/-- Cancellation of a specified homotopy equivalence from the left of a
composite, retaining exactly the specified second map. -/
def homotopyEquivCancelLeft {A B C : TopCat.{u}} {a : A ⟶ B} {b : B ⟶ C}
    (e : ContinuousMap.HomotopyEquiv A B) (he : e.toFun = a.hom)
    (e' : ContinuousMap.HomotopyEquiv A C) (he' : e'.toFun = (a ≫ b).hom) :
    ContinuousMap.HomotopyEquiv B C := by
  let H := (ContinuousMap.Homotopy.refl b.hom).comp e.right_inv.some.symm
  apply homotopyEquivOfHomotopy (e.symm.trans e')
  exact H.cast (by ext; rfl) (by
    change b.hom.comp (e.toFun.comp e.invFun) = e'.toFun.comp e.invFun
    rw [he, he']
    rfl)

@[simp]
theorem homotopyEquivCancelLeft_toFun {A B C : TopCat.{u}} {a : A ⟶ B} {b : B ⟶ C}
    (e : ContinuousMap.HomotopyEquiv A B) (he : e.toFun = a.hom)
    (e' : ContinuousMap.HomotopyEquiv A C) (he' : e'.toFun = (a ≫ b).hom) :
    (homotopyEquivCancelLeft e he e' he').toFun = b.hom := rfl

/-- The homotopy gluing theorem for a map between two actual topological
pushout squares. Three homotopy-equivalence components and HEP for the
corresponding attaching legs imply that the canonical fourth component is
an actual homotopy equivalence. -/
def pushoutHomotopyEquiv
    {A B C D A' B' C' D' : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    {i' : A' ⟶ B'} {f' : A' ⟶ C'} {g' : B' ⟶ D'} {j' : C' ⟶ D'}
    (sq : IsPushout i f g j) (sq' : IsPushout i' f' g' j')
    (hi : homotopyExtensionProperty i) (hi' : homotopyExtensionProperty i')
    (ea : ContinuousMap.HomotopyEquiv A A')
    (eb : ContinuousMap.HomotopyEquiv B B')
    (ec : ContinuousMap.HomotopyEquiv C C')
    (wi : i ≫ TopCat.ofHom eb.toFun = TopCat.ofHom ea.toFun ≫ i')
    (wf : f ≫ TopCat.ofHom ec.toFun = TopCat.ofHom ea.toFun ≫ f') :
    ContinuousMap.HomotopyEquiv D D' := by
  let a : A ⟶ A' := TopCat.ofHom ea.toFun
  let b : B ⟶ B' := TopCat.ofHom eb.toFun
  let c : C ⟶ C' := TopCat.ofHom ec.toFun
  let E := pushout i a
  let be : B ⟶ E := pushout.inl _ _
  let ae : A' ⟶ E := pushout.inr _ _
  let sqE : IsPushout i a be ae := IsPushout.of_hasPushout _ _
  let x : E ⟶ B' := sqE.desc b i' wi
  have hbx : be ≫ x = b := sqE.inl_desc _ _ _
  have hax : ae ≫ x = i' := sqE.inr_desc _ _ _
  let ebe := pushoutHomotopyEquivAlongCofibration sqE hi ea rfl
  let ex := homotopyEquivCancelLeft ebe rfl eb (by
    change eb.toFun = (be ≫ x).hom
    rw [hbx]
    rfl)
  let P := pushout i (f ≫ c)
  let bp : B ⟶ P := pushout.inl _ _
  let cp : C' ⟶ P := pushout.inr _ _
  let sqP : IsPushout i (f ≫ c) bp cp := IsPushout.of_hasPushout _ _
  have sqPa : IsPushout i (a ≫ f') bp cp := by
    have wf' : f ≫ c = a ≫ f' := wf
    rw [← wf']
    exact sqP
  let ep : E ⟶ P := sqE.desc bp (f' ≫ cp) (by rw [← Category.assoc, ← wf, sqP.w])
  have hbep : be ≫ ep = bp := sqE.inl_desc _ _ _
  have haep : ae ≫ ep = f' ≫ cp := sqE.inr_desc _ _ _
  have sqEP : IsPushout ae f' ep cp := by
    apply IsPushout.of_top _ haep sqE
    simpa only [hbep] using sqPa
  let d : D ⟶ P := sq.desc bp (c ≫ cp) (by rw [← Category.assoc, sqP.w])
  have hgd : g ≫ d = bp := sq.inl_desc _ _ _
  have hjd : j ≫ d = c ≫ cp := sq.inr_desc _ _ _
  have sqDP : IsPushout j c d cp := by
    apply IsPushout.of_top _ hjd sq
    simpa only [hgd] using sqP
  let ed := pushoutHomotopyEquivAlongCofibration sqDP
    (homotopyExtensionProperty_pushout sq hi) ec rfl
  let ey := pushoutHomotopyEquivOverBase sqEP sq'
    (homotopyExtensionProperty_pushout sqE hi) hi' ex hax
  let y : P ⟶ D' := TopCat.ofHom ey.toFun
  have hepy : ep ≫ y = x ≫ g' := sqEP.inl_desc _ _ _
  have hcpy : cp ≫ y = j' := sqEP.inr_desc _ _ _
  have hw : i ≫ b ≫ g' = f ≫ c ≫ j' := by
    rw [← Category.assoc i b, wi, Category.assoc, sq'.w,
      ← Category.assoc a f', ← wf, Category.assoc]
  let q : D ⟶ D' := sq.desc (b ≫ g') (c ≫ j') hw
  have hdq : d ≫ y = q := by
    apply sq.hom_ext
    · rw [← Category.assoc, hgd, ← hbep, Category.assoc, hepy,
        ← Category.assoc, hbx]
      exact (sq.inl_desc _ _ _).symm
    · rw [← Category.assoc, hjd, Category.assoc, hcpy]
      exact (sq.inr_desc _ _ _).symm
  let et := ed.trans ey
  have het : et.toFun = q.hom := congrArg TopCat.Hom.hom hdq
  exact { et with
    toFun := q.hom
    left_inv := by simpa only [het] using et.left_inv
    right_inv := by simpa only [het] using et.right_inv }

@[reassoc (attr := simp)]
theorem pushoutHomotopyEquiv_inl
    {A B C D A' B' C' D' : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    {i' : A' ⟶ B'} {f' : A' ⟶ C'} {g' : B' ⟶ D'} {j' : C' ⟶ D'}
    (sq : IsPushout i f g j) (sq' : IsPushout i' f' g' j')
    (hi : homotopyExtensionProperty i) (hi' : homotopyExtensionProperty i')
    (ea : ContinuousMap.HomotopyEquiv A A')
    (eb : ContinuousMap.HomotopyEquiv B B')
    (ec : ContinuousMap.HomotopyEquiv C C')
    (wi : i ≫ TopCat.ofHom eb.toFun = TopCat.ofHom ea.toFun ≫ i')
    (wf : f ≫ TopCat.ofHom ec.toFun = TopCat.ofHom ea.toFun ≫ f') :
    g ≫ TopCat.ofHom (pushoutHomotopyEquiv sq sq' hi hi' ea eb ec wi wf).toFun =
      TopCat.ofHom eb.toFun ≫ g' := sq.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem pushoutHomotopyEquiv_inr
    {A B C D A' B' C' D' : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    {i' : A' ⟶ B'} {f' : A' ⟶ C'} {g' : B' ⟶ D'} {j' : C' ⟶ D'}
    (sq : IsPushout i f g j) (sq' : IsPushout i' f' g' j')
    (hi : homotopyExtensionProperty i) (hi' : homotopyExtensionProperty i')
    (ea : ContinuousMap.HomotopyEquiv A A')
    (eb : ContinuousMap.HomotopyEquiv B B')
    (ec : ContinuousMap.HomotopyEquiv C C')
    (wi : i ≫ TopCat.ofHom eb.toFun = TopCat.ofHom ea.toFun ≫ i')
    (wf : f ≫ TopCat.ofHom ec.toFun = TopCat.ofHom ea.toFun ≫ f') :
    j ≫ TopCat.ofHom (pushoutHomotopyEquiv sq sq' hi hi' ea eb ec wi wf).toFun =
      TopCat.ofHom ec.toFun ≫ j' := sq.inr_desc _ _ _

/-- A formulation of homotopy gluing for four specified vertical maps.
The equivalences are required to represent the actual three component
maps, and the constructed equivalence represents the actual fourth map. -/
def pushoutHomotopyEquivOfMap
    {A B C D A' B' C' D' : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    {i' : A' ⟶ B'} {f' : A' ⟶ C'} {g' : B' ⟶ D'} {j' : C' ⟶ D'}
    (sq : IsPushout i f g j) (sq' : IsPushout i' f' g' j')
    (hi : homotopyExtensionProperty i) (hi' : homotopyExtensionProperty i')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (wi : i ≫ b = a ≫ i') (wf : f ≫ c = a ≫ f')
    (wg : g ≫ d = b ≫ g') (wj : j ≫ d = c ≫ j')
    (ea : ContinuousMap.HomotopyEquiv A A') (ha : ea.toFun = a.hom)
    (eb : ContinuousMap.HomotopyEquiv B B') (hb : eb.toFun = b.hom)
    (ec : ContinuousMap.HomotopyEquiv C C') (hc : ec.toFun = c.hom) :
    ContinuousMap.HomotopyEquiv D D' := by
  have hai : TopCat.ofHom ea.toFun = a := by rw [ha]; rfl
  have hbi : TopCat.ofHom eb.toFun = b := by rw [hb]; rfl
  have hci : TopCat.ofHom ec.toFun = c := by rw [hc]; rfl
  let E := pushoutHomotopyEquiv sq sq' hi hi' ea eb ec
    (by simpa only [hai, hbi] using wi) (by simpa only [hai, hci] using wf)
  have hE : TopCat.ofHom E.toFun = d := by
    apply sq.hom_ext
    · rw [pushoutHomotopyEquiv_inl, hbi, wg]
    · rw [pushoutHomotopyEquiv_inr, hci, wj]
  have hE' : E.toFun = d.hom := congrArg TopCat.Hom.hom hE
  exact { E with
    toFun := d.hom
    left_inv := by simpa only [hE'] using E.left_inv
    right_inv := by simpa only [hE'] using E.right_inv }

@[simp]
theorem pushoutHomotopyEquivOfMap_toFun
    {A B C D A' B' C' D' : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    {i' : A' ⟶ B'} {f' : A' ⟶ C'} {g' : B' ⟶ D'} {j' : C' ⟶ D'}
    (sq : IsPushout i f g j) (sq' : IsPushout i' f' g' j')
    (hi : homotopyExtensionProperty i) (hi' : homotopyExtensionProperty i')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (wi : i ≫ b = a ≫ i') (wf : f ≫ c = a ≫ f')
    (wg : g ≫ d = b ≫ g') (wj : j ≫ d = c ≫ j')
    (ea : ContinuousMap.HomotopyEquiv A A') (ha : ea.toFun = a.hom)
    (eb : ContinuousMap.HomotopyEquiv B B') (hb : eb.toFun = b.hom)
    (ec : ContinuousMap.HomotopyEquiv C C') (hc : ec.toFun = c.hom) :
    (pushoutHomotopyEquivOfMap sq sq' hi hi' a b c d wi wf wg wj ea ha eb hb ec hc).toFun =
      d.hom := rfl

end Quillen.TheoremA
