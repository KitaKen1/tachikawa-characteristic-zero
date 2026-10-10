import OAI.RingTheory.Tachikawa.GenericCoinduction

/-! Characteristic-independent excerpts from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; source files, exact line ranges and hashes are
recorded in vendor/openai-math/manifest.json. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

lemma ext_subsingleton_retract_left {X X' Y : C} (r : Retract X X') (n : ℕ)
    [Subsingleton (Ext X' Y n)] : Subsingleton (Ext X Y n) := by
  have hz (x : Ext X Y n) : x = 0 := by
    have h : (Ext.mk₀ r.r).comp x (zero_add n) = 0 := Subsingleton.elim _ _
    have h' := congrArg (fun z => (Ext.mk₀ r.i).comp z (zero_add n)) h
    simpa only [Ext.mk₀_comp_mk₀_assoc, r.retract, Ext.mk₀_id_comp, Ext.comp_zero] using h'
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

lemma ext_subsingleton_retract_right {X Y Y' : C} (r : Retract Y Y') (n : ℕ)
    [Subsingleton (Ext X Y' n)] : Subsingleton (Ext X Y n) := by
  have hz (x : Ext X Y n) : x = 0 := by
    have h : x.comp (Ext.mk₀ r.i) (add_zero n) = 0 := Subsingleton.elim _ _
    have h' := congrArg (fun z => z.comp (Ext.mk₀ r.r) (add_zero n)) h
    simpa only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      r.retract, Ext.comp_mk₀_id, Ext.zero_comp] using h'
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

def InAdd (W V : C) : Prop := ∃ n : ℕ, Nonempty (Retract V (⨁ fun _ : Fin n => W))

lemma ext_subsingleton_inAdd_left {W V Y : C} (h : InAdd W V) (n : ℕ)
    [Subsingleton (Ext W Y n)] : Subsingleton (Ext V Y n) := by
  obtain ⟨d,⟨r⟩⟩ := h
  let : Subsingleton (Ext (⨁ fun _ : Fin d => W) Y n) :=
    (Ext.biproductAddEquiv (biproduct.isBilimit _) Y n).injective.subsingleton
  exact ext_subsingleton_retract_left r n

lemma ext_subsingleton_inAdd_right {W V X : C} (h : InAdd W V) (n : ℕ)
    [Subsingleton (Ext X W n)] : Subsingleton (Ext X V n) := by
  obtain ⟨d,⟨r⟩⟩ := h
  let : Subsingleton (Ext X (⨁ fun _ : Fin d => W) n) :=
    (Ext.addEquivBiproduct X (biproduct.isBilimit _) n).injective.subsingleton
  exact ext_subsingleton_retract_right r n

end Tachikawa


namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt C]

lemma projective_dimension_of_bounded_resolution {X : C} (P : ProjectiveResolution X)
    (d : ℕ) (h : ∀ n, d < n → IsZero (P.complex.X n)) :
    HasProjectiveDimensionLE X d := by
  apply HasProjectiveDimensionLT.mk
  intro n hn Y e
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let : Subsingleton (Ext X Y (m+1)) := ext_subsingleton_of_boundaries P m (by
    intro f hf
    refine ⟨0, ?_⟩
    rw [comp_zero]
    exact (h (m+1) (by omega)).eq_of_src 0 f)
  exact Subsingleton.elim _ _

lemma InAdd.projectiveDimension {W V : C} (h : InAdd W V) (n : ℕ)
    [HasProjectiveDimensionLT W n] : HasProjectiveDimensionLT V n := by
  apply HasProjectiveDimensionLT.mk
  intro i hi Y e
  let := HasProjectiveDimensionLT.subsingleton W n i hi Y
  let := ext_subsingleton_inAdd_left h i (Y := Y)
  exact Subsingleton.elim _ _

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
universe u v w t
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} {D : Type w} [Category.{v} C] [Category.{t} D] [Abelian C] [Abelian D]

lemma InAdd.map (F : C ⥤ D) [F.Additive] {W V : C} (h : InAdd W V) :
    InAdd (F.obj W) (F.obj V) := by
  obtain ⟨n,⟨r⟩⟩ := h
  exact ⟨n,⟨(r.map F).trans (F.mapBiproduct (fun _ : Fin n => W)).retract⟩⟩

lemma InAdd.iso {W V V' : C} (h : InAdd W V) (e : V' ≅ V) : InAdd W V' := by
  obtain ⟨n,⟨r⟩⟩ := h
  exact ⟨n,⟨e.retract.trans r⟩⟩

lemma InAdd.retract {W V V' : C} (h : InAdd W V) (r : Retract V' V) : InAdd W V' := by
  obtain ⟨n,⟨r'⟩⟩ := h
  exact ⟨n,⟨r.trans r'⟩⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
attribute [local instance] Abelian.hasFiniteBiproducts
variable {R : Type} [Ring R]

lemma finiteProjective_inAdd (M : ModuleCat R) [Module.Finite R M] [Module.Projective R M] :
    InAdd (ModuleCat.of R R) M := by
  let c := finiteFreeCover (R := R) (M := M)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let e := ModuleCat.biproductIsoPi (fun _ : Fin c.rank => ModuleCat.of R R)
  refine ⟨c.rank,⟨{ i := ModuleCat.ofHom i ≫ e.inv, r := e.hom ≫ ModuleCat.ofHom c.map, retract := ?_ }⟩⟩
  rw [Category.assoc,← Category.assoc e.inv,e.inv_hom_id,Category.id_comp]
  exact ModuleCat.hom_ext hi

end Tachikawa


namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma InAdd.trans {W V X : C} (h : InAdd W V) (h' : InAdd V X) : InAdd W X := by
  classical
  obtain ⟨n,⟨r⟩⟩ := h
  obtain ⟨m,⟨s⟩⟩ := h'
  let t : Retract (⨁ fun _ : Fin m => V) (⨁ fun _ : Fin m => ⨁ fun _ : Fin n => W) :=
    { i := biproduct.map (fun _ => r.i)
      r := biproduct.map (fun _ => r.r)
      retract := by
        apply biproduct.hom_ext
        intro j
        simp only [Category.assoc,biproduct.map_π,biproduct.map_π_assoc,Category.id_comp,
          r.retract,Category.comp_id] }
  let e := biproductBiproductIso (fun _ : Fin m => Fin n) (fun _ _ => W)
  let d := biproduct.whiskerEquiv (f := fun _ : Σ _ : Fin m, Fin n => W)
    (g := fun _ : Fin (Fintype.card (Σ _ : Fin m, Fin n)) => W)
    (Fintype.equivFin _) (fun _ => Iso.refl _)
  exact ⟨_,⟨s.trans (t.trans (e.retract.trans d.retract))⟩⟩

end Tachikawa


namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma InAdd.biproduct {W : C} {ι : Type} [Fintype ι] (V : ι → C)
    (h : ∀ i, InAdd W (V i)) : InAdd W (⨁ V) := by
  classical
  choose n r using h
  let s (i : ι) := (r i).some
  let t : Retract (⨁ V) (⨁ fun i : ι => ⨁ fun _ : Fin (n i) => W) :=
    { i := biproduct.map (fun i => (s i).i)
      r := biproduct.map (fun i => (s i).r)
      retract := by
        apply biproduct.hom_ext
        intro j
        simp only [Category.assoc,biproduct.map_π,biproduct.map_π_assoc,Category.id_comp,
          (s j).retract,Category.comp_id] }
  let e := biproductBiproductIso (fun i : ι => Fin (n i)) (fun _ _ => W)
  let d := biproduct.whiskerEquiv (f := fun _ : Σ i : ι, Fin (n i) => W)
    (g := fun _ : Fin (Fintype.card (Σ i : ι, Fin (n i))) => W)
    (Fintype.equivFin _) (fun _ => Iso.refl _)
  exact ⟨_,⟨t.trans (e.retract.trans d.retract)⟩⟩

lemma InAdd.biprod {W X Y : C} (hX : InAdd W X) (hY : InAdd W Y) :
    InAdd W (X ⊞ Y) := by
  have h : ∀ i, InAdd W (pairFunction X Y i) := by
    intro i
    cases i
    · exact hX
    · exact hY
  let e := biprod.uniqueUpToIso X Y
    ((Bicone.toBinaryBiconeIsBilimit _).symm (biproduct.isBilimit (pairFunction X Y)))
  exact (InAdd.biproduct _ h).iso e.symm

end Tachikawa


end
end OAI
