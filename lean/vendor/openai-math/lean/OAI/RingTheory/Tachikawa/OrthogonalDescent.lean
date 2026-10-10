import OAI.RingTheory.Tachikawa.AdditiveClosure

/-! Characteristic-independent excerpts from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; source files, exact line ranges and hashes are
recorded in vendor/openai-math/manifest.json. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

lemma kProjective_chain_representative (K L : CochainComplex C ℤ) [K.IsKProjective]
    (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, DerivedCategory.Q.map f = a := by
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨b,hb⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C (.up ℤ)).obj L)).surjective
      ((e.app K).hom ≫ a ≫ (e.app L).inv)
  obtain ⟨f,rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective b
  refine ⟨f,?_⟩
  have ht := congrArg (fun t => (e.app K).inv ≫ t ≫ (e.app L).hom) hb
  change e.inv.app K ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫ e.hom.app L =
    e.inv.app K ≫ (e.hom.app K ≫ a ≫ e.inv.app L) ≫ e.hom.app L at ht
  simpa [e] using ht

end Tachikawa


namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C]
variable {K L : CochainComplex C ℤ}

def HomColumnBoundaries (K L : CochainComplex C ℤ) : Prop :=
  ∀ (n : ℕ) (a : K.X (-(n+1 : ℤ)) ⟶ L.X (-(n+1 : ℤ))),
    K.d (-(n+2 : ℤ)) (-(n+1 : ℤ)) ≫ a = 0 →
    ∃ b : K.X (-(n : ℤ)) ⟶ L.X (-(n+1 : ℤ)),
      K.d (-(n+1 : ℤ)) (-(n : ℤ)) ≫ b = a

lemma raise_cochain_map (n : ℕ) (f : K ⟶ L)
    (hf : ∀ j, j < -(n+1 : ℤ) → f.f j = 0) (hb : HomColumnBoundaries K L) :
    ∃ f' : K ⟶ L, (∀ j, j < -(n : ℤ) → f'.f j = 0) ∧ Nonempty (Homotopy f f') := by
  classical
  have hc : K.d (-(n+2 : ℤ)) (-(n+1 : ℤ)) ≫ f.f (-(n+1 : ℤ)) = 0 := by
    rw [← f.comm, hf _ (by omega), zero_comp]
  obtain ⟨g,hg⟩ := hb n (f.f (-(n+1 : ℤ))) hc
  let h : ∀ i j, K.X i ⟶ L.X j := fun i j =>
    if hi : i = -(n : ℤ) then if hj : j = -(n+1 : ℤ) then
      eqToHom (congrArg K.X hi) ≫ g ≫ eqToHom (congrArg L.X hj.symm)
      else 0 else 0
  have hh : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → h i j = 0 := by
    intro i j hij
    dsimp only [h]
    split_ifs with hi hj
    · subst i; subst j
      exact False.elim (hij (by change -(n+1 : ℤ)+1= -(n : ℤ); omega))
    all_goals rfl
  let z := Homotopy.nullHomotopicMap h
  have hz (j : ℤ) : z.f j = K.d j (j+1) ≫ h (j+1) j + h j (j-1) ≫ L.d (j-1) j :=
    Homotopy.nullHomotopicMap_f (by change j-1+1=j; omega) rfl h
  refine ⟨f-z, ?_, ?_⟩
  · intro j hj
    change f.f j - z.f j = 0
    rw [hz]
    have h1 : j ≠ -(n : ℤ) := by omega
    by_cases h2 : j = -(n+1 : ℤ)
    · subst j
      have hi : -(n+1 : ℤ)+1= -(n : ℤ) := by omega
      rw [hi]
      simp only [h, dite_eq_left rfl, eqToHom_refl, Category.id_comp, Category.comp_id,
        dite_eq_right h1, zero_comp, add_zero, hg, sub_self]
    · have h3 : j+1 ≠ -(n : ℤ) := by omega
      simp only [h, dite_eq_right h1, dite_eq_right h3, comp_zero, zero_comp, add_zero,
        hf j (by omega), sub_self]
  · apply Nonempty.intro
    refine Homotopy.equivSubZero.symm ?_
    have he : f-(f-z)=z := by abel
    rw [he]
    exact Homotopy.nullHomotopy h hh

theorem cochain_map_supported_nonnegative (N : ℕ) (f : K ⟶ L)
    (hf : ∀ j, j < -(N : ℤ) → f.f j = 0) (hb : HomColumnBoundaries K L) :
    ∃ f' : K ⟶ L, (∀ j, j < 0 → f'.f j = 0) ∧ Nonempty (Homotopy f f') := by
  induction N generalizing f with
  | zero => exact ⟨f,by simpa using hf,⟨Homotopy.refl f⟩⟩
  | succ N ih =>
    obtain ⟨g,hg,⟨H⟩⟩ := raise_cochain_map N f (by simpa using hf) hb
    obtain ⟨f',hf',⟨H'⟩⟩ := ih g hg
    exact ⟨f',hf',⟨H.trans H'⟩⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C]
variable {X : C} (P : ProjectiveResolution X) (L : CochainComplex C ℤ)

lemma resolution_HomColumnBoundaries
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext X (L.X (-(n+1 : ℤ))) (n+1))) :
    HomColumnBoundaries (P.complex.extend ComplexShape.embeddingDownNat) L := by
  intro n a ha
  let e (j : ℕ) := P.complex.extendXIso ComplexShape.embeddingDownNat
    (i := j) (i' := -(j : ℤ)) rfl
  have d (i j : ℕ) : (P.complex.extend ComplexShape.embeddingDownNat).d (-(i : ℤ)) (-(j : ℤ)) =
      (e i).hom ≫ P.complex.d i j ≫ (e j).inv :=
    P.complex.extend_d_eq ComplexShape.embeddingDownNat rfl rfl
  have he1 : -(↑(n+1) : ℤ) = -(n+1 : ℤ) := by push_cast; rfl
  have he2 : -(↑(n+2) : ℤ) = -(n+2 : ℤ) := by push_cast; rfl
  let e1 : (P.complex.extend ComplexShape.embeddingDownNat).X (-(n+1 : ℤ)) ≅ P.complex.X (n+1) :=
    eqToIso (congrArg _ he1.symm) ≪≫ e (n+1)
  let e2 : (P.complex.extend ComplexShape.embeddingDownNat).X (-(n+2 : ℤ)) ≅ P.complex.X (n+2) :=
    eqToIso (congrArg _ he2.symm) ≪≫ e (n+2)
  have hd1 : (P.complex.extend ComplexShape.embeddingDownNat).d (-(n+2 : ℤ)) (-(n+1 : ℤ)) =
      e2.hom ≫ P.complex.d (n+2) (n+1) ≫ e1.inv := by
    simpa [e1,e2,he1,he2] using d (n+2) (n+1)
  have hd0 : (P.complex.extend ComplexShape.embeddingDownNat).d (-(n+1 : ℤ)) (-(n : ℤ)) =
      e1.hom ≫ P.complex.d (n+1) n ≫ (e n).inv := by
    simpa [e1,he1] using d (n+1) n
  have ha' : P.complex.d (n+2) (n+1) ≫ e1.inv ≫ a = 0 := by
    have hs := congrArg (fun t => e2.inv ≫ t) ha
    simpa only [hd1, Category.assoc, Iso.inv_hom_id_assoc, comp_zero] using hs
  let := hExt n
  obtain ⟨b,hb⟩ := boundaries_of_ext_subsingleton P n (e1.inv ≫ a) ha'
  refine ⟨(e n).hom ≫ b, ?_⟩
  rw [hd0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hb, Iso.hom_inv_id_assoc]

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C]
variable {X : C} (P : ProjectiveResolution X) {L : CochainComplex C ℤ}

theorem bounded_cochain_resolution_descends (N : ℕ) (f : P.cochainComplex ⟶ L)
    (hL : ∀ j, j < -(N : ℤ) → IsZero (L.X j))
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext X (L.X (-(n+1 : ℤ))) (n+1))) :
    ∃ g : (CochainComplex.singleFunctor C 0).obj X ⟶ L,
      Nonempty (Homotopy f (P.π' ≫ g)) := by
  obtain ⟨f',hf',H⟩ := cochain_map_supported_nonnegative N f
    (fun j hj => (hL j hj).eq_of_tgt _ _)
    (resolution_HomColumnBoundaries P L hExt)
  let e0 := P.cochainComplexXIso 0 0 rfl
  let e1 := P.cochainComplexXIso (-1) 1 rfl
  have hc : P.cochainComplex.d (-1) 0 ≫ f'.f 0 = 0 := by
    rw [← f'.comm, hf' (-1) (by omega), zero_comp]
  have hc' : P.complex.d 1 0 ≫ e0.inv ≫ f'.f 0 = 0 := by
    have hs := congrArg (fun t => e1.inv ≫ t) hc
    rw [P.cochainComplex_d (-1) 0 1 0 rfl rfl] at hs
    simpa only [e0,e1,Category.assoc, Iso.inv_hom_id_assoc, comp_zero] using hs
  let s : CokernelCofork (P.complex.d 1 0) := CokernelCofork.ofπ (e0.inv ≫ f'.f 0) hc'
  let a : X ⟶ L.X 0 := P.isColimitCokernelCofork.desc s
  have ha : P.π.f 0 ≫ a = e0.inv ≫ f'.f 0 :=
    P.isColimitCokernelCofork.fac s WalkingParallelPair.one
  have hd : P.cochainComplex.d 0 1 = 0 :=
    (CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 1).eq_of_tgt _ _
  have hca : ∀ j, (ComplexShape.up ℤ).Rel 0 j → a ≫ L.d 0 j = 0 := by
    intro j hj
    have hj' : j=1 := by change 0+1=j at hj; omega
    rw [hj']
    apply (cancel_epi (P.π.f 0)).1
    erw [← Category.assoc, ha, Category.assoc, f'.comm]
    change e0.inv ≫ P.cochainComplex.d 0 1 ≫ f'.f 1 = P.π.f 0 ≫ 0
    rw [hd,zero_comp,comp_zero,comp_zero]
  let g : (CochainComplex.singleFunctor C 0).obj X ⟶ L := mkHomFromSingle a hca
  have he : P.π' ≫ g = f' := by
    apply HomologicalComplex.Hom.ext
    funext j
    by_cases hj : j=0
    · subst j
      simp only [comp_f, g, mkHomFromSingle_f, P.π'_f_zero, Category.assoc]
      erw [Category.assoc, Iso.inv_hom_id_assoc, ha]
      simp only [e0, Iso.hom_inv_id_assoc]
    · by_cases hneg : j<0
      · rw [comp_f, hf' j hneg]
        have hp : P.π'.f j = 0 :=
          (isZero_single_obj_X (ComplexShape.up ℤ) 0 X j hj).eq_of_tgt _ _
        rw [hp,zero_comp]
      · exact (CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 j (by omega)).eq_of_src _ _
  exact ⟨g, he.symm ▸ H⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C] [HasDerivedCategory C]
variable {X : C} (P : ProjectiveResolution X) (L : CochainComplex C ℤ)

theorem bounded_orthogonal_derived_descent (P : ProjectiveResolution X) (N : ℕ)
    (hL : ∀ j, j < -(N : ℤ) → IsZero (L.X j))
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext X (L.X (-(n+1 : ℤ))) (n+1)))
    (a : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶
      DerivedCategory.Q.obj L) :
    ∃ g : (CochainComplex.singleFunctor C 0).obj X ⟶ L,
      DerivedCategory.Q.map g = a := by
  obtain ⟨f,hf⟩ := kProjective_chain_representative P.cochainComplex L
    (DerivedCategory.Q.map P.π' ≫ a)
  obtain ⟨g,⟨H⟩⟩ := bounded_cochain_resolution_descends P N f hL hExt
  refine ⟨g, (cancel_epi (DerivedCategory.Q.map P.π')).1 ?_⟩
  rw [← Functor.map_comp, ← DerivedCategory.Q_map_eq_of_homotopy C H, hf]

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C]
variable {K L : CochainComplex C ℤ}

def HomRowBoundaries (K L : CochainComplex C ℤ) : Prop :=
  ∀ (n : ℕ) (a : K.X (n+1 : ℤ) ⟶ L.X (n+1 : ℤ)),
    a ≫ L.d (n+1 : ℤ) (n+2 : ℤ) = 0 →
    ∃ b : K.X (n+1 : ℤ) ⟶ L.X (n : ℤ),
      b ≫ L.d (n : ℤ) (n+1 : ℤ) = a

lemma lower_cochain_map (n : ℕ) (f : K ⟶ L)
    (hf : ∀ j, (n+1 : ℤ) < j → f.f j = 0) (hb : HomRowBoundaries K L) :
    ∃ f' : K ⟶ L, (∀ j, (n : ℤ) < j → f'.f j = 0) ∧ Nonempty (Homotopy f f') := by
  classical
  have hc : f.f (n+1 : ℤ) ≫ L.d (n+1 : ℤ) (n+2 : ℤ) = 0 := by
    rw [f.comm, hf _ (by omega), comp_zero]
  obtain ⟨g,hg⟩ := hb n (f.f (n+1 : ℤ)) hc
  let h : ∀ i j, K.X i ⟶ L.X j := fun i j =>
    if hi : i = (n+1 : ℤ) then if hj : j = (n : ℤ) then
      eqToHom (congrArg K.X hi) ≫ g ≫ eqToHom (congrArg L.X hj.symm)
      else 0 else 0
  have hh : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → h i j = 0 := by
    intro i j hij
    dsimp only [h]
    split_ifs with hi hj
    · subst i; subst j
      exact False.elim (hij (by rfl))
    all_goals rfl
  let z := Homotopy.nullHomotopicMap h
  have hz (j : ℤ) : z.f j = K.d j (j+1) ≫ h (j+1) j + h j (j-1) ≫ L.d (j-1) j :=
    Homotopy.nullHomotopicMap_f (by change j-1+1=j; omega) rfl h
  refine ⟨f-z, ?_, ?_⟩
  · intro j hj
    change f.f j - z.f j = 0
    rw [hz]
    have h1 : j+1 ≠ (n+1 : ℤ) := by omega
    by_cases h2 : j = (n+1 : ℤ)
    · subst j
      have hi : (n+1 : ℤ)-1= (n : ℤ) := by omega
      rw [hi]
      simp only [h, dite_eq_left rfl, eqToHom_refl, Category.id_comp, Category.comp_id,
        dite_eq_right h1, comp_zero, zero_add, hg, sub_self]
    · simp only [h, dite_eq_right h1, dite_eq_right h2, comp_zero, zero_comp, add_zero,
        hf j (by omega), sub_self]
  · apply Nonempty.intro
    refine Homotopy.equivSubZero.symm ?_
    have he : f-(f-z)=z := by abel
    rw [he]
    exact Homotopy.nullHomotopy h hh

theorem cochain_map_supported_nonpositive (N : ℕ) (f : K ⟶ L)
    (hf : ∀ j, (N : ℤ) < j → f.f j = 0) (hb : HomRowBoundaries K L) :
    ∃ f' : K ⟶ L, (∀ j, 0 < j → f'.f j = 0) ∧ Nonempty (Homotopy f f') := by
  induction N generalizing f with
  | zero => exact ⟨f,by simpa using hf,⟨Homotopy.refl f⟩⟩
  | succ N ih =>
    obtain ⟨g,hg,⟨H⟩⟩ := lower_cochain_map N f (by simpa using hf) hb
    obtain ⟨f',hf',⟨H'⟩⟩ := ih g hg
    exact ⟨f',hf',⟨H.trans H'⟩⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C]
variable {Y : C} (R : InjectiveResolution Y) (K : CochainComplex C ℤ)

lemma coresolution_HomRowBoundaries
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext (K.X (n+1 : ℤ)) Y (n+1))) :
    HomRowBoundaries K R.cochainComplex := by
  intro n a ha
  let e (j : ℕ) := R.cochainComplexXIso (j : ℤ) j rfl
  have he1 : (↑(n+1) : ℤ) = (n+1 : ℤ) := by push_cast; rfl
  have he2 : (↑(n+2) : ℤ) = (n+2 : ℤ) := by push_cast; rfl
  let e1 : R.cochainComplex.X (n+1 : ℤ) ≅ R.cocomplex.X (n+1) :=
    eqToIso (congrArg _ he1.symm) ≪≫ e (n+1)
  let e2 : R.cochainComplex.X (n+2 : ℤ) ≅ R.cocomplex.X (n+2) :=
    eqToIso (congrArg _ he2.symm) ≪≫ e (n+2)
  have hd1 : R.cochainComplex.d (n+1 : ℤ) (n+2 : ℤ) =
      e1.hom ≫ R.cocomplex.d (n+1) (n+2) ≫ e2.inv := by
    simpa [e1,e2,e,he1,he2] using R.cochainComplex_d (n+1 : ℤ) (n+2 : ℤ) (n+1) (n+2) he1 he2
  have hd0 : R.cochainComplex.d (n : ℤ) (n+1 : ℤ) =
      (e n).hom ≫ R.cocomplex.d n (n+1) ≫ e1.inv := by
    simpa [e1,e,he1] using R.cochainComplex_d (n : ℤ) (n+1 : ℤ) n (n+1) rfl he1
  have ha' : (a ≫ e1.hom) ≫ R.cocomplex.d (n+1) (n+2) = 0 := by
    have hs := congrArg (fun t => t ≫ e2.hom) ha
    simpa only [hd1, Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using hs
  let := hExt n
  obtain ⟨b,hb⟩ := (R.extMk_eq_zero_iff (a ≫ e1.hom) (n+2) rfl ha' n rfl).mp
    (Subsingleton.elim _ 0)
  refine ⟨b ≫ (e n).inv, ?_⟩
  rw [hd0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C]
variable {Y : C} (R : InjectiveResolution Y) {K : CochainComplex C ℤ}

theorem bounded_cochain_coresolution_descends (N : ℕ) (f : K ⟶ R.cochainComplex)
    (hK : ∀ j, (N : ℤ) < j → IsZero (K.X j))
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext (K.X (n+1 : ℤ)) Y (n+1))) :
    ∃ g : K ⟶ (CochainComplex.singleFunctor C 0).obj Y,
      Nonempty (Homotopy f (g ≫ R.ι')) := by
  obtain ⟨f',hf',H⟩ := cochain_map_supported_nonpositive N f
    (fun j hj => (hK j hj).eq_of_src _ _)
    (coresolution_HomRowBoundaries R K hExt)
  let e0 := R.cochainComplexXIso 0 0 rfl
  let e1 := R.cochainComplexXIso 1 1 rfl
  have hc : f'.f 0 ≫ R.cochainComplex.d 0 1 = 0 := by
    rw [f'.comm, hf' 1 (by omega), comp_zero]
  have hc' : (f'.f 0 ≫ e0.hom) ≫ R.cocomplex.d 0 1 = 0 := by
    have hs := congrArg (fun t => t ≫ e1.hom) hc
    rw [R.cochainComplex_d 0 1 0 1 rfl rfl] at hs
    simpa only [e0,e1,Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using hs
  let s : KernelFork (R.cocomplex.d 0 1) := KernelFork.ofι (f'.f 0 ≫ e0.hom) hc'
  let a : K.X 0 ⟶ Y := R.isLimitKernelFork.lift s
  have ha : a ≫ R.ι.f 0 = f'.f 0 ≫ e0.hom :=
    R.isLimitKernelFork.fac s WalkingParallelPair.zero
  have hd : R.cochainComplex.d (-1) 0 = 0 :=
    (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 (-1)).eq_of_src _ _
  have hca : ∀ j, (ComplexShape.up ℤ).Rel j 0 → K.d j 0 ≫ a = 0 := by
    intro j hj
    have hj' : j = -1 := by change j+1=0 at hj; omega
    rw [hj']
    apply (cancel_mono (R.ι.f 0)).1
    erw [Category.assoc, ha, ← Category.assoc, ← f'.comm]
    change (f'.f (-1) ≫ R.cochainComplex.d (-1) 0) ≫ e0.hom = 0 ≫ R.ι.f 0
    rw [hd,comp_zero,zero_comp,zero_comp]
  let g : K ⟶ (CochainComplex.singleFunctor C 0).obj Y := mkHomToSingle a hca
  have he : g ≫ R.ι' = f' := by
    apply HomologicalComplex.Hom.ext
    funext j
    by_cases hj : j=0
    · subst j
      simp only [comp_f, g, mkHomToSingle_f, R.ι'_f_zero, Category.assoc,
        Iso.inv_hom_id_assoc]
      erw [← Category.assoc, ha]
      simp only [Category.assoc, e0, Iso.hom_inv_id, Category.comp_id]
    · by_cases hpos : 0<j
      · rw [comp_f, hf' j hpos]
        have hp : R.ι'.f j = 0 :=
          (isZero_single_obj_X (ComplexShape.up ℤ) 0 Y j hj).eq_of_src _ _
        rw [hp,comp_zero]
      · exact (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 j (by omega)).eq_of_tgt _ _
  exact ⟨g, he.symm ▸ H⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

lemma kInjective_chain_representative (K L : CochainComplex C ℤ) [L.IsKInjective]
    (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, DerivedCategory.Q.map f = a := by
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨b,hb⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (.up ℤ)).obj K) L).surjective
      ((e.app K).hom ≫ a ≫ (e.app L).inv)
  obtain ⟨f,rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective b
  refine ⟨f,?_⟩
  have ht := congrArg (fun t => (e.app K).inv ≫ t ≫ (e.app L).hom) hb
  change e.inv.app K ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫ e.hom.app L =
    e.inv.app K ≫ (e.hom.app K ≫ a ≫ e.inv.app L) ≫ e.hom.app L at ht
  simpa [e] using ht

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C] [HasDerivedCategory C]
variable {Y : C} (K : CochainComplex C ℤ)

theorem bounded_orthogonal_derived_descent_dual (R : InjectiveResolution Y) (N : ℕ)
    (hK : ∀ j, (N : ℤ) < j → IsZero (K.X j))
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext (K.X (n+1 : ℤ)) Y (n+1)))
    (a : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y)) :
    ∃ g : K ⟶ (CochainComplex.singleFunctor C 0).obj Y,
      DerivedCategory.Q.map g = a := by
  obtain ⟨f,hf⟩ := kInjective_chain_representative K R.cochainComplex
    (a ≫ DerivedCategory.Q.map R.ι')
  obtain ⟨g,⟨H⟩⟩ := bounded_cochain_coresolution_descends R N f hK hExt
  refine ⟨g, (cancel_mono (DerivedCategory.Q.map R.ι')).1 ?_⟩
  rw [← Functor.map_comp, ← DerivedCategory.Q_map_eq_of_homotopy C H, hf]

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C] [HasDerivedCategory C]
variable {X Y W : C}

theorem bounded_ordinary_factorization (P : ProjectiveResolution X)
    (R : InjectiveResolution Y) (L : CochainComplex C ℤ) (l u : ℤ)
    (hbound : ∀ j, j < l ∨ u < j → IsZero (L.X j))
    (hterms : ∀ j, InAdd W (L.X j))
    (hleft : ∀ n : ℕ, Subsingleton (Abelian.Ext X W (n+1)))
    (hright : ∀ n : ℕ, Subsingleton (Abelian.Ext W Y (n+1)))
    (v : X ⟶ Y)
    (α : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶ DerivedCategory.Q.obj L)
    (β : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y))
    (hv : α ≫ β = DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map v)) :
    ∃ (a : X ⟶ L.X 0) (b : L.X 0 ⟶ Y), a ≫ b = v := by
  obtain ⟨a,ha⟩ := bounded_orthogonal_derived_descent L P l.natAbs
    (fun j hj => hbound j (Or.inl (by have h : -l ≤ ((-l).natAbs : ℤ) := Int.le_natAbs; rw [Int.natAbs_neg] at h; omega)))
    (fun n => by
      let := hleft n
      exact ext_subsingleton_inAdd_right (hterms _) _) α
  obtain ⟨b,hb⟩ := bounded_orthogonal_derived_descent_dual L R u.natAbs
    (fun j hj => hbound j (Or.inr (by have h : u ≤ (u.natAbs : ℤ) := Int.le_natAbs; omega)))
    (fun n => by
      let := hright n
      exact ext_subsingleton_inAdd_left (hterms _) _) β
  let eX := singleObjXSelf (.up ℤ) 0 X
  let eY := singleObjXSelf (.up ℤ) 0 Y
  refine ⟨eX.inv ≫ a.f 0, b.f 0 ≫ eY.hom, ?_⟩
  have hab : DerivedCategory.Q.map (a ≫ b) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map v) := by
    rw [Functor.map_comp,ha,hb,hv]
  let S := CochainComplex.singleFunctor C 0
  let c := S.preimage (a ≫ b)
  have hcmap : S.map c = a ≫ b := S.map_preimage _
  have hc : c = v := by
    apply (DerivedCategory.singleFunctor C 0).map_injective
    change DerivedCategory.Q.map (S.map c) = DerivedCategory.Q.map (S.map v)
    rw [hcmap]
    exact hab
  have he : S.map v = a ≫ b := hc ▸ hcmap
  have he0 := congrArg (fun t => t.f 0) he
  change ((HomologicalComplex.single C (.up ℤ) 0).map v).f 0 = (a ≫ b).f 0 at he0
  rw [single_map_f_self,comp_f] at he0
  have h := congrArg (fun t => eX.inv ≫ t ≫ eY.hom) he0
  simpa only [eX,eY,Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,
    Category.comp_id] using h.symm

end Tachikawa


end
end OAI
