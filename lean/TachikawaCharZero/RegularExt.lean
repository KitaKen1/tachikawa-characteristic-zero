import TachikawaCharZero.HomDual
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-! Ordinary Abelian.Ext(L,C) vanishes in every degree except two.
A concrete degree-two cocycle represents a nonzero class. This connects the
Hom calculation to the actual Ext API without adding any paper assumptions. -/
namespace TachikawaCharZero.Resolution
noncomputable section
open CategoryTheory

theorem simple_regular_ext_zero :
    Subsingleton (Abelian.Ext.{0} (ModuleCat.of A Simple) (ModuleCat.of A A) 0) := by
  have : Subsingleton (ModuleCat.of A Simple ⟶ ModuleCat.of A A) :=
    ⟨fun F G => ModuleCat.hom_ext
      ((homSimpleRegular_zero F.hom).trans (homSimpleRegular_zero G.hom).symm)⟩
  exact Abelian.Ext.addEquiv₀.injective.subsingleton

theorem simple_regular_ext_one :
    Subsingleton (Abelian.Ext.{0} (ModuleCat.of A Simple) (ModuleCat.of A A) 1) := by
  let P := projectiveResolution
  have hz (α : Abelian.Ext.{0} (ModuleCat.of A Simple) (ModuleCat.of A A) 1) : α=0 := by
    obtain ⟨F,hF,rfl⟩ := P.extMk_surjective α 2 rfl
    have hf : homDiff 1 F.hom=0 := by
      change projectiveResolution.complex.d 2 1 ≫ F=0 at hF
      rw [projectiveResolution_d] at hF
      exact ModuleCat.hom_ext_iff.mp hF
    obtain ⟨g,hg⟩ := (homInitial_exact F.hom).mp hf
    apply (P.extMk_eq_zero_iff F 2 rfl hF 0 rfl).mpr
    refine ⟨ModuleCat.ofHom g,?_⟩
    change projectiveResolution.complex.d 1 0 ≫ _=F
    rw [projectiveResolution_d]
    exact ModuleCat.hom_ext hg
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

theorem simple_regular_ext_above (m : ℕ) :
    Subsingleton (Abelian.Ext.{0} (ModuleCat.of A Simple) (ModuleCat.of A A) (m+3)) := by
  let P := projectiveResolution
  have hz (α : Abelian.Ext.{0} (ModuleCat.of A Simple) (ModuleCat.of A A) (m+3)) :
      α=0 := by
    obtain ⟨F,hF,rfl⟩ := P.extMk_surjective α (m+4) rfl
    have hf : homDiff ((-2:ℚ)^(m+2)) F.hom=0 := by
      change projectiveResolution.complex.d (m+4) (m+3) ≫ F=0 at hF
      rw [projectiveResolution_d] at hF
      exact ModuleCat.hom_ext_iff.mp hF
    obtain ⟨g,hg⟩ := (homDiff_exact_all_degrees m F.hom).mp hf
    apply (P.extMk_eq_zero_iff F (m+4) rfl hF (m+2) rfl).mpr
    refine ⟨ModuleCat.ofHom g,?_⟩
    change projectiveResolution.complex.d (m+3) (m+2) ≫ _=F
    rw [projectiveResolution_d]
    exact ModuleCat.hom_ext hg
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

theorem simple_regular_ext_vanishing (n : ℕ) (hn : n≠2) :
    Subsingleton (Abelian.Ext.{0} (ModuleCat.of A Simple) (ModuleCat.of A A) n) := by
  rcases n with _ | _ | _ | m
  · exact simple_regular_ext_zero
  · exact simple_regular_ext_one
  · exact (hn rfl).elim
  · exact simple_regular_ext_above m

def vHom : HomE := homEEquiv.symm (ecIso ![0,0,0,0,0,1])

theorem vHom_diff (t : ℚ) : homDiff t vHom=0 := by
  apply homEEquiv.injective
  rw [homEEquiv_diff,map_zero]
  change leftDiff t (homEEquiv (homEEquiv.symm _))=0
  rw [homEEquiv.apply_symm_apply,leftDiff_iso,← ecIso.map_zero]
  apply congrArg ecIso
  ext i
  fin_cases i <;> simp [leftD]

theorem vHom_v_coefficient : (homEEquiv vHom:A).coeff .v=1 := by
  rw [vHom,homEEquiv.apply_symm_apply]
  rfl

theorem homDiff_one_v_zero (F : HomE) : (homEEquiv (homDiff 1 F):A).coeff .v=0 := by
  rw [homEEquiv_diff]
  obtain ⟨a,ha⟩ := ecIso.surjective (homEEquiv F)
  rw [← ha,leftDiff_iso]
  simp [ecIso,ecEmbed,leftD]

theorem vHom_closed : projectiveResolution.complex.d 3 2 ≫ ModuleCat.ofHom vHom=0 := by
  rw [projectiveResolution_d]
  apply ModuleCat.hom_ext
  change homDiff ((-2:ℚ)^1) vHom=0
  simpa using vHom_diff (-2)

def regularExtTwoClass : Abelian.Ext.{0} (ModuleCat.of A Simple) (ModuleCat.of A A) 2 :=
  projectiveResolution.extMk (ModuleCat.ofHom vHom) 3 rfl vHom_closed

theorem regularExtTwoClass_ne_zero : regularExtTwoClass≠0 := by
  intro h
  change projectiveResolution.extMk (ModuleCat.ofHom vHom) 3 rfl vHom_closed=0 at h
  obtain ⟨g,hg⟩ := (projectiveResolution.extMk_eq_zero_iff (n := 2)
    (Y := ModuleCat.of A A) (ModuleCat.ofHom vHom) 3 rfl vHom_closed 1 rfl).mp h
  rw [projectiveResolution_d] at hg
  have hf : homDiff 1 g.hom=vHom := ModuleCat.hom_ext_iff.mp hg
  have hv := congrArg (fun F : HomE => (homEEquiv F:A).coeff .v) hf
  exact zero_ne_one ((homDiff_one_v_zero g.hom).symm.trans
    (hv.trans vHom_v_coefficient))

end
end TachikawaCharZero.Resolution
