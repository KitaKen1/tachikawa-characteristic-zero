import TachikawaCharZero.RestrictedPerfect
import TachikawaCharZero.RestrictedSocleObstruction
import OAI.RingTheory.Tachikawa.ExactDerived

/-! The actual rational Hom(X,X) socle map cannot factor through a
bounded finite-projective E-enveloping complex. Restrict a proposed
factorization and replace its middle complex using the constructed
length-eight resolution; the actual restricted eta obstruction applies.
Stable lifts and their evaluated nonzero classes remain separate. -/
namespace TachikawaCharZero.SoclePerfectObstruction
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open ScalingSocle SocleBimodule
attribute [local instance] HasDerivedCategory.standard
abbrev singleE := CochainComplex.singleFunctor (ModuleCat EE) 0
abbrev singleB := CochainComplex.singleFunctor (ModuleCat BE) 0
abbrev comparison := singleMapHomologicalComplex restriction (.up ℤ) 0

/-- The single-complex comparison is natural on the actual socle map. -/
theorem restricted_single_socle (H : ℚ) (hH : H ≠ 0) :
    singleB.map restrictedCharacterMap ≫ comparison.inv.app S ≫
      (restriction.mapHomologicalComplex (.up ℤ)).map (singleE.map (socleMap H hH)) ≫
      comparison.hom.app (UH H hH) = singleB.map (restrictedSocleMap H hH) := by
  have hn := comparison.hom.naturality (socleMap H hH)
  dsimp only [Functor.comp_map] at hn
  erw [hn]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp,restricted_character_socle]

theorem socle_not_bounded_projective_factor (H : ℚ) (hH : H ≠ 0)
    (P : CochainComplex (ModuleCat EE) ℤ)
    (hfin : ∀ i, Module.Finite EE (P.X i))
    (hproj : ∀ i, Module.Projective EE (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i))
    (α : DerivedCategory.Q.obj (singleE.obj S) ⟶ DerivedCategory.Q.obj P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (singleE.obj (UH H hH))) :
    α ≫ β ≠ DerivedCategory.Q.map (singleE.map (socleMap H hH)) := by
  intro h
  obtain ⟨Q,f,hf,hp,hf',hb⟩ := RestrictedPerfect.bounded_replacement P hfin hproj l u hbound
  let := hf
  let a := DerivedCategory.Q.map (singleB.map restrictedCharacterMap ≫ comparison.inv.app S) ≫
    exactDerivedHom restriction α ≫ inv (DerivedCategory.Q.map f)
  let b := DerivedCategory.Q.map f ≫ exactDerivedHom restriction β ≫
    DerivedCategory.Q.map (comparison.hom.app (UH H hH))
  apply RestrictedSocleObstruction.socle_not_bounded_projective_factor
    H hH Q hf' hp (l-8) u hb a b
  dsimp only [a,b]
  simp only [Category.assoc,IsIso.inv_hom_id_assoc]
  rw [← Category.assoc (exactDerivedHom restriction α) (exactDerivedHom restriction β)]
  rw [← exactDerivedHom_comp,h,exactDerivedHom_map]
  simpa only [Functor.map_comp,Category.assoc] using
    congrArg (fun v => DerivedCategory.Q.map v) (restricted_single_socle H hH)

end
end TachikawaCharZero.SoclePerfectObstruction
