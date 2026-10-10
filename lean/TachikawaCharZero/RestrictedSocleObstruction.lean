import TachikawaCharZero.SocleBimodule

/-! The actual restricted socle map inherits the rational derived obstruction.
Postcomposition with the constructed dual projection recovers eta. This
does not yet prove that restriction preserves perfect complexes: the
finite-projective-dimension replacement on restriction remains separate. -/
namespace TachikawaCharZero.RestrictedSocleObstruction
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI.Tachikawa ScalingSocle
attribute [local instance] HasDerivedCategory.standard
abbrev B := ScalingSocle.B

abbrev single := CochainComplex.singleFunctor (ModuleCat BE) 0
abbrev source := TwistedDerivedObstruction.sourceSingle
abbrev target (H : ℚ) (hH : H ≠ 0) := single.obj (restriction.obj (UH H hH))

theorem socle_not_bounded_projective_factor (H : ℚ) (hH : H ≠ 0)
    (P : CochainComplex (ModuleCat BE) ℤ)
    (hfin : ∀ i, Module.Finite BE (P.X i))
    (hproj : ∀ i, Module.Projective BE (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i))
    (α : DerivedCategory.Q.obj source ⟶ DerivedCategory.Q.obj P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (target H hH)) :
    α ≫ β ≠ DerivedCategory.Q.map (single.map (restrictedSocleMap H hH)) := by
  intro h
  apply TwistedDerivedObstruction.eta_not_bounded_projective_factor
    P hfin hproj l u hbound α
    (β ≫ DerivedCategory.Q.map (single.map (rhoMap H hH)))
  rw [← Category.assoc,h,← Functor.map_comp,← Functor.map_comp,restricted_socle_eta]

theorem restricted_socle_ne_zero (H : ℚ) (hH : H ≠ 0) :
    restrictedSocleMap H hH ≠ 0 := by
  intro h
  have he := restricted_socle_eta H hH
  rw [h,zero_comp] at he
  have hv := congrArg (fun f : TwistedBimoduleObstruction.U ⟶ TwistedBimoduleObstruction.D =>
    TwistedBimoduleObstruction.bimoduleUnderlying
      (f (show TwistedBimoduleObstruction.U from (1 : B)))
        (tensorVertex (2 : ℚ))) he
  change 0=TwistedFactorization.eta 1 (tensorVertex (2 : ℚ)) at hv
  rw [TwistedFactorization.eta_one_vertex] at hv
  exact zero_ne_one hv

end
end TachikawaCharZero.RestrictedSocleObstruction
