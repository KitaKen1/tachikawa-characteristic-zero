import OAI.RingTheory.Tachikawa.InductionAdjunction

namespace TachikawaCharZero.InductionTwistComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex OAI.Tachikawa

section Generic
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

theorem inverse_square (φ : R →ₐ[k] S) (θ : R ≃ₐ[k] R) (ψ : S ≃ₐ[k] S)
    (h : ψ.toAlgHom.comp φ = φ.comp θ.toAlgHom) :
    ψ.symm.toAlgHom.comp φ = φ.comp θ.symm.toAlgHom := by
  apply AlgHom.ext
  intro r
  apply ψ.injective
  have hr := AlgHom.congr_fun h (θ.symm r)
  simpa using hr.symm

def restrictionComparison (φ : R →ₐ[k] S) (θ : R ≃ₐ[k] R) (ψ : S ≃ₐ[k] S)
    (h : ψ.toAlgHom.comp φ = φ.comp θ.toAlgHom) :
    AlgebraInduction.res ψ.symm.toAlgHom ⋙ AlgebraInduction.res φ ≅
      AlgebraInduction.res φ ⋙ AlgebraInduction.res θ.symm.toAlgHom := by
  have hi : ψ.symm.toRingEquiv.toRingHom.comp φ.toRingHom =
      φ.toRingHom.comp θ.symm.toRingEquiv.toRingHom :=
    congrArg AlgHom.toRingHom (inverse_square φ θ ψ h)
  exact (ModuleCat.restrictScalarsComp φ.toRingHom ψ.symm.toRingEquiv.toRingHom).symm ≪≫
    ModuleCat.restrictScalarsComp' θ.symm.toRingEquiv.toRingHom φ.toRingHom
      (ψ.symm.toRingEquiv.toRingHom.comp φ.toRingHom) hi

def inductionComparison (φ : R →ₐ[k] S) (θ : R ≃ₐ[k] R) (ψ : S ≃ₐ[k] S)
    (h : ψ.toAlgHom.comp φ = φ.comp θ.toAlgHom) :
    AlgebraInduction.res θ.toAlgHom ⋙ AlgebraInduction.functor φ ≅
      AlgebraInduction.functor φ ⋙ AlgebraInduction.res ψ.toAlgHom := by
  let a := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv θ.toRingEquiv).toAdjunction.comp
    (AlgebraInduction.adjunction φ)
  let b := (AlgebraInduction.adjunction φ).comp
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv ψ.toRingEquiv).toAdjunction
  exact Adjunction.leftAdjointUniq a (b.ofNatIsoRight (restrictionComparison φ θ ψ h))

theorem restriction_exactAt_iff (φ : R →ₐ[k] S) {ι : Type} (c : ComplexShape ι)
    (K : HomologicalComplex (ModuleCat S) c) (n : ι) :
    (((AlgebraInduction.res φ).mapHomologicalComplex c).obj K).ExactAt n ↔ K.ExactAt n := by
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).trans
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (K.sc n)).symm

end Generic

end
end TachikawaCharZero.InductionTwistComparison
