import OAI.RingTheory.Tachikawa.Twisting
import Mathlib.CategoryTheory.Adjunction.Unique

namespace OAI
noncomputable section

namespace Tachikawa.AlgebraInduction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

def adjunction (φ : R →ₐ[k] S) : functor φ ⊣ res φ :=
  Adjunction.mkOfHomEquiv
  { homEquiv := homEquiv φ
    homEquiv_naturality_left_symm := by
      intro X X' Y f g
      apply ModuleCat.hom_ext
      apply BalancedTensor.hom_ext
      intro s x
      rfl
    homEquiv_naturality_right := by
      intro X Y Y' f g
      ext x
      rfl }

def compositionIso (φ : R →ₐ[k] S) (ψ : S →ₐ[k] U) :
    functor φ ⋙ functor ψ ≅ functor (ψ.comp φ) := by
  let a := (adjunction φ).comp (adjunction ψ)
  let b := adjunction (ψ.comp φ)
  exact Adjunction.leftAdjointUniq a b

end Tachikawa.AlgebraInduction

end
end OAI
