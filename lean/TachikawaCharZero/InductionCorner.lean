import TachikawaCharZero.Corner
import OAI.RingTheory.Tachikawa.Twisting

/-! Induction of a principal projective is the corresponding principal
projective over the target ring. Explicit balanced generators make this
comparison commute with right multiplication, without any flatness or
finite-dimensionality assumption. -/
namespace TachikawaCharZero.InductionCorner
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S)

def source (p : R) := ModuleCat.of R (Corner.leftCorner p)
def target (p : R) := ModuleCat.of S (Corner.leftCorner (φ p))
instance (p : R) : CoeOut (source p) R :=
  ⟨fun x => ((show Corner.leftCorner p from x) : R)⟩
instance (p : R) : CoeOut (target φ p) S :=
  ⟨fun x => ((show Corner.leftCorner (φ p) from x) : S)⟩

def generators (p : R) : source p ⟶ (AlgebraInduction.res φ).obj (target φ p) :=
  ModuleCat.ofHom (Y := (AlgebraInduction.res φ).obj (target φ p))
    { toFun := fun x => ⟨φ (x : R), by
        change φ (x : R) * φ p = φ (x : R)
        rw [← map_mul,x.property]⟩
      map_add' x y := Subtype.ext (φ.map_add _ _)
      map_smul' r x := Subtype.ext (φ.map_mul _ _) }

def forward (p : R) : (AlgebraInduction.functor φ).obj (source p) ⟶ target φ p :=
  AlgebraInduction.extend φ (generators φ p)

theorem forward_mk (p : R) (s : AlgebraInduction.Bimod φ) (x : source p) :
    (forward φ p (BalancedTensor.mk s x) : S) = (show S from s) * φ (x : R) := rfl

def backward {p : R} (hp : p*p=p) :
    target φ p →ₗ[S] (AlgebraInduction.functor φ).obj (source p) where
  toFun x := BalancedTensor.mk (show AlgebraInduction.Bimod φ from (x:S))
    (show source p from ⟨p,hp⟩)
  map_add' x y := LinearMap.congr_fun
    ((BalancedTensor.mk (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := source p)).map_add
      (show AlgebraInduction.Bimod φ from (x:S))
      (show AlgebraInduction.Bimod φ from (y:S))) (show source p from ⟨p,hp⟩)
  map_smul' s x := LinearMap.congr_fun
    ((BalancedTensor.mk (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := source p)).map_smul s
      (show AlgebraInduction.Bimod φ from (x:S))) (show source p from ⟨p,hp⟩)

theorem forward_backward {p : R} (hp : p*p=p) (x : target φ p) :
    forward φ p (backward φ hp x) = x := by
  apply Subtype.ext
  change (x:S) * φ p = (x:S)
  exact x.property

theorem backward_forward {p : R} (hp : p*p=p)
    (x : (AlgebraInduction.functor φ).obj (source p)) :
    backward φ hp (forward φ p x) = x := by
  induction x using BalancedTensor.induction_on with
  | h0 => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht s x =>
    change BalancedTensor.mk (k := k) (R := R) (S := S)
      (show AlgebraInduction.Bimod φ from (show S from s) * φ (x:R))
      (show source p from ⟨p,hp⟩) = BalancedTensor.mk s x
    change BalancedTensor.mk (k := k) (R := R) (S := S)
      (MulOpposite.op (x:R) • s) (show source p from ⟨p,hp⟩) = _
    rw [BalancedTensor.balance]
    congr 1
    exact Subtype.ext x.property

def equiv {p : R} (hp : p*p=p) :
    (AlgebraInduction.functor φ).obj (source p) ≃ₗ[S] target φ p :=
  LinearEquiv.ofBijective (forward φ p).hom
    ⟨Function.LeftInverse.injective (backward_forward φ hp),
      Function.RightInverse.surjective (forward_backward φ hp)⟩

def iso {p : R} (hp : p*p=p) :
    (AlgebraInduction.functor φ).obj (source p) ≅ target φ p :=
  (equiv φ hp).toModuleIso

theorem iso_hom {p : R} (hp : p*p=p) : (iso φ hp).hom = forward φ p := rfl

theorem forward_mulRight {p r : R} (b : R) (hb : b*r=b) :
    (AlgebraInduction.functor φ).map (ModuleCat.ofHom
      (X := source p) (Y := source r) (Corner.mulRight (p := p) b hb)) ≫
      forward φ r =
    forward φ p ≫ ModuleCat.ofHom (X := target φ p) (Y := target φ r)
      (Corner.mulRight (p := φ p) (φ b) (by rw [← map_mul,hb])) := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro s x
  apply Subtype.ext
  change (show S from s) * φ ((x:R)*b) =
    ((show S from s) * φ (x:R)) * φ b
  rw [map_mul,mul_assoc]

end
end TachikawaCharZero.InductionCorner
