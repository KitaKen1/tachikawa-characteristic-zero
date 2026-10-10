import OAI.RingTheory.Tachikawa.GenericTriangularCone

/-! Reflect a contraction of the actual triangular cone to its unshifted
source complex. The forbidden D0-to-D1 block is zero, so the reflection
uses actual homotopies and requires no characteristic-two Hom complex. -/
namespace TachikawaCharZero.TriangularHomotopy
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
  {P : ChainComplex (ModuleCat.{0} R) ℤ} (u : P ⟶ Enveloping.tensorComplex F P)

abbrev v := Triangular.crossMap F u
abbrev C := Triangular.cone F u

def lowMap {i j : ℤ} (f : (C F u).X i ⟶ (C F u).X j) : P.X i ⟶ P.X j :=
  Triangular.diagonal₀ (CompleteCone.inRight (v F u) i ≫ f ≫ CompleteCone.right (v F u) j)

theorem lowMap_zero (i j : ℤ) : lowMap F u (0 : (C F u).X i ⟶ (C F u).X j)=0 := by
  simp only [lowMap,comp_zero,zero_comp,map_zero]

theorem lowMap_add {i j : ℤ} (f g : (C F u).X i ⟶ (C F u).X j) :
    lowMap F u (f+g)=lowMap F u f+lowMap F u g := by
  simp only [lowMap,comp_add,add_comp,map_add]

theorem lowMap_id (j : ℤ) : lowMap F u (𝟙 ((C F u).X j))=𝟙 (P.X j) := by
  simp only [lowMap,Category.id_comp,CompleteCone.inRight_right]
  rfl

theorem diagonal_post {L M N : ModuleCat.{0} R}
    (f : Triangular.D₀Obj F L ⟶ Triangular.D₀Obj F M) (d : M ⟶ N) :
    Triangular.diagonal₀ (f ≫ Triangular.D₀Map F d)=Triangular.diagonal₀ f ≫ d := rfl

theorem lowMap_pre_d (i j l : ℤ) (f : (C F u).X j ⟶ (C F u).X l) :
    lowMap F u ((C F u).d i j ≫ f)=P.d i j ≫ lowMap F u f := by
  change Triangular.diagonal₀
    ((CompleteCone.inRight (v F u) i ≫ (C F u).d i j) ≫ f ≫
      CompleteCone.right (v F u) l)=_
  rw [CompleteCone.inRight_d,Category.assoc]
  exact Triangular.diagonal₀_pre F _ _

theorem lowMap_post_d (i j l : ℤ) (f : (C F u).X i ⟶ (C F u).X j) :
    lowMap F u (f ≫ (C F u).d j l)=lowMap F u f ≫ P.d j l := by
  have hz : CompleteCone.inRight (v F u) i ≫ f ≫ CompleteCone.left (v F u) j=0 :=
    Triangular.cross₀₁_zero _
  have ht := congrArg (fun e => CompleteCone.inRight (v F u) i ≫ f ≫ e)
    (CompleteCone.total (v F u) j)
  simp only [comp_add,← Category.assoc,hz,zero_comp,zero_add,Category.comp_id] at ht
  have hf : CompleteCone.inRight (v F u) i ≫ f =
      (CompleteCone.inRight (v F u) i ≫ f ≫ CompleteCone.right (v F u) j) ≫
        CompleteCone.inRight (v F u) j := ht.symm
  change Triangular.diagonal₀
    ((CompleteCone.inRight (v F u) i ≫ f) ≫ (C F u).d j l ≫
      CompleteCone.right (v F u) l)=_
  have hd : CompleteCone.inRight (v F u) j ≫ (C F u).d j l ≫
      CompleteCone.right (v F u) l = Triangular.D₀Map F (P.d j l) := by
    rw [← Category.assoc,CompleteCone.inRight_d,Category.assoc,
      CompleteCone.inRight_right,Category.comp_id]
    rfl
  rw [hf]
  simp only [Category.assoc,hd]
  simpa only [lowMap, Category.assoc] using
    (diagonal_post F
      (CompleteCone.inRight (v F u) i ≫ f ≫ CompleteCone.right (v F u) j)
      (P.d j l))

/-- Reflection of an actual contraction, valid over every field. -/
def contraction (h : Homotopy (𝟙 (C F u)) 0) : Homotopy (𝟙 P) 0 where
  hom i j := lowMap F u (h.hom i j)
  zero i j hij := by rw [h.zero i j hij,lowMap_zero]
  comm j := by
    have hc := congrArg (lowMap F u) (h.comm j)
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel j (j-1) by change j-1+1=j; omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)] at hc ⊢
    simpa only [id_f,zero_f,lowMap_add,lowMap_zero,lowMap_id,lowMap_pre_d,
      lowMap_post_d,add_zero] using hc

end
end TachikawaCharZero.TriangularHomotopy
