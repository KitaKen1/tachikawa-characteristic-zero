import OAI.RingTheory.Tachikawa.InductionLeftComparison
import OAI.RingTheory.Tachikawa.StableEquivalence

/-! A homotopy equivalence of natural-number chain complexes induces
stable equivalences of positive-degree cokernels whenever the preceding
terms are finite projective. Exactness of either complex is unnecessary. -/
namespace TachikawaCharZero.NatCokerStable
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex OAI.Tachikawa
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {P Q U : ChainComplex (ModuleCat R) ℕ}

def map (f : P ⟶ Q) (n : ℕ) : NatCoker.C P n →ₗ[R] NatCoker.C Q n :=
  (LinearMap.range (P.d (n+2) (n+1)).hom).mapQ
    (LinearMap.range (Q.d (n+2) (n+1)).hom) (f.f (n+1)).hom (by
      rintro x ⟨y,rfl⟩
      refine ⟨f.f (n+2) y,?_⟩
      exact (LinearMap.congr_fun
        (ModuleCat.hom_ext_iff.mp (f.comm (n+2) (n+1))) y))

theorem map_comp (f : P ⟶ Q) (g : Q ⟶ U) (n : ℕ) :
    map (f ≫ g) n = (map g n).comp (map f n) := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n+2) (n+1)).hom) x
  rfl

theorem map_id (n : ℕ) : map (𝟙 P) n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n+2) (n+1)).hom) x
  rfl

theorem map_sub (f g : P ⟶ Q) (n : ℕ) : map (f-g) n = map f n - map g n := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n+2) (n+1)).hom) x
  exact (NatCoker.π Q n).map_sub (f.f (n+1) y) (g.f (n+1) y)

theorem map_factors_of_nullhomotopy (f : P ⟶ Q) (h : Homotopy f 0) (n : ℕ)
    (fin : Module.Finite R (P.X n)) (proj : Module.Projective R (P.X n)) :
    map f n ∈ projectiveFactors (k := k) := by
  refine ⟨P.X n,fin,proj,NatCoker.ι P n,
    (NatCoker.π Q n).comp (h.hom n (n+1)).hom,?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n+2) (n+1)).hom) x
  have hc := h.comm (n+1)
  rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n+1) n from rfl),
    prevD_eq _ (show (ComplexShape.down ℕ).Rel (n+2) (n+1) from rfl)] at hc
  have hy := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hc) y
  change f.f (n+1) y = h.hom n (n+1) (P.d (n+1) n y) +
    Q.d (n+2) (n+1) (h.hom (n+1) (n+2) y) + 0 at hy
  change NatCoker.π Q n (h.hom n (n+1) (P.d (n+1) n y)) =
    NatCoker.π Q n (f.f (n+1) y)
  rw [hy,add_zero,map_add]
  have hz : NatCoker.π Q n (Q.d (n+2) (n+1) (h.hom (n+1) (n+2) y)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨h.hom (n+1) (n+2) y,rfl⟩
  rw [hz,add_zero]

def comparison (e : HomotopyEquiv P Q) (n : ℕ)
    (pfin : Module.Finite R (P.X n)) (pproj : Module.Projective R (P.X n))
    (qfin : Module.Finite R (Q.X n)) (qproj : Module.Projective R (Q.X n)) :
    StableEquiv (k := k) (ModuleCat.of R (NatCoker.C P n))
      (ModuleCat.of R (NatCoker.C Q n)) where
  hom := map e.hom n
  inv := map e.inv n
  inv_hom := by
    rw [← map_comp,← map_id (P := P) n,← map_sub]
    exact map_factors_of_nullhomotopy _
      (Homotopy.equivSubZero e.homotopyHomInvId) n pfin pproj
  hom_inv := by
    rw [← map_comp,← map_id (P := Q) n,← map_sub]
    exact map_factors_of_nullhomotopy _
      (Homotopy.equivSubZero e.homotopyInvHomId) n qfin qproj

end
end TachikawaCharZero.NatCokerStable
