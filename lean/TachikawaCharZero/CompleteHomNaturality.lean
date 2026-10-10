import OAI.RingTheory.Tachikawa.CompleteStable

/-! Naturality of the actual complete-Hom/stable-Hom equivalence.
The quotient and target-map proofs adapt the characteristic-independent
HomProfile.lean lines 1007--1050 of OpenAI Math, fixed at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
These are unshifted naturality statements; degree-three generator
compatibility still requires the shifted comparison. -/
namespace TachikawaCharZero.CompleteHomNaturality
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory OAI.Tachikawa OAI.Tachikawa.CompleteHom
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ)
  (hP : TotallyAcyclic P) (fin : ∀ j, Module.Finite R (P.X j))
  (proj : ∀ j, Module.Projective R (P.X j))

theorem equiv_quotient (N : ModuleCat.{0} R) (a : ℤ)
    (z : VectorSplit.Z (completeHom (k := k) P N) a) :
    equiv P N hP fin proj a (VectorSplit.quotient _ a z) =
      stableClass (k := k) ((cokerCycles P N a).symm z) := rfl

theorem equiv_natural {M N : ModuleCat.{0} R} (f : M ⟶ N) (a : ℤ)
    (x : VectorSplit.H (completeHom (k := k) P M) a) :
    equiv P N hP fin proj a (completeHmap P f a x) =
      stablePostcompose f.hom (equiv P M hP fin proj a x) := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective a x
  change stableClass (k := k) _ = stableClass (k := k) _
  congr 1
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := CokerAt.π_surjective P a x
  rfl

/-- Composition in the stable quotient depends on the class of the target map. -/
theorem postcompose_eq_stableComp {M : Type} [AddCommGroup M] [Module R M]
    [Module k M] [IsScalarTower k R M] {N L : ModuleCat.{0} R} (f : N ⟶ L)
    (x : StableHom (k := k) (R := R) (M := M) (N := N)) :
    stablePostcompose f.hom x = stableComp (stableClass (k := k) f.hom) x := by
  obtain ⟨g,rfl⟩ := stableClass_surjective x
  rfl

include hP fin proj in
/-- Every integer degree of complete Hom factors through the stable class
of the target morphism; this does not require a choice of generators. -/
theorem completeHmap_eq_of_stable_class {M N : ModuleCat.{0} R} (f g : M ⟶ N)
    (h : stableClass (k := k) f.hom = stableClass (k := k) g.hom) (a : ℤ) :
    completeHmap (k := k) P f a = completeHmap P g a := by
  apply LinearMap.ext
  intro x
  apply (equiv P N hP fin proj a).injective
  rw [equiv_natural, equiv_natural, postcompose_eq_stableComp,
    postcompose_eq_stableComp, h]

variable {X : ModuleCat.{0} R} (e : CokerAt P 0 ≃ₗ[R] X)

def zeroEquiv (N : ModuleCat.{0} R) :
    VectorSplit.H (completeHom (k := k) P N) 0 ≃ₗ[k] StableMap (k := k) X N :=
  (equiv P N hP fin proj 0).trans ((StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of R (CokerAt P 0)) (N := X) e).pre N)

theorem zeroEquiv_natural {M N : ModuleCat.{0} R} (f : M ⟶ N)
    (x : VectorSplit.H (completeHom (k := k) P M) 0) :
    zeroEquiv P hP fin proj e N (completeHmap P f 0 x) =
      stablePostcompose f.hom (zeroEquiv P hP fin proj e M x) := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective 0 x
  change stableClass (k := k) _ = stableClass (k := k) _
  congr 1
  apply LinearMap.ext
  intro x
  obtain ⟨y,hy⟩ := CokerAt.π_surjective P 0 (e.symm x)
  change ((cokerCycles P N 0).symm
    (VectorSplit.cycleMap (completeHomMap P f) 0 z)) (e.symm x) =
    f (((cokerCycles P M 0).symm z) (e.symm x))
  rw [← hy]
  rfl

/-- Pullback on actual complete-Hom complexes, before taking homology. -/
def sourceMap {P Q : ChainComplex (ModuleCat.{0} R) ℤ}
    (f : P ⟶ Q) (N : ModuleCat.{0} R) :
    completeHom (k := k) Q N ⟶ completeHom P N :=
  (((linearYoneda k (ModuleCat R)).obj N).mapHomologicalComplex (.up ℤ)).map
    ((HomologicalComplex.opFunctor (ModuleCat R) (.down ℤ)).map f.op)

theorem sourceMap_apply {P Q : ChainComplex (ModuleCat.{0} R) ℤ}
    (f : P ⟶ Q) (N : ModuleCat.{0} R) (a : ℤ) (g : Q.X a ⟶ N) :
    (sourceMap (k := k) f N).f a g = f.f a ≫ g := rfl

theorem sourceMap_comp {P Q S : ChainComplex (ModuleCat.{0} R) ℤ}
    (f : P ⟶ Q) (g : Q ⟶ S) (N : ModuleCat.{0} R) :
    sourceMap (k := k) (f ≫ g) N = sourceMap g N ≫ sourceMap f N := by
  ext a h
  rfl

/-- Naturality in the resolution identifies actual chain pullback with
precomposition by its actual cokernel map in the stable quotient. -/
theorem equiv_source_natural (Q : ChainComplex (ModuleCat.{0} R) ℤ)
    (hQ : TotallyAcyclic Q) (finQ : ∀ j, Module.Finite R (Q.X j))
    (projQ : ∀ j, Module.Projective R (Q.X j))
    (f : P ⟶ Q) (N : ModuleCat.{0} R) (a : ℤ)
    (x : VectorSplit.H (completeHom (k := k) Q N) a) :
    equiv P N hP fin proj a (VectorSplit.Hmap (sourceMap f N) a x) =
      stablePrecompose (k := k) (L := ModuleCat.of R (CokerAt P a))
        (M := ModuleCat.of R (CokerAt Q a)) (N := N)
        (CokerAt.map f a) (equiv Q N hQ finQ projQ a x) := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective a x
  change stableClass (k := k) _ = stableClass (k := k) _
  congr 1
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := CokerAt.π_surjective P a x
  rfl

end
end TachikawaCharZero.CompleteHomNaturality
