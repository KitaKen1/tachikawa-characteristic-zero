import OAI.RingTheory.Tachikawa.StableDuality

/-! Characteristic-independent excerpts from OpenAI Math,
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section




namespace Tachikawa
open CategoryTheory
variable {R : Type} [Ring R]

lemma exact_prodMap {A B C D E F : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]
    [Module R A] [Module R B] [Module R C] [Module R D] [Module R E] [Module R F]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (f' : D →ₗ[R] E) (g' : E →ₗ[R] F)
    (h : Function.Exact f g) (h' : Function.Exact f' g') :
    Function.Exact (f.prodMap f') (g.prodMap g') := by
  rintro ⟨b,e⟩
  change (g b,g' e) = (0,0) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨hb,he⟩
    obtain ⟨a,rfl⟩ := (h b).mp hb
    obtain ⟨d,rfl⟩ := (h' e).mp he
    exact ⟨(a,d),rfl⟩
  · rintro ⟨⟨a,d⟩,hh⟩
    cases hh
    exact ⟨h.apply_apply_eq_zero a,h'.apply_apply_eq_zero d⟩

namespace ProjectiveResolution
variable {M N : ModuleCat.{0} R} (P : CategoryTheory.ProjectiveResolution M)
    (Q : CategoryTheory.ProjectiveResolution N)

lemma function_exact_succ (n : ℕ) :
    Function.Exact (P.complex.d (n+2) (n+1)) (P.complex.d (n+1) n) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ n)

lemma function_exact_zero : Function.Exact (P.complex.d 1 0) (P.π.f 0) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀

def prod : CategoryTheory.ProjectiveResolution (ModuleCat.of R (M × N)) :=
  resolutionOfExact _ (fun n => ModuleCat.of R (P.complex.X n × Q.complex.X n))
    (fun n => ModuleCat.ofHom ((P.complex.d (n+1) n).hom.prodMap (Q.complex.d (n+1) n).hom))
    (ModuleCat.ofHom ((P.π.f 0).hom.prodMap (Q.π.f 0).hom))
    (fun n => exact_prodMap _ _ _ _ (function_exact_succ P n) (function_exact_succ Q n))
    (exact_prodMap _ _ _ _ (function_exact_zero P) (function_exact_zero Q))
    (by
      rintro ⟨m,n⟩
      obtain ⟨p,hp⟩ := (ModuleCat.epi_iff_surjective (P.π.f 0)).mp inferInstance m
      obtain ⟨q,hq⟩ := (ModuleCat.epi_iff_surjective (Q.π.f 0)).mp inferInstance n
      exact ⟨(p,q),Prod.ext hp hq⟩)
    (fun n => by infer_instance)

end ProjectiveResolution
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

namespace ProjectiveResolution
variable (M : ModuleCat.{0} R) [Projective M]

def simpleTerm : ℕ → ModuleCat R
  | 0 => M
  | _+1 => ModuleCat.of R PUnit

def simpleAug : simpleTerm M 0 ⟶ M := 𝟙 M

def simpleSelf : CategoryTheory.ProjectiveResolution M :=
  resolutionOfExact M (simpleTerm M) (fun _ => 0) (simpleAug M)
    (by
      intro n x
      refine ⟨fun _ => ⟨PUnit.unit, ?_⟩, fun _ => rfl⟩
      change (0 : PUnit) = x
      exact Subsingleton.elim _ _)
    (by intro x; exact ⟨fun hx => ⟨PUnit.unit,hx.symm⟩,fun ⟨_,hx⟩ => hx.symm⟩)
    (Function.surjective_id)
    (by intro n; cases n <;> dsimp [simpleTerm] <;> infer_instance)

lemma simpleSelf_above (n : ℕ) (hn : 0 < n) : IsZero ((simpleSelf M).complex.X n) := by
  cases n with
  | zero => omega
  | succ n =>
    change IsZero (ModuleCat.of R PUnit)
    exact ModuleCat.isZero_of_subsingleton _

lemma simpleSelf_finite [FiniteDimensional k M] (n : ℕ) :
    FiniteDimensional k ((simpleSelf M).complex.X n) := by
  cases n with
  | zero => exact inferInstanceAs (FiniteDimensional k M)
  | succ n => exact inferInstanceAs (FiniteDimensional k PUnit)

variable {M} {N : ModuleCat.{0} R} (P : CategoryTheory.ProjectiveResolution M)
    (Q : CategoryTheory.ProjectiveResolution N)

omit [Projective M] in
lemma prod_above (b n : ℕ) (hP : ∀ i, b < i → IsZero (P.complex.X i))
    (hQ : ∀ i, b < i → IsZero (Q.complex.X i)) (hn : b < n) :
    IsZero ((prod P Q).complex.X n) := by
  let := ModuleCat.subsingleton_of_isZero (hP n hn)
  let := ModuleCat.subsingleton_of_isZero (hQ n hn)
  change IsZero (ModuleCat.of R (P.complex.X n × Q.complex.X n))
  exact ModuleCat.isZero_of_subsingleton _

omit [Projective M] in
lemma prod_finite (hP : ∀ n, FiniteDimensional k (P.complex.X n))
    (hQ : ∀ n, FiniteDimensional k (Q.complex.X n)) (n : ℕ) :
    FiniteDimensional k ((prod P Q).complex.X n) := by
  let := hP n
  let := hQ n
  change FiniteDimensional k (P.complex.X n × Q.complex.X n)
  infer_instance

end ProjectiveResolution
end Tachikawa



end
end OAI
