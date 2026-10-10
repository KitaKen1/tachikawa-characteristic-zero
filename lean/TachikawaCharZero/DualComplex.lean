import TachikawaCharZero.RightCorners

/-! The rational Hom(R,C) coordinate complex. Exactness is proved in every
tail degree from explicit preimages, rather than finite-degree extrapolation.
The sparse formulas adapt OpenAI Math's Tachikawa/Corner.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0), with the
characteristic-zero signs restored. -/
namespace TachikawaCharZero.Resolution
open OAI.ArExplicit

def leftD (t : ℚ) (a : V) : V :=
  ![0,a 0,-t*a 0,-t*a 1+2*a 2,0,(1-t)*a 4]

def leftInitialD (a : V₀) : V := ![0,2*a 1,a 1,a 2,a 0,a 3]

theorem e_fixed_ell (t : ℚ) : vertexE*ell t=ell t := by
  ext i
  cases i <;> simp [vertexE,ell,BaseAlgebra.product]

theorem e_fixed_u : vertexE*BaseAlgebra.basisVector (2:ℚ) .u=
    BaseAlgebra.basisVector 2 .u := BaseAlgebra.basis_mul 2 .e .u

def leftDiff (t : ℚ) : EC →ₗ[Aᵐᵒᵖ] EC := Corner.mulLeft (ell t) (e_fixed_ell t)
def leftInitial : FC →ₗ[Aᵐᵒᵖ] EC := Corner.mulLeft
  (BaseAlgebra.basisVector 2 .u) e_fixed_u

theorem leftDiff_iso (t : ℚ) (a : V) : leftDiff t (ecIso a)=ecIso (leftD t a) := by
  apply Subtype.ext
  change ell t*ecEmbed a=ecEmbed (leftD t a)
  ext i
  cases i <;> simp [ell,ecEmbed,leftD,BaseAlgebra.product] <;> ring

theorem leftInitial_iso (a : V₀) : leftInitial (fcIso a)=ecIso (leftInitialD a) := by
  apply Subtype.ext
  change BaseAlgebra.basisVector 2 .u*fcEmbed a=ecEmbed (leftInitialD a)
  ext i
  cases i <;> simp [ecEmbed,fcEmbed,leftInitialD,BaseAlgebra.product]

theorem left_consecutive_zero (t : ℚ) (a : V) :
    leftD (-2*t) (leftD t a)=0 := by
  ext i
  fin_cases i <;> simp [leftD]
  ring

theorem left_next_kernel_iff (t : ℚ) (ht : 1+2*t≠0) (a : V) :
    leftD (-2*t) a=0 ↔ ∃ b : W, a=imageEmbed t b := by
  constructor
  · intro h
    have h0 : a 0=0 := by have hh:=congrFun h 1; simpa [leftD] using hh
    have h2 : a 2= -t*a 1 := by
      have hh:=congrFun h 3
      simp [leftD] at hh
      linarith
    have h4 : a 4=0 := by
      have hh:=congrFun h 5
      have hm : (1+2*t)*a 4=0 := by simpa [leftD] using hh
      exact (mul_eq_zero.mp hm).resolve_left ht
    refine ⟨![a 1,a 3,a 5],?_⟩
    ext i
    fin_cases i <;> simp [imageEmbed,h0,h2,h4]
  · rintro ⟨b,rfl⟩
    ext i
    fin_cases i <;> simp [leftD,imageEmbed]
    ring

def leftPreimage (t : ℚ) (b : W) : V := ![b 0,0,b 1/2,0,b 2/(1-t),0]

theorem leftD_preimage (t : ℚ) (ht : 1-t≠0) (b : W) :
    leftD t (leftPreimage t b)=imageEmbed t b := by
  ext i
  fin_cases i <;> simp [leftD,leftPreimage,imageEmbed]
  all_goals field_simp [ht]

theorem left_exact_coordinates (t : ℚ) (ht : 1-t≠0) (ht' : 1+2*t≠0) :
    Function.Exact (leftD t) (leftD (-2*t)) := by
  intro a
  constructor
  · intro h
    obtain ⟨b,rfl⟩ := (left_next_kernel_iff t ht' a).mp h
    exact ⟨leftPreimage t b,leftD_preimage t ht b⟩
  · rintro ⟨b,rfl⟩
    exact left_consecutive_zero t b

theorem left_exact_all_degrees (m : ℕ) :
    Function.Exact (leftDiff ((-2:ℚ)^(m+1))) (leftDiff ((-2:ℚ)^(m+2))) := by
  have hp : (-2:ℚ)^(m+2)= -2*(-2:ℚ)^(m+1) := by rw [pow_succ]; ring
  have ht := resolution_left_coefficient_ne_zero (m+1) (by omega)
  have ht' : 1+2*(-2:ℚ)^(m+1)≠0 := by
    have h := resolution_left_coefficient_ne_zero (m+2) (by omega)
    rw [hp] at h
    simpa using h
  intro a
  obtain ⟨a,rfl⟩ := ecIso.surjective a
  constructor
  · intro h
    rw [leftDiff_iso,← ecIso.map_zero] at h
    obtain ⟨b,hb⟩ := (left_exact_coordinates _ ht ht' a).mp
      (by simpa only [hp] using ecIso.injective h)
    exact ⟨ecIso b,by rw [leftDiff_iso,hb]⟩
  · rintro ⟨b,hb⟩
    obtain ⟨b,rfl⟩ := ecIso.surjective b
    rw [← hb,leftDiff_iso,leftDiff_iso,← ecIso.map_zero,hp]
    exact congrArg ecIso (left_consecutive_zero _ b)

theorem leftInitial_injective : Function.Injective leftInitial := by
  intro a b h
  obtain ⟨a,rfl⟩ := fcIso.surjective a
  obtain ⟨b,rfl⟩ := fcIso.surjective b
  rw [leftInitial_iso,leftInitial_iso] at h
  have hh := ecIso.injective h
  apply fcIso.injective.eq_iff.mpr
  ext i
  fin_cases i
  · exact congrFun hh 4
  · exact congrFun hh 2
  · exact congrFun hh 3
  · exact congrFun hh 5

theorem leftInitial_exact : Function.Exact leftInitial (leftDiff 1) := by
  intro a
  obtain ⟨a,rfl⟩ := ecIso.surjective a
  constructor
  · intro h
    rw [leftDiff_iso,← ecIso.map_zero] at h
    have hh := ecIso.injective h
    have h0 : a 0=0 := by have h:=congrFun hh 1; simpa [leftD] using h
    have h1 : a 1=2*a 2 := by
      have h:=congrFun hh 3
      simp [leftD] at h
      linarith
    refine ⟨fcIso ![a 4,a 2,a 3,a 5],?_⟩
    rw [leftInitial_iso]
    apply ecIso.injective.eq_iff.mpr
    ext i
    fin_cases i <;> simp [leftInitialD,h0,h1]
  · rintro ⟨b,hb⟩
    obtain ⟨b,rfl⟩ := fcIso.surjective b
    rw [← hb,leftInitial_iso,leftDiff_iso,← ecIso.map_zero]
    apply congrArg ecIso
    ext i
    fin_cases i <;> simp [leftInitialD,leftD]

end TachikawaCharZero.Resolution
