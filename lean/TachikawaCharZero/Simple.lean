import TachikawaCharZero.Initial
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The quotient is the one-dimensional character at f. The explicit kernel
preimage avoids rank computations. The character construction follows the
generic part of OpenAI Math's Tachikawa/Corner.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0). -/
namespace TachikawaCharZero.Resolution
noncomputable section
open OAI.ArExplicit

def character : A →ₐ[ℚ] ℚ where
  toFun a := a.coeff .f
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

def CharacterModule := ℚ
instance : AddCommGroup CharacterModule := inferInstanceAs (AddCommGroup ℚ)
instance : Module ℚ CharacterModule := inferInstanceAs (Module ℚ ℚ)
instance : Module A CharacterModule := Module.compHom CharacterModule character.toRingHom
instance : IsScalarTower ℚ A CharacterModule :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    change character (algebraMap ℚ A r) • x = r • x
    rw [AlgHom.commutes]
    rfl
instance : Module.Finite ℚ CharacterModule := inferInstanceAs (Module.Finite ℚ ℚ)

def characterAug : Cf →ₗ[A] CharacterModule where
  toFun a := (a:A).coeff .f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem characterAug_surjective : Function.Surjective characterAug :=
  fun x => ⟨cfIso ![x,0,0,0], rfl⟩

theorem characterAug_exact : Function.Exact initialMap characterAug := by
  intro a
  obtain ⟨a,rfl⟩ := cfIso.surjective a
  constructor
  · intro h
    change a 0 = 0 at h
    refine ⟨ceIso ![a 1,a 2,0,0,a 3/3,0], ?_⟩
    rw [initialMap_iso]
    apply cfIso.injective.eq_iff.mpr
    ext i
    fin_cases i <;> simp [initialD,h]
    ring
  · rintro ⟨b,hb⟩
    obtain ⟨b,rfl⟩ := ceIso.surjective b
    rw [← hb,initialMap_iso]
    rfl

def simpleCharacterIso : Simple ≃ₗ[A] CharacterModule :=
  (Submodule.quotEquivOfEq _ _ characterAug_exact.linearMap_ker_eq.symm).trans
    (characterAug.quotKerEquivOfSurjective characterAug_surjective)

def simpleRationalIso : Simple ≃ₗ[ℚ] ℚ :=
  simpleCharacterIso.restrictScalars ℚ

instance simpleFiniteQ : Module.Finite ℚ Simple :=
  Module.Finite.equiv simpleRationalIso.symm

theorem simple_finrank : Module.finrank ℚ Simple = 1 := by
  rw [simpleRationalIso.finrank_eq]
  exact Module.finrank_self ℚ

instance simpleIsSimple : IsSimpleModule A Simple :=
  (isSimpleModule_iff A Simple).mpr
    (is_simple_module_of_finrank_eq_one (A := A) simple_finrank)

theorem character_e_smul (x : CharacterModule) : vertexE • x = 0 := by
  change (0:ℚ) • x = 0
  exact zero_smul ℚ x

theorem e_smul_simple (x : Simple) : vertexE • x = 0 := by
  apply simpleCharacterIso.injective
  rw [map_smul,character_e_smul,map_zero]

def eGenerator : Ce := ⟨vertexE,vertexE_idempotent⟩

theorem ce_generated (a : Ce) : (a:A) • eGenerator = a :=
  Subtype.ext a.property

theorem homCeSimple_zero (F : Ce →ₗ[A] Simple) : F = 0 := by
  have hfix : vertexE • eGenerator = eGenerator := Subtype.ext vertexE_idempotent
  have hF : F eGenerator = 0 := by
    calc
      F eGenerator = F (vertexE • eGenerator) := congrArg F hfix.symm
      _ = vertexE • F eGenerator := F.map_smul _ _
      _ = 0 := e_smul_simple _
  ext a
  change F a = 0
  rw [← ce_generated a,map_smul,hF,smul_zero]

end
end TachikawaCharZero.Resolution
