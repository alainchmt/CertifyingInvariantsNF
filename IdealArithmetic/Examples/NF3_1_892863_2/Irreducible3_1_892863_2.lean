import IdealArithmetic.DedekindProject.Polynomial.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import IdealArithmetic.DedekindProject.Polynomial.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^3 + 105*X - 598 : ℤ[X])

local notation "l" => [-598, 105, 0, 1]

unseal Rat.add Rat.mul Rat.inv

lemma T_ofList' : T = ofList l := by norm_num ; ring
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 12
 P := 3929
 M := -35
 r := 41/4
 ρ := 3361/164
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide
 hrho := by decide
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C
