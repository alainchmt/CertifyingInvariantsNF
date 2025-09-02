import IdealArithmetic.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import IdealArithmetic.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^5 + 20*X - 16 : ℤ[X])

local notation "l" => [-16, 20, 0, 0, 0, 1]

unseal Rat.add Rat.mul Rat.inv

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 1
 P := 3209
 M := 5
 r := 11/4
 ρ := 19761/5324
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide
 hrho := by decide
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 
