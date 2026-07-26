import IdealArithmetic.DedekindProject.Polynomial.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import IdealArithmetic.DedekindProject.Polynomial.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => (X^8 - 4*X^7 + 8*X^6 - 10*X^5 + 11*X^4 - 10*X^3 + 2*X^2 + 2*X + 1 : ℤ[X])

local notation "l" => [1, 2, 2, -10, 11, -10, 8, -4, 1]

unseal Rat.add Rat.mul Rat.inv

lemma T_ofList' : T = ofList l := by norm_num ; ring
instance hp13' : Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)

def P13PI0 : CertificateIrreducibleZModOfList' 13 4 2 3 [1, 9, 2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 8], [6, 12], [1, 5], [0, 1]]
 g := ![![[8, 12, 0, 10], [12, 12, 1], []], ![[5, 12, 6, 11], [6, 7, 12], []], ![[4, 0, 11, 3], [3, 2, 1], []], ![[4, 2, 9, 2], [12, 5, 12], []]]
 h' := ![![[5, 8], [1, 10, 10, 7], [0, 0, 0, 1], [0, 1]], ![[6, 12], [6, 10, 2, 9], [8, 2, 11, 5], [5, 8]], ![[1, 5], [9, 11, 6, 6], [8, 9, 5, 12], [6, 12]], ![[0, 1], [2, 8, 8, 4], [1, 2, 10, 8], [1, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6], []]
 b := ![[], [], [10, 3, 12, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P13PI1 : CertificateIrreducibleZModOfList' 13 4 2 3 [1, 6, 11, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 8], [9, 12], [8, 5], [0, 1]]
 g := ![![[12, 12, 0, 3], [1, 5, 1], []], ![[1, 12, 4, 2], [7, 4, 12], []], ![[6, 0, 3, 10], [10, 3, 1], []], ![[6, 2, 6, 11], [1, 1, 12], []]]
 h' := ![![[1, 8], [12, 2, 10, 9], [0, 0, 0, 1], [0, 1]], ![[9, 12], [7, 2, 2, 6], [1, 11, 10, 5], [1, 8]], ![[8, 5], [4, 10, 6, 4], [1, 4, 1, 12], [9, 12]], ![[0, 1], [11, 12, 8, 7], [5, 11, 2, 8], [8, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6], []]
 b := ![[], [], [11, 10, 5, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

noncomputable def C : CertificateIrreducibleIntOfPrimeDegreeAnalysis T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 n := 1
 d := 4
 s := 441
 P := 338141
 M := 11
 r := 2
 ρ := 6
 hPPrime := by norm_num
 hrpos := by norm_num
 hnn := by decide
 hdn := by decide
 p := ![13]
 hp := by
  intro i
  fin_cases i
  exact hp13'.out
 hlc := by decide
 m := ![2]
 F := fun i =>
  match i with
  | 0 => ![[1, 9, 2, 1, 1], [1, 6, 11, 8, 1]]
 D := fun i =>
  match i with
  | 0 => ![4, 4]
 hl := by decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13PI0
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P13PI1
 hm := by decide
 hprod := by decide
 hinter := by decide
 hrhoeq := by decide
 hrho := by decide
 hs := by norm_num
 heval := by norm_num

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrimeDegrees _ _ C
