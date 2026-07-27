import IdealArithmetic.DedekindProject.Polynomial.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^9 - X^8 + 5*X^7 - 6*X^6 + 5*X^5 - 14*X^4 - 3*X^3 - 10*X^2 - 3*X - 1 : ℤ[X])

local notation "l" => [-1, -3, -10, -3, -14, 5, -6, 5, -1, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring
instance hp5' : Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def P5PI0 : CertificateIrreducibleZModOfList' 5 9 2 2 [4, 2, 0, 2, 1, 0, 4, 0, 4, 1] where
 m := 1
 P := ![3]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 0, 0, 0, 1], [0, 4, 3, 3, 3, 0, 3, 0, 2], [2, 2, 2, 3, 4, 3, 1, 3], [4, 4, 0, 4, 2, 3, 4, 0, 3], [3, 1, 2, 0, 3, 0, 3, 2, 4], [1, 0, 2, 0, 1, 4, 0, 4], [1, 2, 4, 1, 0, 3, 0, 2, 2], [0, 1, 2, 4, 2, 1, 4, 4, 4], [0, 1]]
 g := ![![[], []], ![[0, 4, 1, 0, 1, 2, 0, 1, 3, 2, 1, 3, 1], [1, 1]], ![[2, 0, 2, 1, 0, 1, 2, 2, 2, 2, 1, 1, 3, 4, 3, 3], [2, 2, 4, 0, 0, 1, 4, 4]], ![[2, 0, 1, 1, 1, 2, 1, 1, 3, 1, 0, 1, 3], [0, 3, 3, 4, 0, 4]], ![[2, 2, 2, 0, 2, 4, 4, 3, 2, 1, 0, 4, 3, 2, 4, 2], [1, 2, 4, 2, 0, 3, 4, 4]], ![[3, 1, 3, 2, 4, 0, 3, 3, 2, 3, 1, 4, 0, 1], [2, 2, 4, 3, 3, 0, 2, 1]], ![[0, 4, 3, 4, 4, 4, 2, 2, 1, 4, 3, 2, 1], [0, 4, 2, 3, 1, 1]], ![[4, 4, 0, 1, 2, 1, 0, 0, 2, 4, 3, 2, 1, 2, 3, 2], [3, 3, 2, 1, 2, 1, 2, 4]], ![[0, 0, 1, 1, 4, 4, 3, 3, 3, 3, 2, 1, 4, 0, 4, 1], [1, 3, 1, 0, 2, 1, 3, 1]]]
 h' := ![![[0, 0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[0, 4, 3, 3, 3, 0, 3, 0, 2], [1, 4, 3, 3, 2, 4, 1, 1, 1], [0, 0, 0, 0, 0, 1]], ![[2, 2, 2, 3, 4, 3, 1, 3], [2, 3, 1, 2, 2, 3, 2, 0, 3], [0, 4, 3, 3, 3, 0, 3, 0, 2]], ![[4, 4, 0, 4, 2, 3, 4, 0, 3], [4, 1, 4, 3, 3, 0, 2, 1], [2, 2, 2, 3, 4, 3, 1, 3]], ![[3, 1, 2, 0, 3, 0, 3, 2, 4], [2, 2, 1, 4, 4, 3, 3, 4, 3], [4, 4, 0, 4, 2, 3, 4, 0, 3]], ![[1, 0, 2, 0, 1, 4, 0, 4], [1, 4, 3, 0, 3, 0, 4, 3], [3, 1, 2, 0, 3, 0, 3, 2, 4]], ![[1, 2, 4, 1, 0, 3, 0, 2, 2], [1, 4, 3, 4, 3, 4, 4, 3], [1, 0, 2, 0, 1, 4, 0, 4]], ![[0, 1, 2, 4, 2, 1, 4, 4, 4], [4, 1, 3, 4, 1, 4, 2, 1, 1], [1, 2, 4, 1, 0, 3, 0, 2, 2]], ![[0, 1], [1, 1, 1, 0, 2, 2, 2, 2, 2], [0, 1, 2, 4, 2, 1, 4, 4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [], [3, 2, 0, 1, 0, 0, 3], [], [], [], [], []]
 b := ![[], [], [], [2, 2, 0, 0, 1, 4, 0, 3, 4], [], [], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 1
 d := 9
 hprim := by decide
 hdeg := by decide
 hnn := by decide
 hdn := by decide
 p := ![5]
 hp := by
  intro i
  fin_cases i
  exact hp5'.out
 hlc := by decide
 m := ![1]
 F := fun i =>
  match i with
  | 0 => ![[4, 2, 0, 2, 1, 0, 4, 0, 4, 1]]
 D := fun i =>
  match i with
  | 0 => ![9]
 hl := by decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P5PI0
 hm := by decide
 hprod := by decide
 hinter := by decide

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C
