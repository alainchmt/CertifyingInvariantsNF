import IdealArithmetic.DedekindProject.Polynomial.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^10 - 3*X^9 + 3*X^8 - 6*X^7 + 11*X^6 - 5*X^5 + 7*X^4 - 11*X^3 + 3*X + 1 : ℤ[X])

local notation "l" => [1, 3, 0, -11, 7, -5, 11, -6, 3, -3, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring
instance hp2' : Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)

def P2PI0 : CertificateIrreducibleZModOfList' 2 10 2 1 [1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1] where
 m := 2
 P := ![2, 5]
 exp := ![1, 1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, 1, 0, 1, 1, 1, 1, 1, 1], [1, 0, 0, 1, 1, 1, 0, 0, 1], [1, 1, 1, 1, 0, 0, 1, 1, 1], [0, 0, 1, 0, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 1, 1, 1, 1, 0, 0, 1], [0, 1]]
 g := ![![[]], ![[]], ![[]], ![[1, 1, 0, 1, 0, 1, 1]], ![[0, 0, 0, 1, 1, 0, 1, 1, 1]], ![[0, 1, 0, 1, 0, 1, 1]], ![[1, 1, 1, 0, 1, 1, 1]], ![[1, 1, 1, 1, 0, 1, 0, 1, 1]], ![[0, 0, 0, 1, 0, 1, 0, 1, 1]], ![[1, 0, 0, 1, 0, 1, 0, 1, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[0, 0, 0, 0, 1], [0, 0, 1]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1]], ![[1, 0, 1, 0, 1, 1, 1, 1, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[1, 0, 0, 1, 1, 1, 0, 0, 1], [1, 0, 1, 0, 1, 1, 1, 1, 1, 1]], ![[1, 1, 1, 1, 0, 0, 1, 1, 1], [1, 0, 0, 1, 1, 1, 0, 0, 1]], ![[0, 0, 1, 0, 0, 1, 0, 0, 0, 1], [1, 1, 1, 1, 0, 0, 1, 1, 1]], ![[1, 0, 0, 1, 0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0, 0, 0, 1]], ![[1, 0, 0, 1, 1, 1, 1, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 0, 0, 1]], ![[0, 1], [1, 0, 0, 1, 1, 1, 1, 0, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 0, 1, 1], [], [], [1, 0, 1, 0, 1, 0, 1, 1], [], [], [], []]
 b := ![[], [], [1, 1, 1, 1, 1, 0, 1, 0, 0, 1], [], [], [0, 1, 0, 0, 1, 1, 1, 0, 0, 1], [], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 1
 d := 10
 hprim := by decide
 hdeg := by decide
 hnn := by decide
 hdn := by decide
 p := ![2]
 hp := by
  intro i
  fin_cases i
  exact hp2'.out
 hlc := by decide
 m := ![1]
 F := fun i =>
  match i with
  | 0 => ![[1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1]]
 D := fun i =>
  match i with
  | 0 => ![10]
 hl := by decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P2PI0
 hm := by decide
 hprod := by decide
 hinter := by decide

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C
