import IdealArithmetic.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => (X^5 - 10*X^2 - 285*X + 774 : ℤ[X])

local notation "l" => [774, -285, -10, 0, 0, 1]

lemma T_ofList' : T = ofList l := by norm_num ; ring 
    
instance hp11' : Fact $ Nat.Prime 11 := fact_iff.2 (by norm_num)

def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [4, 1, 1, 0, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 4, 7, 9, 2], [2, 5, 6, 3, 3], [4, 10, 4, 0, 5], [9, 2, 5, 10, 1], [0, 1]]
 g := ![![[1], [1], []],![[7, 10, 0, 4, 6, 2, 8, 2], [0, 2, 5, 1, 7, 2, 2, 2], [6, 10, 3, 4]],![[1, 10, 4, 1, 9, 7, 4, 3], [3, 1, 3, 9, 7, 2, 3, 4], [2, 1, 7, 9]],![[7, 7, 4, 3, 3, 10, 4, 1], [1, 8, 0, 4, 7, 10, 1, 9], [9, 7, 0, 3]],![[5, 9, 8, 5, 4, 5, 8, 9], [8, 6, 1, 9, 5, 0, 6, 5], [4, 0, 9, 1]]]
 h' := ![![[7, 4, 7, 9, 2], [7, 10, 10], [0, 0, 1], [0, 1]],![[2, 5, 6, 3, 3], [8, 8, 6, 3, 10], [3, 10, 9, 10, 10], [7, 4, 7, 9, 2]],![[4, 10, 4, 0, 5], [9, 3, 9, 2, 1], [7, 3, 7, 6, 7], [2, 5, 6, 3, 3]],![[9, 2, 5, 10, 1], [1, 2, 1, 5, 8], [2, 10, 6, 6, 9], [4, 10, 4, 0, 5]],![[0, 1], [10, 10, 7, 1, 3], [10, 10, 10, 0, 7], [9, 2, 5, 10, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 9, 7, 1], [], [], []]
 b := ![[], [3, 10, 7, 7, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

noncomputable def C : IrreducibleCertificateIntPolynomial T l where
 hpol := T_ofList'
 n := 1
 d := 5
 hprim := by decide
 hdeg := by decide
 hnn := by decide
 hdn := by decide
 p := ![11]
 hp := by 
  intro i
  fin_cases i
  exact hp11'.out
 hlc := by decide
 m := ![1]
 F := fun i =>
  match i with 
  | 0 => ![[4, 1, 1, 0, 0, 1]]
 D := fun i =>
  match i with 
  | 0 => ![5]
 hl := by decide
 hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j
  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
 hm := by decide
 hprod := by decide
 hinter := by decide

theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C 
