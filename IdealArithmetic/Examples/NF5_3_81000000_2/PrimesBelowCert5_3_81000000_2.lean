import IdealArithmetic.Examples.NF5_3_81000000_2.PrimesBelow5_3_81000000_2F0
import IdealArithmetic.Examples.NF5_3_81000000_2.PrimesBelow5_3_81000000_2F1
import IdealArithmetic.Examples.NF5_3_81000000_2.PrimesBelow5_3_81000000_2F2
import IdealArithmetic.Examples.NF5_3_81000000_2.PrimesBelow5_3_81000000_2F3
import IdealArithmetic.Examples.NF5_3_81000000_2.PrimesBelow5_3_81000000_2F4
import IdealArithmetic.Examples.NF5_3_81000000_2.PrimesBelow5_3_81000000_2F5
import IdealArithmetic.Examples.NF5_3_81000000_2.PrimesBelow5_3_81000000_2F6
import IdealArithmetic.Examples.NF5_3_81000000_2.PrimesBelow5_3_81000000_2F7
import IdealArithmetic.Examples.NF5_3_81000000_2.PrimesBelow5_3_81000000_2F8
import IdealArithmetic.Examples.NF5_3_81000000_2.PrimesBelow5_3_81000000_2F9

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 440]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 441 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB441I0
  exact PB441I1
  exact PB441I2
  exact PB441I3
  exact PB441I4
  exact PB441I5
  exact PB441I6
  exact PB441I7
  exact PB441I8
  exact PB441I9

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB441 : PrimesBelowBoundCertificate O 441 := by
  refine primesBelowBoundCertificate_of_Interval O eC 440 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 440 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 440 hC

lemma cert_eq_𝔭 : PB441.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 440 rfl rfl hel hC
