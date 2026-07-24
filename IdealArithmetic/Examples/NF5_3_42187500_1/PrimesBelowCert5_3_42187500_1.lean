import IdealArithmetic.Examples.NF5_3_42187500_1.PrimesBelow5_3_42187500_1F0
import IdealArithmetic.Examples.NF5_3_42187500_1.PrimesBelow5_3_42187500_1F1
import IdealArithmetic.Examples.NF5_3_42187500_1.PrimesBelow5_3_42187500_1F2
import IdealArithmetic.Examples.NF5_3_42187500_1.PrimesBelow5_3_42187500_1F3
import IdealArithmetic.Examples.NF5_3_42187500_1.PrimesBelow5_3_42187500_1F4
import IdealArithmetic.Examples.NF5_3_42187500_1.PrimesBelow5_3_42187500_1F5
import IdealArithmetic.Examples.NF5_3_42187500_1.PrimesBelow5_3_42187500_1F6
import IdealArithmetic.Examples.NF5_3_42187500_1.PrimesBelow5_3_42187500_1F7

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 317]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 318 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB318I0
  exact PB318I1
  exact PB318I2
  exact PB318I3
  exact PB318I4
  exact PB318I5
  exact PB318I6
  exact PB318I7

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB318 : PrimesBelowBoundCertificate O 318 := by
  refine primesBelowBoundCertificate_of_Interval O eC 317 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 317 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 317 hC

lemma cert_eq_𝔭 : PB318.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 317 rfl rfl hel hC
