import IdealArithmetic.Examples.NF5_1_75937500_3.PrimesBelow5_1_75937500_3F0
import IdealArithmetic.Examples.NF5_1_75937500_3.PrimesBelow5_1_75937500_3F1
import IdealArithmetic.Examples.NF5_1_75937500_3.PrimesBelow5_1_75937500_3F2
import IdealArithmetic.Examples.NF5_1_75937500_3.PrimesBelow5_1_75937500_3F3
import IdealArithmetic.Examples.NF5_1_75937500_3.PrimesBelow5_1_75937500_3F4
import IdealArithmetic.Examples.NF5_1_75937500_3.PrimesBelow5_1_75937500_3F5
import IdealArithmetic.Examples.NF5_1_75937500_3.PrimesBelow5_1_75937500_3F6
import IdealArithmetic.Examples.NF5_1_75937500_3.PrimesBelow5_1_75937500_3F7
import IdealArithmetic.Examples.NF5_1_75937500_3.PrimesBelow5_1_75937500_3F8
import IdealArithmetic.Examples.NF5_1_75937500_3.PrimesBelow5_1_75937500_3F9
import IdealArithmetic.Examples.NF5_1_75937500_3.PrimesBelow5_1_75937500_3F10
import IdealArithmetic.Examples.NF5_1_75937500_3.PrimesBelow5_1_75937500_3F11

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 542]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 543 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB543I0
  exact PB543I1
  exact PB543I2
  exact PB543I3
  exact PB543I4
  exact PB543I5
  exact PB543I6
  exact PB543I7
  exact PB543I8
  exact PB543I9
  exact PB543I10
  exact PB543I11

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB543 : PrimesBelowBoundCertificate O 543 := by
  refine primesBelowBoundCertificate_of_Interval O eC 542 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 542 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 542 hC

lemma cert_eq_𝔭 : PB543.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 542 rfl rfl hel hC
