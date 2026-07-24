import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F0
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F1
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F2
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F3
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F4
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F5
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F6
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F7
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F8
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F9
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F10
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F11
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F12
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F13
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F14
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F15
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F16
import IdealArithmetic.Examples.NF5_3_379687500_1.PrimesBelow5_3_379687500_1F17

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 952]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 953 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB953I0
  exact PB953I1
  exact PB953I2
  exact PB953I3
  exact PB953I4
  exact PB953I5
  exact PB953I6
  exact PB953I7
  exact PB953I8
  exact PB953I9
  exact PB953I10
  exact PB953I11
  exact PB953I12
  exact PB953I13
  exact PB953I14
  exact PB953I15
  exact PB953I16
  exact PB953I17

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB953 : PrimesBelowBoundCertificate O 953 := by
  refine primesBelowBoundCertificate_of_Interval O eC 952 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 952 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 952 hC

lemma cert_eq_𝔭 : PB953.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 952 rfl rfl hel hC
