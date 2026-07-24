import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F0
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F1
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F2
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F3
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F4
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F5
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F6
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F7
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F8
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F9
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F10
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F11
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F12
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F13
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F14
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F15
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F16
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F17
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F18
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F19
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F20
import IdealArithmetic.Examples.NF5_1_364500000_3.PrimesBelow5_1_364500000_3F21

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1188]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 1189 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB1189I0
  exact PB1189I1
  exact PB1189I2
  exact PB1189I3
  exact PB1189I4
  exact PB1189I5
  exact PB1189I6
  exact PB1189I7
  exact PB1189I8
  exact PB1189I9
  exact PB1189I10
  exact PB1189I11
  exact PB1189I12
  exact PB1189I13
  exact PB1189I14
  exact PB1189I15
  exact PB1189I16
  exact PB1189I17
  exact PB1189I18
  exact PB1189I19
  exact PB1189I20
  exact PB1189I21

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB1189 : PrimesBelowBoundCertificate O 1189 := by
  refine primesBelowBoundCertificate_of_Interval O eC 1188 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 1188 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 1188 hC

lemma cert_eq_𝔭 : PB1189.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 1188 rfl rfl hel hC
