import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F0
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F1
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F2
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F3
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F4
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F5
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F6
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F7
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F8
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F9
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F10
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F11
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F12
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F13
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F14
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F15
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F16
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F17
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F18
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F19
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F20
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F21
import IdealArithmetic.Examples.NF5_1_405000000_12.PrimesBelow5_1_405000000_12F22

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1252]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 1253 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB1253I0
  exact PB1253I1
  exact PB1253I2
  exact PB1253I3
  exact PB1253I4
  exact PB1253I5
  exact PB1253I6
  exact PB1253I7
  exact PB1253I8
  exact PB1253I9
  exact PB1253I10
  exact PB1253I11
  exact PB1253I12
  exact PB1253I13
  exact PB1253I14
  exact PB1253I15
  exact PB1253I16
  exact PB1253I17
  exact PB1253I18
  exact PB1253I19
  exact PB1253I20
  exact PB1253I21
  exact PB1253I22

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB1253 : PrimesBelowBoundCertificate O 1253 := by
  refine primesBelowBoundCertificate_of_Interval O eC 1252 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 1252 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 1252 hC

lemma cert_eq_𝔭 : PB1253.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 1252 rfl rfl hel hC
