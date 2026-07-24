import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F0
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F1
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F2
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F3
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F4
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F5
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F6
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F7
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F8
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F9
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F10
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F11
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F12
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F13
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F14
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F15
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F16
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F17
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F18
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F19
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F20
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F21
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F22
import IdealArithmetic.Examples.NF5_3_729000000_4.PrimesBelow5_3_729000000_4F23

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1320]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 1321 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB1321I0
  exact PB1321I1
  exact PB1321I2
  exact PB1321I3
  exact PB1321I4
  exact PB1321I5
  exact PB1321I6
  exact PB1321I7
  exact PB1321I8
  exact PB1321I9
  exact PB1321I10
  exact PB1321I11
  exact PB1321I12
  exact PB1321I13
  exact PB1321I14
  exact PB1321I15
  exact PB1321I16
  exact PB1321I17
  exact PB1321I18
  exact PB1321I19
  exact PB1321I20
  exact PB1321I21
  exact PB1321I22
  exact PB1321I23

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB1321 : PrimesBelowBoundCertificate O 1321 := by
  refine primesBelowBoundCertificate_of_Interval O eC 1320 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 1320 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 1320 hC

lemma cert_eq_𝔭 : PB1321.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 1320 rfl rfl hel hC
