import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F0
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F1
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F2
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F3
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F4
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F5
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F6
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F7
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F8
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F9
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F10
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F11
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F12
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F13
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F14
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F15
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F16
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F17
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F18
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F19
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F20
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F21
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F22
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F23
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F24
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F25
import IdealArithmetic.Examples.NF5_1_607500000_5.PrimesBelow5_1_607500000_5F26

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1321, 1427, 1481, 1534]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 1535 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB1535I0
  exact PB1535I1
  exact PB1535I2
  exact PB1535I3
  exact PB1535I4
  exact PB1535I5
  exact PB1535I6
  exact PB1535I7
  exact PB1535I8
  exact PB1535I9
  exact PB1535I10
  exact PB1535I11
  exact PB1535I12
  exact PB1535I13
  exact PB1535I14
  exact PB1535I15
  exact PB1535I16
  exact PB1535I17
  exact PB1535I18
  exact PB1535I19
  exact PB1535I20
  exact PB1535I21
  exact PB1535I22
  exact PB1535I23
  exact PB1535I24
  exact PB1535I25
  exact PB1535I26

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB1535 : PrimesBelowBoundCertificate O 1535 := by
  refine primesBelowBoundCertificate_of_Interval O eC 1534 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 1534 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 1534 hC

lemma cert_eq_𝔭 : PB1535.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 1534 rfl rfl hel hC
