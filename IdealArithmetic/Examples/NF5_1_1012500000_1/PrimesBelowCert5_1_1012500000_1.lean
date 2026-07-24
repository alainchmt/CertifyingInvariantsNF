import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F0
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F1
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F2
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F3
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F4
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F5
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F6
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F7
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F8
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F9
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F10
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F11
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F12
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F13
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F14
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F15
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F16
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F17
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F18
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F19
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F20
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F21
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F22
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F23
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F24
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F25
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F26
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F27
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F28
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F29
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F30
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F31
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F32
import IdealArithmetic.Examples.NF5_1_1012500000_1.PrimesBelow5_1_1012500000_1F33

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1321, 1427, 1481, 1543, 1601, 1663, 1733, 1801, 1877, 1951, 1980]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 1981 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB1981I0
  exact PB1981I1
  exact PB1981I2
  exact PB1981I3
  exact PB1981I4
  exact PB1981I5
  exact PB1981I6
  exact PB1981I7
  exact PB1981I8
  exact PB1981I9
  exact PB1981I10
  exact PB1981I11
  exact PB1981I12
  exact PB1981I13
  exact PB1981I14
  exact PB1981I15
  exact PB1981I16
  exact PB1981I17
  exact PB1981I18
  exact PB1981I19
  exact PB1981I20
  exact PB1981I21
  exact PB1981I22
  exact PB1981I23
  exact PB1981I24
  exact PB1981I25
  exact PB1981I26
  exact PB1981I27
  exact PB1981I28
  exact PB1981I29
  exact PB1981I30
  exact PB1981I31
  exact PB1981I32
  exact PB1981I33

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB1981 : PrimesBelowBoundCertificate O 1981 := by
  refine primesBelowBoundCertificate_of_Interval O eC 1980 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 1980 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 1980 hC

lemma cert_eq_𝔭 : PB1981.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 1980 rfl rfl hel hC
