import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F0
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F1
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F2
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F3
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F4
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F5
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F6
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F7
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F8
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F9
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F10
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F11
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F12
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F13
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F14
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F15
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F16
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F17
import IdealArithmetic.Examples.NF5_3_405000000_1.PrimesBelow5_3_405000000_1F18

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 983]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 984 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB984I0
  exact PB984I1
  exact PB984I2
  exact PB984I3
  exact PB984I4
  exact PB984I5
  exact PB984I6
  exact PB984I7
  exact PB984I8
  exact PB984I9
  exact PB984I10
  exact PB984I11
  exact PB984I12
  exact PB984I13
  exact PB984I14
  exact PB984I15
  exact PB984I16
  exact PB984I17
  exact PB984I18

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB984 : PrimesBelowBoundCertificate O 984 := by
  refine primesBelowBoundCertificate_of_Interval O eC 983 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 983 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 983 hC

lemma cert_eq_𝔭 : PB984.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 983 rfl rfl hel hC
