import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F0
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F1
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F2
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F3
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F4
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F5
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F6
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F7
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F8
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F9
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F10
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F11
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F12
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F13
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F14
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F15
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F16
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F17
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F18
import IdealArithmetic.Examples.NF5_1_281250000_1.PrimesBelow5_1_281250000_1F19

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1044]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 1045 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB1045I0
  exact PB1045I1
  exact PB1045I2
  exact PB1045I3
  exact PB1045I4
  exact PB1045I5
  exact PB1045I6
  exact PB1045I7
  exact PB1045I8
  exact PB1045I9
  exact PB1045I10
  exact PB1045I11
  exact PB1045I12
  exact PB1045I13
  exact PB1045I14
  exact PB1045I15
  exact PB1045I16
  exact PB1045I17
  exact PB1045I18
  exact PB1045I19

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB1045 : PrimesBelowBoundCertificate O 1045 := by
  refine primesBelowBoundCertificate_of_Interval O eC 1044 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 1044 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 1044 hC

lemma cert_eq_𝔭 : PB1045.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 1044 rfl rfl hel hC
