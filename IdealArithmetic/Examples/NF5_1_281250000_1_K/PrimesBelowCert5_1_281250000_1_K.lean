import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF0
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF1
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF2
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF3
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF4
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF5
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF6
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF7
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF8
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF9
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF10
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF11
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF12
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF13
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF14
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF15
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF16
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF17
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF18
import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF19

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
