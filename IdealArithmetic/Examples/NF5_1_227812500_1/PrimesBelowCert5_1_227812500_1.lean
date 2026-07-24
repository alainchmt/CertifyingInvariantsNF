import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F0
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F1
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F2
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F3
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F4
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F5
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F6
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F7
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F8
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F9
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F10
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F11
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F12
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F13
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F14
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F15
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F16
import IdealArithmetic.Examples.NF5_1_227812500_1.PrimesBelow5_1_227812500_1F17

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 939]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 940 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB940I0
  exact PB940I1
  exact PB940I2
  exact PB940I3
  exact PB940I4
  exact PB940I5
  exact PB940I6
  exact PB940I7
  exact PB940I8
  exact PB940I9
  exact PB940I10
  exact PB940I11
  exact PB940I12
  exact PB940I13
  exact PB940I14
  exact PB940I15
  exact PB940I16
  exact PB940I17

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB940 : PrimesBelowBoundCertificate O 940 := by
  refine primesBelowBoundCertificate_of_Interval O eC 939 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 939 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 939 hC

lemma cert_eq_𝔭 : PB940.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 939 rfl rfl hel hC
