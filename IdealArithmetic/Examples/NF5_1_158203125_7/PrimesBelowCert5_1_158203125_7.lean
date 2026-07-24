import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F0
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F1
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F2
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F3
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F4
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F5
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F6
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F7
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F8
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F9
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F10
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F11
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F12
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F13
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F14
import IdealArithmetic.Examples.NF5_1_158203125_7.PrimesBelow5_1_158203125_7F15

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 783]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 784 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB784I0
  exact PB784I1
  exact PB784I2
  exact PB784I3
  exact PB784I4
  exact PB784I5
  exact PB784I6
  exact PB784I7
  exact PB784I8
  exact PB784I9
  exact PB784I10
  exact PB784I11
  exact PB784I12
  exact PB784I13
  exact PB784I14
  exact PB784I15

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB784 : PrimesBelowBoundCertificate O 784 := by
  refine primesBelowBoundCertificate_of_Interval O eC 783 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 783 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 783 hC

lemma cert_eq_𝔭 : PB784.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 783 rfl rfl hel hC
