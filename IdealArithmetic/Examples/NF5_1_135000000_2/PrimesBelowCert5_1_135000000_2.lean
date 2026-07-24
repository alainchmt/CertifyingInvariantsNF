import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F0
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F1
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F2
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F3
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F4
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F5
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F6
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F7
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F8
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F9
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F10
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F11
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F12
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F13
import IdealArithmetic.Examples.NF5_1_135000000_2.PrimesBelow5_1_135000000_2F14

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 723]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 724 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB724I0
  exact PB724I1
  exact PB724I2
  exact PB724I3
  exact PB724I4
  exact PB724I5
  exact PB724I6
  exact PB724I7
  exact PB724I8
  exact PB724I9
  exact PB724I10
  exact PB724I11
  exact PB724I12
  exact PB724I13
  exact PB724I14

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB724 : PrimesBelowBoundCertificate O 724 := by
  refine primesBelowBoundCertificate_of_Interval O eC 723 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 723 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 723 hC

lemma cert_eq_𝔭 : PB724.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 723 rfl rfl hel hC
