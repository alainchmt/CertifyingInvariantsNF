import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F0
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F1
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F2
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F3
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F4
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F5
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F6
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F7
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F8
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F9
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F10
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F11
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F12
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F13
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F14
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F15
import IdealArithmetic.Examples.NF5_3_303750000_1.PrimesBelow5_3_303750000_1F16

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 852]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 853 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB853I0
  exact PB853I1
  exact PB853I2
  exact PB853I3
  exact PB853I4
  exact PB853I5
  exact PB853I6
  exact PB853I7
  exact PB853I8
  exact PB853I9
  exact PB853I10
  exact PB853I11
  exact PB853I12
  exact PB853I13
  exact PB853I14
  exact PB853I15
  exact PB853I16

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB853 : PrimesBelowBoundCertificate O 853 := by
  refine primesBelowBoundCertificate_of_Interval O eC 852 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 852 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 852 hC

lemma cert_eq_𝔭 : PB853.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 852 rfl rfl hel hC
