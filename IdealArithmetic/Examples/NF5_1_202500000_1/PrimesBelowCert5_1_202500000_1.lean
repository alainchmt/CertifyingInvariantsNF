import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F0
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F1
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F2
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F3
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F4
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F5
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F6
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F7
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F8
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F9
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F10
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F11
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F12
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F13
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F14
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F15
import IdealArithmetic.Examples.NF5_1_202500000_1.PrimesBelow5_1_202500000_1F16

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 885]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 886 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB886I0
  exact PB886I1
  exact PB886I2
  exact PB886I3
  exact PB886I4
  exact PB886I5
  exact PB886I6
  exact PB886I7
  exact PB886I8
  exact PB886I9
  exact PB886I10
  exact PB886I11
  exact PB886I12
  exact PB886I13
  exact PB886I14
  exact PB886I15
  exact PB886I16

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB886 : PrimesBelowBoundCertificate O 886 := by
  refine primesBelowBoundCertificate_of_Interval O eC 885 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 885 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 885 hC

lemma cert_eq_𝔭 : PB886.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 885 rfl rfl hel hC
