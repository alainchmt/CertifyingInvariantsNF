import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F0
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F1
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F2
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F3
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F4
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F5
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F6
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F7
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F8
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F9
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F10
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F11
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F12
import IdealArithmetic.Examples.NF5_3_202500000_3.PrimesBelow5_3_202500000_3F13

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 695]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 696 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB696I0
  exact PB696I1
  exact PB696I2
  exact PB696I3
  exact PB696I4
  exact PB696I5
  exact PB696I6
  exact PB696I7
  exact PB696I8
  exact PB696I9
  exact PB696I10
  exact PB696I11
  exact PB696I12
  exact PB696I13

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB696 : PrimesBelowBoundCertificate O 696 := by
  refine primesBelowBoundCertificate_of_Interval O eC 695 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 695 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 695 hC

lemma cert_eq_𝔭 : PB696.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 695 rfl rfl hel hC
