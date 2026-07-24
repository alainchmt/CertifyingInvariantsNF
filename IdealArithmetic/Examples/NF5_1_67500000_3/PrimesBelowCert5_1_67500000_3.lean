import IdealArithmetic.Examples.NF5_1_67500000_3.PrimesBelow5_1_67500000_3F0
import IdealArithmetic.Examples.NF5_1_67500000_3.PrimesBelow5_1_67500000_3F1
import IdealArithmetic.Examples.NF5_1_67500000_3.PrimesBelow5_1_67500000_3F2
import IdealArithmetic.Examples.NF5_1_67500000_3.PrimesBelow5_1_67500000_3F3
import IdealArithmetic.Examples.NF5_1_67500000_3.PrimesBelow5_1_67500000_3F4
import IdealArithmetic.Examples.NF5_1_67500000_3.PrimesBelow5_1_67500000_3F5
import IdealArithmetic.Examples.NF5_1_67500000_3.PrimesBelow5_1_67500000_3F6
import IdealArithmetic.Examples.NF5_1_67500000_3.PrimesBelow5_1_67500000_3F7
import IdealArithmetic.Examples.NF5_1_67500000_3.PrimesBelow5_1_67500000_3F8
import IdealArithmetic.Examples.NF5_1_67500000_3.PrimesBelow5_1_67500000_3F9
import IdealArithmetic.Examples.NF5_1_67500000_3.PrimesBelow5_1_67500000_3F10

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 511]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 512 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB512I0
  exact PB512I1
  exact PB512I2
  exact PB512I3
  exact PB512I4
  exact PB512I5
  exact PB512I6
  exact PB512I7
  exact PB512I8
  exact PB512I9
  exact PB512I10

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB512 : PrimesBelowBoundCertificate O 512 := by
  refine primesBelowBoundCertificate_of_Interval O eC 511 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 511 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 511 hC

lemma cert_eq_𝔭 : PB512.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 511 rfl rfl hel hC
