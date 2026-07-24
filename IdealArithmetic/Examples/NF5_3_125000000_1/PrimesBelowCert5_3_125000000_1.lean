import IdealArithmetic.Examples.NF5_3_125000000_1.PrimesBelow5_3_125000000_1F0
import IdealArithmetic.Examples.NF5_3_125000000_1.PrimesBelow5_3_125000000_1F1
import IdealArithmetic.Examples.NF5_3_125000000_1.PrimesBelow5_3_125000000_1F2
import IdealArithmetic.Examples.NF5_3_125000000_1.PrimesBelow5_3_125000000_1F3
import IdealArithmetic.Examples.NF5_3_125000000_1.PrimesBelow5_3_125000000_1F4
import IdealArithmetic.Examples.NF5_3_125000000_1.PrimesBelow5_3_125000000_1F5
import IdealArithmetic.Examples.NF5_3_125000000_1.PrimesBelow5_3_125000000_1F6
import IdealArithmetic.Examples.NF5_3_125000000_1.PrimesBelow5_3_125000000_1F7
import IdealArithmetic.Examples.NF5_3_125000000_1.PrimesBelow5_3_125000000_1F8
import IdealArithmetic.Examples.NF5_3_125000000_1.PrimesBelow5_3_125000000_1F9
import IdealArithmetic.Examples.NF5_3_125000000_1.PrimesBelow5_3_125000000_1F10
import IdealArithmetic.Examples.NF5_3_125000000_1.PrimesBelow5_3_125000000_1F11

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 546]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 547 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB547I0
  exact PB547I1
  exact PB547I2
  exact PB547I3
  exact PB547I4
  exact PB547I5
  exact PB547I6
  exact PB547I7
  exact PB547I8
  exact PB547I9
  exact PB547I10
  exact PB547I11

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB547 : PrimesBelowBoundCertificate O 547 := by
  refine primesBelowBoundCertificate_of_Interval O eC 546 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 546 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 546 hC

lemma cert_eq_𝔭 : PB547.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 546 rfl rfl hel hC
