import IdealArithmetic.Examples.NF5_1_27000000_1.PrimesBelow5_1_27000000_1F0
import IdealArithmetic.Examples.NF5_1_27000000_1.PrimesBelow5_1_27000000_1F1
import IdealArithmetic.Examples.NF5_1_27000000_1.PrimesBelow5_1_27000000_1F2
import IdealArithmetic.Examples.NF5_1_27000000_1.PrimesBelow5_1_27000000_1F3
import IdealArithmetic.Examples.NF5_1_27000000_1.PrimesBelow5_1_27000000_1F4
import IdealArithmetic.Examples.NF5_1_27000000_1.PrimesBelow5_1_27000000_1F5
import IdealArithmetic.Examples.NF5_1_27000000_1.PrimesBelow5_1_27000000_1F6
import IdealArithmetic.Examples.NF5_1_27000000_1.PrimesBelow5_1_27000000_1F7

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 323]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 324 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB324I0
  exact PB324I1
  exact PB324I2
  exact PB324I3
  exact PB324I4
  exact PB324I5
  exact PB324I6
  exact PB324I7

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB324 : PrimesBelowBoundCertificate O 324 := by
  refine primesBelowBoundCertificate_of_Interval O eC 323 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 323 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 323 hC

lemma cert_eq_𝔭 : PB324.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 323 rfl rfl hel hC
