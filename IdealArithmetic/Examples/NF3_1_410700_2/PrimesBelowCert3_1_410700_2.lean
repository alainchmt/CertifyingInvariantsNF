import IdealArithmetic.Examples.NF3_1_410700_2.PrimesBelow3_1_410700_2F0
import IdealArithmetic.Examples.NF3_1_410700_2.PrimesBelow3_1_410700_2F1
import IdealArithmetic.Examples.NF3_1_410700_2.PrimesBelow3_1_410700_2F2
import IdealArithmetic.Examples.NF3_1_410700_2.PrimesBelow3_1_410700_2F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 181]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 182 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB182I0
  exact PB182I1
  exact PB182I2
  exact PB182I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB182 : PrimesBelowBoundCertificate O 182 := by
  refine primesBelowBoundCertificate_of_Interval O eC 181 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 181 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 181 hC

lemma cert_eq_𝔭 : PB182.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 181 rfl rfl hel hC
