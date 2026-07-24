import IdealArithmetic.Examples.NF3_1_325983_1.PrimesBelow3_1_325983_1F0
import IdealArithmetic.Examples.NF3_1_325983_1.PrimesBelow3_1_325983_1F1
import IdealArithmetic.Examples.NF3_1_325983_1.PrimesBelow3_1_325983_1F2
import IdealArithmetic.Examples.NF3_1_325983_1.PrimesBelow3_1_325983_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 161]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 162 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB162I0
  exact PB162I1
  exact PB162I2
  exact PB162I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB162 : PrimesBelowBoundCertificate O 162 := by
  refine primesBelowBoundCertificate_of_Interval O eC 161 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 161 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 161 hC

lemma cert_eq_𝔭 : PB162.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 161 rfl rfl hel hC
