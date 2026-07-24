import IdealArithmetic.Examples.NF3_1_213716_1.PrimesBelow3_1_213716_1F0
import IdealArithmetic.Examples.NF3_1_213716_1.PrimesBelow3_1_213716_1F1
import IdealArithmetic.Examples.NF3_1_213716_1.PrimesBelow3_1_213716_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 130]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 131 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB131I0
  exact PB131I1
  exact PB131I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB131 : PrimesBelowBoundCertificate O 131 := by
  refine primesBelowBoundCertificate_of_Interval O eC 130 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 130 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 130 hC

lemma cert_eq_𝔭 : PB131.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 130 rfl rfl hel hC
