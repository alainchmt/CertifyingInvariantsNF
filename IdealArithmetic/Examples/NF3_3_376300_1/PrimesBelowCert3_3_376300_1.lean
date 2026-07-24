import IdealArithmetic.Examples.NF3_3_376300_1.PrimesBelow3_3_376300_1F0
import IdealArithmetic.Examples.NF3_3_376300_1.PrimesBelow3_3_376300_1F1
import IdealArithmetic.Examples.NF3_3_376300_1.PrimesBelow3_3_376300_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 136]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 137 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB137I0
  exact PB137I1
  exact PB137I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB137 : PrimesBelowBoundCertificate O 137 := by
  refine primesBelowBoundCertificate_of_Interval O eC 136 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 136 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 136 hC

lemma cert_eq_𝔭 : PB137.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 136 rfl rfl hel hC
