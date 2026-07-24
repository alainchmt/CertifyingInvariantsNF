import IdealArithmetic.Examples.NF3_1_125083_1.PrimesBelow3_1_125083_1F0
import IdealArithmetic.Examples.NF3_1_125083_1.PrimesBelow3_1_125083_1F1
import IdealArithmetic.Examples.NF3_1_125083_1.PrimesBelow3_1_125083_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 100]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 101 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB101I0
  exact PB101I1
  exact PB101I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB101 : PrimesBelowBoundCertificate O 101 := by
  refine primesBelowBoundCertificate_of_Interval O eC 100 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 100 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 100 hC

lemma cert_eq_𝔭 : PB101.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 100 rfl rfl hel hC
