import IdealArithmetic.Examples.NF3_1_226175_1.PrimesBelow3_1_226175_1F0
import IdealArithmetic.Examples.NF3_1_226175_1.PrimesBelow3_1_226175_1F1
import IdealArithmetic.Examples.NF3_1_226175_1.PrimesBelow3_1_226175_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 134]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 135 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB135I0
  exact PB135I1
  exact PB135I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB135 : PrimesBelowBoundCertificate O 135 := by
  refine primesBelowBoundCertificate_of_Interval O eC 134 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 134 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 134 hC

lemma cert_eq_𝔭 : PB135.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 134 rfl rfl hel hC
