import IdealArithmetic.Examples.NF3_1_181804_1.PrimesBelow3_1_181804_1F0
import IdealArithmetic.Examples.NF3_1_181804_1.PrimesBelow3_1_181804_1F1
import IdealArithmetic.Examples.NF3_1_181804_1.PrimesBelow3_1_181804_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 120]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 121 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB121I0
  exact PB121I1
  exact PB121I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB121 : PrimesBelowBoundCertificate O 121 := by
  refine primesBelowBoundCertificate_of_Interval O eC 120 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 120 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 120 hC

lemma cert_eq_𝔭 : PB121.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 120 rfl rfl hel hC
