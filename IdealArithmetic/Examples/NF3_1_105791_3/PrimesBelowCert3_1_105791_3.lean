import IdealArithmetic.Examples.NF3_1_105791_3.PrimesBelow3_1_105791_3F0
import IdealArithmetic.Examples.NF3_1_105791_3.PrimesBelow3_1_105791_3F1
import IdealArithmetic.Examples.NF3_1_105791_3.PrimesBelow3_1_105791_3F2

noncomputable section
abbrev eC := ![1, 31, 79, 92]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 93 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB93I0
  exact PB93I1
  exact PB93I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB93 : PrimesBelowBoundCertificate O 93 := by
  refine primesBelowBoundCertificate_of_Interval O eC 92 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 92 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 92 hC

lemma cert_eq_𝔭 : PB93.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 92 rfl rfl hel hC
