import IdealArithmetic.Examples.NF3_3_157300_2.PrimesBelow3_3_157300_2F0
import IdealArithmetic.Examples.NF3_3_157300_2.PrimesBelow3_3_157300_2F1
import IdealArithmetic.Examples.NF3_3_157300_2.PrimesBelow3_3_157300_2F2

noncomputable section
abbrev eC := ![1, 31, 79, 88]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 89 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB89I0
  exact PB89I1
  exact PB89I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB89 : PrimesBelowBoundCertificate O 89 := by
  refine primesBelowBoundCertificate_of_Interval O eC 88 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 88 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 88 hC

lemma cert_eq_𝔭 : PB89.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 88 rfl rfl hel hC
