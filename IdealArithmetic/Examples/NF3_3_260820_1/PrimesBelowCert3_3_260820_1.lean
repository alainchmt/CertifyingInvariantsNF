import IdealArithmetic.Examples.NF3_3_260820_1.PrimesBelow3_3_260820_1F0
import IdealArithmetic.Examples.NF3_3_260820_1.PrimesBelow3_3_260820_1F1
import IdealArithmetic.Examples.NF3_3_260820_1.PrimesBelow3_3_260820_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 113]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 114 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB114I0
  exact PB114I1
  exact PB114I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB114 : PrimesBelowBoundCertificate O 114 := by
  refine primesBelowBoundCertificate_of_Interval O eC 113 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 113 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 113 hC

lemma cert_eq_𝔭 : PB114.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 113 rfl rfl hel hC
