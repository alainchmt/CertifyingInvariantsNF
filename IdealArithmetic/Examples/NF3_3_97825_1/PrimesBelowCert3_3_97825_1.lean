import IdealArithmetic.Examples.NF3_3_97825_1.PrimesBelow3_3_97825_1F0
import IdealArithmetic.Examples.NF3_3_97825_1.PrimesBelow3_3_97825_1F1

noncomputable section
abbrev eC := ![1, 31, 69]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 70 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB70I0
  exact PB70I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB70 : PrimesBelowBoundCertificate O 70 := by
  refine primesBelowBoundCertificate_of_Interval O eC 69 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 69 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 69 hC

lemma cert_eq_𝔭 : PB70.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 69 rfl rfl hel hC
