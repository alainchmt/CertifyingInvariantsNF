import IdealArithmetic.Examples.NF3_1_58604_2.PrimesBelow3_1_58604_2F0
import IdealArithmetic.Examples.NF3_1_58604_2.PrimesBelow3_1_58604_2F1

noncomputable section
abbrev eC := ![1, 31, 68]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 69 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB69I0
  exact PB69I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB69 : PrimesBelowBoundCertificate O 69 := by
  refine primesBelowBoundCertificate_of_Interval O eC 68 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 68 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 68 hC

lemma cert_eq_𝔭 : PB69.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 68 rfl rfl hel hC
