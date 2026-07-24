import IdealArithmetic.Examples.NF3_3_46965_1.PrimesBelow3_3_46965_1F0
import IdealArithmetic.Examples.NF3_3_46965_1.PrimesBelow3_3_46965_1F1

noncomputable section
abbrev eC := ![1, 31, 48]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 49 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB49I0
  exact PB49I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB49 : PrimesBelowBoundCertificate O 49 := by
  refine primesBelowBoundCertificate_of_Interval O eC 48 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 48 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 48 hC

lemma cert_eq_𝔭 : PB49.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 48 rfl rfl hel hC
