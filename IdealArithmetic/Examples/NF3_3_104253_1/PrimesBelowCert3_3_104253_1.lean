import IdealArithmetic.Examples.NF3_3_104253_1.PrimesBelow3_3_104253_1F0
import IdealArithmetic.Examples.NF3_3_104253_1.PrimesBelow3_3_104253_1F1

noncomputable section
abbrev eC := ![1, 31, 71]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 72 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB72I0
  exact PB72I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB72 : PrimesBelowBoundCertificate O 72 := by
  refine primesBelowBoundCertificate_of_Interval O eC 71 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 71 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 71 hC

lemma cert_eq_𝔭 : PB72.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 71 rfl rfl hel hC
