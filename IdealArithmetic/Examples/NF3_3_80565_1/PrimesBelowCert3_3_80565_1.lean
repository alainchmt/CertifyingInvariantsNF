import IdealArithmetic.Examples.NF3_3_80565_1.PrimesBelow3_3_80565_1F0
import IdealArithmetic.Examples.NF3_3_80565_1.PrimesBelow3_3_80565_1F1

noncomputable section
abbrev eC := ![1, 31, 63]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 64 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB64I0
  exact PB64I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB64 : PrimesBelowBoundCertificate O 64 := by
  refine primesBelowBoundCertificate_of_Interval O eC 63 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 63 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 63 hC

lemma cert_eq_𝔭 : PB64.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 63 rfl rfl hel hC
