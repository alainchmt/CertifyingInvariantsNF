import IdealArithmetic.Examples.NF8_0_12960000_2.PrimesBelow8_0_12960000_2F0

noncomputable section
abbrev eC := ![1, 22]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 23 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB23I0

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB23 : PrimesBelowBoundCertificate O 23 := by
  refine primesBelowBoundCertificate_of_Interval O eC 22 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 22 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 22 hC

lemma cert_eq_𝔭 : PB23.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 22 rfl rfl hel hC
