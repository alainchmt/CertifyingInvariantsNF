import IdealArithmetic.Examples.NF2_0_231_1.PrimesBelow2_0_231_1F0

noncomputable section
abbrev eC := ![1, 9]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 10 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB10I0

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB10 : PrimesBelowBoundCertificate O 10 := by
  refine primesBelowBoundCertificate_of_Interval O eC 9 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 9 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 9 hC

lemma cert_eq_𝔭 : PB10.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 9 rfl rfl hel hC
