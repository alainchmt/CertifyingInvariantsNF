import IdealArithmetic.Examples.NF5_5_390625_1.PrimesBelow5_5_390625_1F0

noncomputable section
abbrev eC := ![1, 24]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 25 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB25I0

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB25 : PrimesBelowBoundCertificate O 25 := by
  refine primesBelowBoundCertificate_of_Interval O eC 24 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 24 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 24 hC

lemma cert_eq_𝔭 : PB25.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 24 rfl rfl hel hC
