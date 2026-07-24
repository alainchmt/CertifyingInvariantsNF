import IdealArithmetic.Examples.NF3_1_64823_1.PrimesBelow3_1_64823_1F0
import IdealArithmetic.Examples.NF3_1_64823_1.PrimesBelow3_1_64823_1F1

noncomputable section
abbrev eC := ![1, 31, 72]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 73 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB73I0
  exact PB73I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB73 : PrimesBelowBoundCertificate O 73 := by
  refine primesBelowBoundCertificate_of_Interval O eC 72 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 72 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 72 hC

lemma cert_eq_𝔭 : PB73.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 72 rfl rfl hel hC
