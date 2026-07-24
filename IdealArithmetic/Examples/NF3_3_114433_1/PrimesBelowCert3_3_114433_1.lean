import IdealArithmetic.Examples.NF3_3_114433_1.PrimesBelow3_3_114433_1F0
import IdealArithmetic.Examples.NF3_3_114433_1.PrimesBelow3_3_114433_1F1

noncomputable section
abbrev eC := ![1, 31, 75]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 76 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB76I0
  exact PB76I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB76 : PrimesBelowBoundCertificate O 76 := by
  refine primesBelowBoundCertificate_of_Interval O eC 75 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 75 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 75 hC

lemma cert_eq_𝔭 : PB76.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 75 rfl rfl hel hC
