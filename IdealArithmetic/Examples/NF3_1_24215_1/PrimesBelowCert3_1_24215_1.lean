import IdealArithmetic.Examples.NF3_1_24215_1.PrimesBelow3_1_24215_1F0
import IdealArithmetic.Examples.NF3_1_24215_1.PrimesBelow3_1_24215_1F1

noncomputable section
abbrev eC := ![1, 31, 44]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 45 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB45I0
  exact PB45I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB45 : PrimesBelowBoundCertificate O 45 := by
  refine primesBelowBoundCertificate_of_Interval O eC 44 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 44 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 44 hC

lemma cert_eq_𝔭 : PB45.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 44 rfl rfl hel hC
