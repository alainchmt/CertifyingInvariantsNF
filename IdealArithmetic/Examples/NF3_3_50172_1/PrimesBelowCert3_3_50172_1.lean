import IdealArithmetic.Examples.NF3_3_50172_1.PrimesBelow3_3_50172_1F0
import IdealArithmetic.Examples.NF3_3_50172_1.PrimesBelow3_3_50172_1F1

noncomputable section
abbrev eC := ![1, 31, 49]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 50 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB50I0
  exact PB50I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB50 : PrimesBelowBoundCertificate O 50 := by
  refine primesBelowBoundCertificate_of_Interval O eC 49 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 49 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 49 hC

lemma cert_eq_𝔭 : PB50.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 49 rfl rfl hel hC
