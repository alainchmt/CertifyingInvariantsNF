import IdealArithmetic.Examples.NF5_1_1000000_1.PrimesBelow5_1_1000000_1F0
import IdealArithmetic.Examples.NF5_1_1000000_1.PrimesBelow5_1_1000000_1F1

noncomputable section
abbrev eC := ![1, 23, 62]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 63 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB63I0
  exact PB63I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB63 : PrimesBelowBoundCertificate O 63 := by
  refine primesBelowBoundCertificate_of_Interval O eC 62 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 62 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 62 hC

lemma cert_eq_𝔭 : PB63.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 62 rfl rfl hel hC
