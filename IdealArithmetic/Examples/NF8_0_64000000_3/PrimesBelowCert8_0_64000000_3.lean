import IdealArithmetic.Examples.NF8_0_64000000_3.PrimesBelow8_0_64000000_3F0
import IdealArithmetic.Examples.NF8_0_64000000_3.PrimesBelow8_0_64000000_3F1

noncomputable section
abbrev eC := ![1, 19, 50]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 51 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB51I0
  exact PB51I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB51 : PrimesBelowBoundCertificate O 51 := by
  refine primesBelowBoundCertificate_of_Interval O eC 50 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 50 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 50 hC

lemma cert_eq_𝔭 : PB51.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 50 rfl rfl hel hC
