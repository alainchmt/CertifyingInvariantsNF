import IdealArithmetic.Examples.NF3_1_117288_3.PrimesBelow3_1_117288_3F0
import IdealArithmetic.Examples.NF3_1_117288_3.PrimesBelow3_1_117288_3F1
import IdealArithmetic.Examples.NF3_1_117288_3.PrimesBelow3_1_117288_3F2

noncomputable section
abbrev eC := ![1, 31, 79, 96]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 97 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB97I0
  exact PB97I1
  exact PB97I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB97 : PrimesBelowBoundCertificate O 97 := by
  refine primesBelowBoundCertificate_of_Interval O eC 96 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 96 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 96 hC

lemma cert_eq_𝔭 : PB97.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 96 rfl rfl hel hC
