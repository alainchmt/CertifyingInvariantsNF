import IdealArithmetic.Examples.NF3_1_603288_2.PrimesBelow3_1_603288_2F0
import IdealArithmetic.Examples.NF3_1_603288_2.PrimesBelow3_1_603288_2F1
import IdealArithmetic.Examples.NF3_1_603288_2.PrimesBelow3_1_603288_2F2
import IdealArithmetic.Examples.NF3_1_603288_2.PrimesBelow3_1_603288_2F3
import IdealArithmetic.Examples.NF3_1_603288_2.PrimesBelow3_1_603288_2F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 219]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 220 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB220I0
  exact PB220I1
  exact PB220I2
  exact PB220I3
  exact PB220I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB220 : PrimesBelowBoundCertificate O 220 := by
  refine primesBelowBoundCertificate_of_Interval O eC 219 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 219 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 219 hC

lemma cert_eq_𝔭 : PB220.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 219 rfl rfl hel hC
