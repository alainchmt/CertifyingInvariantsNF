import IdealArithmetic.Examples.NF3_1_688076_2.PrimesBelow3_1_688076_2F0
import IdealArithmetic.Examples.NF3_1_688076_2.PrimesBelow3_1_688076_2F1
import IdealArithmetic.Examples.NF3_1_688076_2.PrimesBelow3_1_688076_2F2
import IdealArithmetic.Examples.NF3_1_688076_2.PrimesBelow3_1_688076_2F3
import IdealArithmetic.Examples.NF3_1_688076_2.PrimesBelow3_1_688076_2F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 234]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 235 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB235I0
  exact PB235I1
  exact PB235I2
  exact PB235I3
  exact PB235I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB235 : PrimesBelowBoundCertificate O 235 := by
  refine primesBelowBoundCertificate_of_Interval O eC 234 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 234 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 234 hC

lemma cert_eq_𝔭 : PB235.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 234 rfl rfl hel hC
