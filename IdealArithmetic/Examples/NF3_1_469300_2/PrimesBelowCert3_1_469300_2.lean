import IdealArithmetic.Examples.NF3_1_469300_2.PrimesBelow3_1_469300_2F0
import IdealArithmetic.Examples.NF3_1_469300_2.PrimesBelow3_1_469300_2F1
import IdealArithmetic.Examples.NF3_1_469300_2.PrimesBelow3_1_469300_2F2
import IdealArithmetic.Examples.NF3_1_469300_2.PrimesBelow3_1_469300_2F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 194 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB194I0
  exact PB194I1
  exact PB194I2
  exact PB194I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB194 : PrimesBelowBoundCertificate O 194 := by
  refine primesBelowBoundCertificate_of_Interval O eC 193 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 193 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 193 hC

lemma cert_eq_𝔭 : PB194.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 193 rfl rfl hel hC
