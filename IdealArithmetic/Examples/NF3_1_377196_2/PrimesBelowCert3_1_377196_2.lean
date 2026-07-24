import IdealArithmetic.Examples.NF3_1_377196_2.PrimesBelow3_1_377196_2F0
import IdealArithmetic.Examples.NF3_1_377196_2.PrimesBelow3_1_377196_2F1
import IdealArithmetic.Examples.NF3_1_377196_2.PrimesBelow3_1_377196_2F2
import IdealArithmetic.Examples.NF3_1_377196_2.PrimesBelow3_1_377196_2F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 173]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 174 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB174I0
  exact PB174I1
  exact PB174I2
  exact PB174I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB174 : PrimesBelowBoundCertificate O 174 := by
  refine primesBelowBoundCertificate_of_Interval O eC 173 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 173 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 173 hC

lemma cert_eq_𝔭 : PB174.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 173 rfl rfl hel hC
