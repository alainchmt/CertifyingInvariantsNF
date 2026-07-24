import IdealArithmetic.Examples.NF3_1_392196_1.PrimesBelow3_1_392196_1F0
import IdealArithmetic.Examples.NF3_1_392196_1.PrimesBelow3_1_392196_1F1
import IdealArithmetic.Examples.NF3_1_392196_1.PrimesBelow3_1_392196_1F2
import IdealArithmetic.Examples.NF3_1_392196_1.PrimesBelow3_1_392196_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 177]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 178 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB178I0
  exact PB178I1
  exact PB178I2
  exact PB178I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB178 : PrimesBelowBoundCertificate O 178 := by
  refine primesBelowBoundCertificate_of_Interval O eC 177 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 177 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 177 hC

lemma cert_eq_𝔭 : PB178.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 177 rfl rfl hel hC
