import IdealArithmetic.Examples.NF3_3_874321_1.PrimesBelow3_3_874321_1F0
import IdealArithmetic.Examples.NF3_3_874321_1.PrimesBelow3_3_874321_1F1
import IdealArithmetic.Examples.NF3_3_874321_1.PrimesBelow3_3_874321_1F2
import IdealArithmetic.Examples.NF3_3_874321_1.PrimesBelow3_3_874321_1F3
import IdealArithmetic.Examples.NF3_3_874321_1.PrimesBelow3_3_874321_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 207]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 208 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB208I0
  exact PB208I1
  exact PB208I2
  exact PB208I3
  exact PB208I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB208 : PrimesBelowBoundCertificate O 208 := by
  refine primesBelowBoundCertificate_of_Interval O eC 207 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 207 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 207 hC

lemma cert_eq_𝔭 : PB208.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 207 rfl rfl hel hC
