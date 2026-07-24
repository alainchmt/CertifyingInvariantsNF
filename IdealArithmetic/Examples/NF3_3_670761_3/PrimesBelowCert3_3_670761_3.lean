import IdealArithmetic.Examples.NF3_3_670761_3.PrimesBelow3_3_670761_3F0
import IdealArithmetic.Examples.NF3_3_670761_3.PrimesBelow3_3_670761_3F1
import IdealArithmetic.Examples.NF3_3_670761_3.PrimesBelow3_3_670761_3F2
import IdealArithmetic.Examples.NF3_3_670761_3.PrimesBelow3_3_670761_3F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 182]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 183 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB183I0
  exact PB183I1
  exact PB183I2
  exact PB183I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB183 : PrimesBelowBoundCertificate O 183 := by
  refine primesBelowBoundCertificate_of_Interval O eC 182 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 182 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 182 hC

lemma cert_eq_𝔭 : PB183.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 182 rfl rfl hel hC
