import IdealArithmetic.Examples.NF3_1_439803_1.PrimesBelow3_1_439803_1F0
import IdealArithmetic.Examples.NF3_1_439803_1.PrimesBelow3_1_439803_1F1
import IdealArithmetic.Examples.NF3_1_439803_1.PrimesBelow3_1_439803_1F2
import IdealArithmetic.Examples.NF3_1_439803_1.PrimesBelow3_1_439803_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 187]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 188 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB188I0
  exact PB188I1
  exact PB188I2
  exact PB188I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB188 : PrimesBelowBoundCertificate O 188 := by
  refine primesBelowBoundCertificate_of_Interval O eC 187 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 187 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 187 hC

lemma cert_eq_𝔭 : PB188.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 187 rfl rfl hel hC
