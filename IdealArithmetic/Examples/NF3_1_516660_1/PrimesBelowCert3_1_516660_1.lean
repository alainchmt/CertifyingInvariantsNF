import IdealArithmetic.Examples.NF3_1_516660_1.PrimesBelow3_1_516660_1F0
import IdealArithmetic.Examples.NF3_1_516660_1.PrimesBelow3_1_516660_1F1
import IdealArithmetic.Examples.NF3_1_516660_1.PrimesBelow3_1_516660_1F2
import IdealArithmetic.Examples.NF3_1_516660_1.PrimesBelow3_1_516660_1F3
import IdealArithmetic.Examples.NF3_1_516660_1.PrimesBelow3_1_516660_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 203]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 204 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB204I0
  exact PB204I1
  exact PB204I2
  exact PB204I3
  exact PB204I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB204 : PrimesBelowBoundCertificate O 204 := by
  refine primesBelowBoundCertificate_of_Interval O eC 203 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 203 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 203 hC

lemma cert_eq_𝔭 : PB204.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 203 rfl rfl hel hC
