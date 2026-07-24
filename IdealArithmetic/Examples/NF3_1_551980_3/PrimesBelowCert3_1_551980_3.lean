import IdealArithmetic.Examples.NF3_1_551980_3.PrimesBelow3_1_551980_3F0
import IdealArithmetic.Examples.NF3_1_551980_3.PrimesBelow3_1_551980_3F1
import IdealArithmetic.Examples.NF3_1_551980_3.PrimesBelow3_1_551980_3F2
import IdealArithmetic.Examples.NF3_1_551980_3.PrimesBelow3_1_551980_3F3
import IdealArithmetic.Examples.NF3_1_551980_3.PrimesBelow3_1_551980_3F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 210]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 211 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB211I0
  exact PB211I1
  exact PB211I2
  exact PB211I3
  exact PB211I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB211 : PrimesBelowBoundCertificate O 211 := by
  refine primesBelowBoundCertificate_of_Interval O eC 210 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 210 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 210 hC

lemma cert_eq_𝔭 : PB211.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 210 rfl rfl hel hC
