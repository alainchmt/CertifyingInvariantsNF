import IdealArithmetic.Examples.NF3_1_662796_4.PrimesBelow3_1_662796_4F0
import IdealArithmetic.Examples.NF3_1_662796_4.PrimesBelow3_1_662796_4F1
import IdealArithmetic.Examples.NF3_1_662796_4.PrimesBelow3_1_662796_4F2
import IdealArithmetic.Examples.NF3_1_662796_4.PrimesBelow3_1_662796_4F3
import IdealArithmetic.Examples.NF3_1_662796_4.PrimesBelow3_1_662796_4F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 230]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 231 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB231I0
  exact PB231I1
  exact PB231I2
  exact PB231I3
  exact PB231I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB231 : PrimesBelowBoundCertificate O 231 := by
  refine primesBelowBoundCertificate_of_Interval O eC 230 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 230 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 230 hC

lemma cert_eq_𝔭 : PB231.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 230 rfl rfl hel hC
