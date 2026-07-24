import IdealArithmetic.Examples.NF3_1_314847_3.PrimesBelow3_1_314847_3F0
import IdealArithmetic.Examples.NF3_1_314847_3.PrimesBelow3_1_314847_3F1
import IdealArithmetic.Examples.NF3_1_314847_3.PrimesBelow3_1_314847_3F2
import IdealArithmetic.Examples.NF3_1_314847_3.PrimesBelow3_1_314847_3F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 158]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 159 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB159I0
  exact PB159I1
  exact PB159I2
  exact PB159I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB159 : PrimesBelowBoundCertificate O 159 := by
  refine primesBelowBoundCertificate_of_Interval O eC 158 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 158 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 158 hC

lemma cert_eq_𝔭 : PB159.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 158 rfl rfl hel hC
