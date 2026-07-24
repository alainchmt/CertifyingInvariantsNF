import IdealArithmetic.Examples.NF3_1_649415_1.PrimesBelow3_1_649415_1F0
import IdealArithmetic.Examples.NF3_1_649415_1.PrimesBelow3_1_649415_1F1
import IdealArithmetic.Examples.NF3_1_649415_1.PrimesBelow3_1_649415_1F2
import IdealArithmetic.Examples.NF3_1_649415_1.PrimesBelow3_1_649415_1F3
import IdealArithmetic.Examples.NF3_1_649415_1.PrimesBelow3_1_649415_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 228]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 229 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB229I0
  exact PB229I1
  exact PB229I2
  exact PB229I3
  exact PB229I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB229 : PrimesBelowBoundCertificate O 229 := by
  refine primesBelowBoundCertificate_of_Interval O eC 228 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 228 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 228 hC

lemma cert_eq_𝔭 : PB229.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 228 rfl rfl hel hC
