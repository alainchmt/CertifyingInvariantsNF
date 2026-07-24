import IdealArithmetic.Examples.NF3_1_491724_2.PrimesBelow3_1_491724_2F0
import IdealArithmetic.Examples.NF3_1_491724_2.PrimesBelow3_1_491724_2F1
import IdealArithmetic.Examples.NF3_1_491724_2.PrimesBelow3_1_491724_2F2
import IdealArithmetic.Examples.NF3_1_491724_2.PrimesBelow3_1_491724_2F3
import IdealArithmetic.Examples.NF3_1_491724_2.PrimesBelow3_1_491724_2F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 198]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 199 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB199I0
  exact PB199I1
  exact PB199I2
  exact PB199I3
  exact PB199I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB199 : PrimesBelowBoundCertificate O 199 := by
  refine primesBelowBoundCertificate_of_Interval O eC 198 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 198 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 198 hC

lemma cert_eq_𝔭 : PB199.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 198 rfl rfl hel hC
