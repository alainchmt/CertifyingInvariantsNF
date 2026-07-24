import IdealArithmetic.Examples.NF3_1_680504_1.PrimesBelow3_1_680504_1F0
import IdealArithmetic.Examples.NF3_1_680504_1.PrimesBelow3_1_680504_1F1
import IdealArithmetic.Examples.NF3_1_680504_1.PrimesBelow3_1_680504_1F2
import IdealArithmetic.Examples.NF3_1_680504_1.PrimesBelow3_1_680504_1F3
import IdealArithmetic.Examples.NF3_1_680504_1.PrimesBelow3_1_680504_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 233]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 234 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB234I0
  exact PB234I1
  exact PB234I2
  exact PB234I3
  exact PB234I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB234 : PrimesBelowBoundCertificate O 234 := by
  refine primesBelowBoundCertificate_of_Interval O eC 233 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 233 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 233 hC

lemma cert_eq_𝔭 : PB234.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 233 rfl rfl hel hC
