import IdealArithmetic.Examples.NF3_1_504175_1.PrimesBelow3_1_504175_1F0
import IdealArithmetic.Examples.NF3_1_504175_1.PrimesBelow3_1_504175_1F1
import IdealArithmetic.Examples.NF3_1_504175_1.PrimesBelow3_1_504175_1F2
import IdealArithmetic.Examples.NF3_1_504175_1.PrimesBelow3_1_504175_1F3
import IdealArithmetic.Examples.NF3_1_504175_1.PrimesBelow3_1_504175_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 200]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 201 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB201I0
  exact PB201I1
  exact PB201I2
  exact PB201I3
  exact PB201I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB201 : PrimesBelowBoundCertificate O 201 := by
  refine primesBelowBoundCertificate_of_Interval O eC 200 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 200 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 200 hC

lemma cert_eq_𝔭 : PB201.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 200 rfl rfl hel hC
