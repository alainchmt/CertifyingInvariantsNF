import IdealArithmetic.Examples.NF3_1_334235_1.PrimesBelow3_1_334235_1F0
import IdealArithmetic.Examples.NF3_1_334235_1.PrimesBelow3_1_334235_1F1
import IdealArithmetic.Examples.NF3_1_334235_1.PrimesBelow3_1_334235_1F2
import IdealArithmetic.Examples.NF3_1_334235_1.PrimesBelow3_1_334235_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 163]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 164 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB164I0
  exact PB164I1
  exact PB164I2
  exact PB164I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB164 : PrimesBelowBoundCertificate O 164 := by
  refine primesBelowBoundCertificate_of_Interval O eC 163 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 163 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 163 hC

lemma cert_eq_𝔭 : PB164.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 163 rfl rfl hel hC
