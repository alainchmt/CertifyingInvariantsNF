import IdealArithmetic.Examples.NF3_1_614075_2.PrimesBelow3_1_614075_2F0
import IdealArithmetic.Examples.NF3_1_614075_2.PrimesBelow3_1_614075_2F1
import IdealArithmetic.Examples.NF3_1_614075_2.PrimesBelow3_1_614075_2F2
import IdealArithmetic.Examples.NF3_1_614075_2.PrimesBelow3_1_614075_2F3
import IdealArithmetic.Examples.NF3_1_614075_2.PrimesBelow3_1_614075_2F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 221]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 222 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB222I0
  exact PB222I1
  exact PB222I2
  exact PB222I3
  exact PB222I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB222 : PrimesBelowBoundCertificate O 222 := by
  refine primesBelowBoundCertificate_of_Interval O eC 221 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 221 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 221 hC

lemma cert_eq_𝔭 : PB222.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 221 rfl rfl hel hC
