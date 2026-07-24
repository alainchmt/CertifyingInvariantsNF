import IdealArithmetic.Examples.NF3_1_797203_1.PrimesBelow3_1_797203_1F0
import IdealArithmetic.Examples.NF3_1_797203_1.PrimesBelow3_1_797203_1F1
import IdealArithmetic.Examples.NF3_1_797203_1.PrimesBelow3_1_797203_1F2
import IdealArithmetic.Examples.NF3_1_797203_1.PrimesBelow3_1_797203_1F3
import IdealArithmetic.Examples.NF3_1_797203_1.PrimesBelow3_1_797203_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 252]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 253 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB253I0
  exact PB253I1
  exact PB253I2
  exact PB253I3
  exact PB253I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB253 : PrimesBelowBoundCertificate O 253 := by
  refine primesBelowBoundCertificate_of_Interval O eC 252 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 252 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 252 hC

lemma cert_eq_𝔭 : PB253.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 252 rfl rfl hel hC
