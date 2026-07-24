import IdealArithmetic.Examples.NF5_1_15000000_1.PrimesBelow5_1_15000000_1F0
import IdealArithmetic.Examples.NF5_1_15000000_1.PrimesBelow5_1_15000000_1F1
import IdealArithmetic.Examples.NF5_1_15000000_1.PrimesBelow5_1_15000000_1F2
import IdealArithmetic.Examples.NF5_1_15000000_1.PrimesBelow5_1_15000000_1F3
import IdealArithmetic.Examples.NF5_1_15000000_1.PrimesBelow5_1_15000000_1F4
import IdealArithmetic.Examples.NF5_1_15000000_1.PrimesBelow5_1_15000000_1F5

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 241]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 242 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB242I0
  exact PB242I1
  exact PB242I2
  exact PB242I3
  exact PB242I4
  exact PB242I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB242 : PrimesBelowBoundCertificate O 242 := by
  refine primesBelowBoundCertificate_of_Interval O eC 241 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 241 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 241 hC

lemma cert_eq_𝔭 : PB242.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 241 rfl rfl hel hC
