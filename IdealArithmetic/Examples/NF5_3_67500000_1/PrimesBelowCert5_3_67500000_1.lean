import IdealArithmetic.Examples.NF5_3_67500000_1.PrimesBelow5_3_67500000_1F0
import IdealArithmetic.Examples.NF5_3_67500000_1.PrimesBelow5_3_67500000_1F1
import IdealArithmetic.Examples.NF5_3_67500000_1.PrimesBelow5_3_67500000_1F2
import IdealArithmetic.Examples.NF5_3_67500000_1.PrimesBelow5_3_67500000_1F3
import IdealArithmetic.Examples.NF5_3_67500000_1.PrimesBelow5_3_67500000_1F4
import IdealArithmetic.Examples.NF5_3_67500000_1.PrimesBelow5_3_67500000_1F5
import IdealArithmetic.Examples.NF5_3_67500000_1.PrimesBelow5_3_67500000_1F6
import IdealArithmetic.Examples.NF5_3_67500000_1.PrimesBelow5_3_67500000_1F7
import IdealArithmetic.Examples.NF5_3_67500000_1.PrimesBelow5_3_67500000_1F8

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 401]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 402 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB402I0
  exact PB402I1
  exact PB402I2
  exact PB402I3
  exact PB402I4
  exact PB402I5
  exact PB402I6
  exact PB402I7
  exact PB402I8

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB402 : PrimesBelowBoundCertificate O 402 := by
  refine primesBelowBoundCertificate_of_Interval O eC 401 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 401 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 401 hC

lemma cert_eq_𝔭 : PB402.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 401 rfl rfl hel hC
