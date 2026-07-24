import IdealArithmetic.Examples.NF5_3_40500000_1.PrimesBelow5_3_40500000_1F0
import IdealArithmetic.Examples.NF5_3_40500000_1.PrimesBelow5_3_40500000_1F1
import IdealArithmetic.Examples.NF5_3_40500000_1.PrimesBelow5_3_40500000_1F2
import IdealArithmetic.Examples.NF5_3_40500000_1.PrimesBelow5_3_40500000_1F3
import IdealArithmetic.Examples.NF5_3_40500000_1.PrimesBelow5_3_40500000_1F4
import IdealArithmetic.Examples.NF5_3_40500000_1.PrimesBelow5_3_40500000_1F5
import IdealArithmetic.Examples.NF5_3_40500000_1.PrimesBelow5_3_40500000_1F6
import IdealArithmetic.Examples.NF5_3_40500000_1.PrimesBelow5_3_40500000_1F7

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 311]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 312 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB312I0
  exact PB312I1
  exact PB312I2
  exact PB312I3
  exact PB312I4
  exact PB312I5
  exact PB312I6
  exact PB312I7

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB312 : PrimesBelowBoundCertificate O 312 := by
  refine primesBelowBoundCertificate_of_Interval O eC 311 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 311 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 311 hC

lemma cert_eq_𝔭 : PB312.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 311 rfl rfl hel hC
