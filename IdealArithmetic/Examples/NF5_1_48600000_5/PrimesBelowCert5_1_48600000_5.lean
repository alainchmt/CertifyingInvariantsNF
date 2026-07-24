import IdealArithmetic.Examples.NF5_1_48600000_5.PrimesBelow5_1_48600000_5F0
import IdealArithmetic.Examples.NF5_1_48600000_5.PrimesBelow5_1_48600000_5F1
import IdealArithmetic.Examples.NF5_1_48600000_5.PrimesBelow5_1_48600000_5F2
import IdealArithmetic.Examples.NF5_1_48600000_5.PrimesBelow5_1_48600000_5F3
import IdealArithmetic.Examples.NF5_1_48600000_5.PrimesBelow5_1_48600000_5F4
import IdealArithmetic.Examples.NF5_1_48600000_5.PrimesBelow5_1_48600000_5F5
import IdealArithmetic.Examples.NF5_1_48600000_5.PrimesBelow5_1_48600000_5F6
import IdealArithmetic.Examples.NF5_1_48600000_5.PrimesBelow5_1_48600000_5F7
import IdealArithmetic.Examples.NF5_1_48600000_5.PrimesBelow5_1_48600000_5F8
import IdealArithmetic.Examples.NF5_1_48600000_5.PrimesBelow5_1_48600000_5F9

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 433]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 434 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB434I0
  exact PB434I1
  exact PB434I2
  exact PB434I3
  exact PB434I4
  exact PB434I5
  exact PB434I6
  exact PB434I7
  exact PB434I8
  exact PB434I9

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB434 : PrimesBelowBoundCertificate O 434 := by
  refine primesBelowBoundCertificate_of_Interval O eC 433 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 433 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 433 hC

lemma cert_eq_𝔭 : PB434.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 433 rfl rfl hel hC
