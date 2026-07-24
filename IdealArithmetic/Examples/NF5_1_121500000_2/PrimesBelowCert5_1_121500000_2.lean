import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F0
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F1
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F2
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F3
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F4
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F5
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F6
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F7
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F8
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F9
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F10
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F11
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F12
import IdealArithmetic.Examples.NF5_1_121500000_2.PrimesBelow5_1_121500000_2F13

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 686]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 687 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB687I0
  exact PB687I1
  exact PB687I2
  exact PB687I3
  exact PB687I4
  exact PB687I5
  exact PB687I6
  exact PB687I7
  exact PB687I8
  exact PB687I9
  exact PB687I10
  exact PB687I11
  exact PB687I12
  exact PB687I13

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB687 : PrimesBelowBoundCertificate O 687 := by
  refine primesBelowBoundCertificate_of_Interval O eC 686 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 686 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 686 hC

lemma cert_eq_𝔭 : PB687.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 686 rfl rfl hel hC
