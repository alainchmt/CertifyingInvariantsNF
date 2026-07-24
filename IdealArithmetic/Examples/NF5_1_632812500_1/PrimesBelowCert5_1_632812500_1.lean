import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F0
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F1
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F2
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F3
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F4
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F5
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F6
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F7
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F8
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F9
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F10
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F11
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F12
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F13
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F14
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F15
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F16
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F17
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F18
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F19
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F20
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F21
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F22
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F23
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F24
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F25
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F26
import IdealArithmetic.Examples.NF5_1_632812500_1.PrimesBelow5_1_632812500_1F27

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1321, 1427, 1481, 1543, 1566]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 1567 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB1567I0
  exact PB1567I1
  exact PB1567I2
  exact PB1567I3
  exact PB1567I4
  exact PB1567I5
  exact PB1567I6
  exact PB1567I7
  exact PB1567I8
  exact PB1567I9
  exact PB1567I10
  exact PB1567I11
  exact PB1567I12
  exact PB1567I13
  exact PB1567I14
  exact PB1567I15
  exact PB1567I16
  exact PB1567I17
  exact PB1567I18
  exact PB1567I19
  exact PB1567I20
  exact PB1567I21
  exact PB1567I22
  exact PB1567I23
  exact PB1567I24
  exact PB1567I25
  exact PB1567I26
  exact PB1567I27

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB1567 : PrimesBelowBoundCertificate O 1567 := by
  refine primesBelowBoundCertificate_of_Interval O eC 1566 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 1566 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 1566 hC

lemma cert_eq_𝔭 : PB1567.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 1566 rfl rfl hel hC
