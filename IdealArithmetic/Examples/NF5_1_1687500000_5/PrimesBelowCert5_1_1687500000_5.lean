import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F0
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F1
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F2
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F3
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F4
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F5
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F6
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F7
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F8
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F9
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F10
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F11
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F12
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F13
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F14
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F15
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F16
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F17
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F18
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F19
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F20
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F21
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F22
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F23
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F24
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F25
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F26
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F27
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F28
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F29
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F30
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F31
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F32
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F33
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F34
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F35
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F36
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F37
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F38
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F39
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F40
import IdealArithmetic.Examples.NF5_1_1687500000_5.PrimesBelow5_1_1687500000_5F41

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1321, 1427, 1481, 1543, 1601, 1663, 1733, 1801, 1877, 1951, 2017, 2087, 2143, 2239, 2297, 2371, 2423, 2521, 2557]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 2558 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB2558I0
  exact PB2558I1
  exact PB2558I2
  exact PB2558I3
  exact PB2558I4
  exact PB2558I5
  exact PB2558I6
  exact PB2558I7
  exact PB2558I8
  exact PB2558I9
  exact PB2558I10
  exact PB2558I11
  exact PB2558I12
  exact PB2558I13
  exact PB2558I14
  exact PB2558I15
  exact PB2558I16
  exact PB2558I17
  exact PB2558I18
  exact PB2558I19
  exact PB2558I20
  exact PB2558I21
  exact PB2558I22
  exact PB2558I23
  exact PB2558I24
  exact PB2558I25
  exact PB2558I26
  exact PB2558I27
  exact PB2558I28
  exact PB2558I29
  exact PB2558I30
  exact PB2558I31
  exact PB2558I32
  exact PB2558I33
  exact PB2558I34
  exact PB2558I35
  exact PB2558I36
  exact PB2558I37
  exact PB2558I38
  exact PB2558I39
  exact PB2558I40
  exact PB2558I41

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB2558 : PrimesBelowBoundCertificate O 2558 := by
  refine primesBelowBoundCertificate_of_Interval O eC 2557 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 2557 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 2557 hC

lemma cert_eq_𝔭 : PB2558.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 2557 rfl rfl hel hC
