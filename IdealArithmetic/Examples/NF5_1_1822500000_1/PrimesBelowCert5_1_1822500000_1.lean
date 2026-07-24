import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F0
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F1
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F2
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F3
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F4
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F5
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F6
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F7
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F8
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F9
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F10
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F11
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F12
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F13
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F14
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F15
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F16
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F17
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F18
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F19
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F20
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F21
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F22
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F23
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F24
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F25
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F26
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F27
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F28
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F29
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F30
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F31
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F32
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F33
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F34
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F35
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F36
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F37
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F38
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F39
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F40
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F41
import IdealArithmetic.Examples.NF5_1_1822500000_1.PrimesBelow5_1_1822500000_1F42

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1321, 1427, 1481, 1543, 1601, 1663, 1733, 1801, 1877, 1951, 2017, 2087, 2143, 2239, 2297, 2371, 2423, 2521, 2593, 2657]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 2658 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB2658I0
  exact PB2658I1
  exact PB2658I2
  exact PB2658I3
  exact PB2658I4
  exact PB2658I5
  exact PB2658I6
  exact PB2658I7
  exact PB2658I8
  exact PB2658I9
  exact PB2658I10
  exact PB2658I11
  exact PB2658I12
  exact PB2658I13
  exact PB2658I14
  exact PB2658I15
  exact PB2658I16
  exact PB2658I17
  exact PB2658I18
  exact PB2658I19
  exact PB2658I20
  exact PB2658I21
  exact PB2658I22
  exact PB2658I23
  exact PB2658I24
  exact PB2658I25
  exact PB2658I26
  exact PB2658I27
  exact PB2658I28
  exact PB2658I29
  exact PB2658I30
  exact PB2658I31
  exact PB2658I32
  exact PB2658I33
  exact PB2658I34
  exact PB2658I35
  exact PB2658I36
  exact PB2658I37
  exact PB2658I38
  exact PB2658I39
  exact PB2658I40
  exact PB2658I41
  exact PB2658I42

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB2658 : PrimesBelowBoundCertificate O 2658 := by
  refine primesBelowBoundCertificate_of_Interval O eC 2657 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 2657 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 2657 hC

lemma cert_eq_𝔭 : PB2658.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 2657 rfl rfl hel hC
