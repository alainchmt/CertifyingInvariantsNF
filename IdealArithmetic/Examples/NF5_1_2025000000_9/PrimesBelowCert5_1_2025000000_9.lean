import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F0
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F1
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F2
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F3
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F4
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F5
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F6
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F7
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F8
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F9
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F10
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F11
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F12
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F13
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F14
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F15
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F16
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F17
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F18
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F19
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F20
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F21
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F22
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F23
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F24
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F25
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F26
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F27
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F28
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F29
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F30
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F31
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F32
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F33
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F34
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F35
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F36
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F37
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F38
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F39
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F40
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F41
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F42
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F43
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F44
import IdealArithmetic.Examples.NF5_1_2025000000_9.PrimesBelow5_1_2025000000_9F45

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1321, 1427, 1481, 1543, 1601, 1663, 1733, 1801, 1877, 1951, 2017, 2087, 2143, 2239, 2297, 2371, 2423, 2521, 2593, 2671, 2713, 2789, 2801]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 2802 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB2802I0
  exact PB2802I1
  exact PB2802I2
  exact PB2802I3
  exact PB2802I4
  exact PB2802I5
  exact PB2802I6
  exact PB2802I7
  exact PB2802I8
  exact PB2802I9
  exact PB2802I10
  exact PB2802I11
  exact PB2802I12
  exact PB2802I13
  exact PB2802I14
  exact PB2802I15
  exact PB2802I16
  exact PB2802I17
  exact PB2802I18
  exact PB2802I19
  exact PB2802I20
  exact PB2802I21
  exact PB2802I22
  exact PB2802I23
  exact PB2802I24
  exact PB2802I25
  exact PB2802I26
  exact PB2802I27
  exact PB2802I28
  exact PB2802I29
  exact PB2802I30
  exact PB2802I31
  exact PB2802I32
  exact PB2802I33
  exact PB2802I34
  exact PB2802I35
  exact PB2802I36
  exact PB2802I37
  exact PB2802I38
  exact PB2802I39
  exact PB2802I40
  exact PB2802I41
  exact PB2802I42
  exact PB2802I43
  exact PB2802I44
  exact PB2802I45

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB2802 : PrimesBelowBoundCertificate O 2802 := by
  refine primesBelowBoundCertificate_of_Interval O eC 2801 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 2801 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 2801 hC

lemma cert_eq_𝔭 : PB2802.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 2801 rfl rfl hel hC
