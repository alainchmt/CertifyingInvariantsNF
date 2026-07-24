import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F0
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F1
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F2
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F3
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F4
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F5
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F6
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F7
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F8
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F9
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F10
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F11
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F12
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F13
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F14
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F15
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F16
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F17
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F18
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F19
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F20
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F21
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F22
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F23
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F24
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F25
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F26
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F27
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F28
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F29
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F30
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F31
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F32
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F33
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F34
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F35
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F36
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F37
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F38
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F39
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F40
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F41
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F42
import IdealArithmetic.Examples.NF5_3_3037500000_1.PrimesBelow5_3_3037500000_1F43

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1321, 1427, 1481, 1543, 1601, 1663, 1733, 1801, 1877, 1951, 2017, 2087, 2143, 2239, 2297, 2371, 2423, 2521, 2593, 2671, 2694]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 2695 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB2695I0
  exact PB2695I1
  exact PB2695I2
  exact PB2695I3
  exact PB2695I4
  exact PB2695I5
  exact PB2695I6
  exact PB2695I7
  exact PB2695I8
  exact PB2695I9
  exact PB2695I10
  exact PB2695I11
  exact PB2695I12
  exact PB2695I13
  exact PB2695I14
  exact PB2695I15
  exact PB2695I16
  exact PB2695I17
  exact PB2695I18
  exact PB2695I19
  exact PB2695I20
  exact PB2695I21
  exact PB2695I22
  exact PB2695I23
  exact PB2695I24
  exact PB2695I25
  exact PB2695I26
  exact PB2695I27
  exact PB2695I28
  exact PB2695I29
  exact PB2695I30
  exact PB2695I31
  exact PB2695I32
  exact PB2695I33
  exact PB2695I34
  exact PB2695I35
  exact PB2695I36
  exact PB2695I37
  exact PB2695I38
  exact PB2695I39
  exact PB2695I40
  exact PB2695I41
  exact PB2695I42
  exact PB2695I43

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB2695 : PrimesBelowBoundCertificate O 2695 := by
  refine primesBelowBoundCertificate_of_Interval O eC 2694 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 2694 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 2694 hC

lemma cert_eq_𝔭 : PB2695.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 2694 rfl rfl hel hC
