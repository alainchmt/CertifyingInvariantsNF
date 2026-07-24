import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F0
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F1
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F2
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F3
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F4
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F5
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F6
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F7
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F8
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F9
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F10
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F11
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F12
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F13
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F14
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F15
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F16
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F17
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F18
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F19
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F20
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F21
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F22
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F23
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F24
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F25
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F26
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F27
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F28
import IdealArithmetic.Examples.NF5_1_729000000_2.PrimesBelow5_1_729000000_2F29

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1321, 1427, 1481, 1543, 1601, 1663, 1680]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 1681 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB1681I0
  exact PB1681I1
  exact PB1681I2
  exact PB1681I3
  exact PB1681I4
  exact PB1681I5
  exact PB1681I6
  exact PB1681I7
  exact PB1681I8
  exact PB1681I9
  exact PB1681I10
  exact PB1681I11
  exact PB1681I12
  exact PB1681I13
  exact PB1681I14
  exact PB1681I15
  exact PB1681I16
  exact PB1681I17
  exact PB1681I18
  exact PB1681I19
  exact PB1681I20
  exact PB1681I21
  exact PB1681I22
  exact PB1681I23
  exact PB1681I24
  exact PB1681I25
  exact PB1681I26
  exact PB1681I27
  exact PB1681I28
  exact PB1681I29

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB1681 : PrimesBelowBoundCertificate O 1681 := by
  refine primesBelowBoundCertificate_of_Interval O eC 1680 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 1680 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 1680 hC

lemma cert_eq_𝔭 : PB1681.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 1680 rfl rfl hel hC
