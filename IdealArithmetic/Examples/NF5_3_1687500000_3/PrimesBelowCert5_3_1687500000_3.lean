import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F0
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F1
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F2
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F3
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F4
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F5
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F6
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F7
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F8
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F9
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F10
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F11
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F12
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F13
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F14
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F15
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F16
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F17
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F18
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F19
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F20
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F21
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F22
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F23
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F24
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F25
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F26
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F27
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F28
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F29
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F30
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F31
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F32
import IdealArithmetic.Examples.NF5_3_1687500000_3.PrimesBelow5_3_1687500000_3F33

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1321, 1427, 1481, 1543, 1601, 1663, 1733, 1801, 1877, 1951, 2008]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 2009 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB2009I0
  exact PB2009I1
  exact PB2009I2
  exact PB2009I3
  exact PB2009I4
  exact PB2009I5
  exact PB2009I6
  exact PB2009I7
  exact PB2009I8
  exact PB2009I9
  exact PB2009I10
  exact PB2009I11
  exact PB2009I12
  exact PB2009I13
  exact PB2009I14
  exact PB2009I15
  exact PB2009I16
  exact PB2009I17
  exact PB2009I18
  exact PB2009I19
  exact PB2009I20
  exact PB2009I21
  exact PB2009I22
  exact PB2009I23
  exact PB2009I24
  exact PB2009I25
  exact PB2009I26
  exact PB2009I27
  exact PB2009I28
  exact PB2009I29
  exact PB2009I30
  exact PB2009I31
  exact PB2009I32
  exact PB2009I33

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB2009 : PrimesBelowBoundCertificate O 2009 := by
  refine primesBelowBoundCertificate_of_Interval O eC 2008 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 2008 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 2008 hC

lemma cert_eq_𝔭 : PB2009.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 2008 rfl rfl hel hC
