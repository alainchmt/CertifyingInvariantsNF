import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F0
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F1
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F2
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F3
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F4
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F5
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F6
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F7
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F8
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F9
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F10
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F11
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F12
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F13
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F14
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F15
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F16
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F17
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F18
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F19
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F20
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F21
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F22
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F23
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F24
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F25
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F26
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F27
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F28
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F29
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F30
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F31
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F32
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F33
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F34
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F35
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F36
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F37
import IdealArithmetic.Examples.NF5_1_1423828125_3.PrimesBelow5_1_1423828125_3F38

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1321, 1427, 1481, 1543, 1601, 1663, 1733, 1801, 1877, 1951, 2017, 2087, 2143, 2239, 2297, 2348]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 2349 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB2349I0
  exact PB2349I1
  exact PB2349I2
  exact PB2349I3
  exact PB2349I4
  exact PB2349I5
  exact PB2349I6
  exact PB2349I7
  exact PB2349I8
  exact PB2349I9
  exact PB2349I10
  exact PB2349I11
  exact PB2349I12
  exact PB2349I13
  exact PB2349I14
  exact PB2349I15
  exact PB2349I16
  exact PB2349I17
  exact PB2349I18
  exact PB2349I19
  exact PB2349I20
  exact PB2349I21
  exact PB2349I22
  exact PB2349I23
  exact PB2349I24
  exact PB2349I25
  exact PB2349I26
  exact PB2349I27
  exact PB2349I28
  exact PB2349I29
  exact PB2349I30
  exact PB2349I31
  exact PB2349I32
  exact PB2349I33
  exact PB2349I34
  exact PB2349I35
  exact PB2349I36
  exact PB2349I37
  exact PB2349I38

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB2349 : PrimesBelowBoundCertificate O 2349 := by
  refine primesBelowBoundCertificate_of_Interval O eC 2348 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 2348 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 2348 hC

lemma cert_eq_𝔭 : PB2349.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 2348 rfl rfl hel hC
