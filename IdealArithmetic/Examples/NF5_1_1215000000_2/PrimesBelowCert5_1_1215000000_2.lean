import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F0
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F1
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F2
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F3
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F4
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F5
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F6
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F7
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F8
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F9
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F10
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F11
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F12
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F13
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F14
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F15
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F16
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F17
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F18
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F19
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F20
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F21
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F22
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F23
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F24
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F25
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F26
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F27
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F28
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F29
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F30
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F31
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F32
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F33
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F34
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F35
import IdealArithmetic.Examples.NF5_1_1215000000_2.PrimesBelow5_1_1215000000_2F36

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1321, 1427, 1481, 1543, 1601, 1663, 1733, 1801, 1877, 1951, 2017, 2087, 2143, 2169]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 2170 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB2170I0
  exact PB2170I1
  exact PB2170I2
  exact PB2170I3
  exact PB2170I4
  exact PB2170I5
  exact PB2170I6
  exact PB2170I7
  exact PB2170I8
  exact PB2170I9
  exact PB2170I10
  exact PB2170I11
  exact PB2170I12
  exact PB2170I13
  exact PB2170I14
  exact PB2170I15
  exact PB2170I16
  exact PB2170I17
  exact PB2170I18
  exact PB2170I19
  exact PB2170I20
  exact PB2170I21
  exact PB2170I22
  exact PB2170I23
  exact PB2170I24
  exact PB2170I25
  exact PB2170I26
  exact PB2170I27
  exact PB2170I28
  exact PB2170I29
  exact PB2170I30
  exact PB2170I31
  exact PB2170I32
  exact PB2170I33
  exact PB2170I34
  exact PB2170I35
  exact PB2170I36

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB2170 : PrimesBelowBoundCertificate O 2170 := by
  refine primesBelowBoundCertificate_of_Interval O eC 2169 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 2169 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 2169 hC

lemma cert_eq_𝔭 : PB2170.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 2169 rfl rfl hel hC
