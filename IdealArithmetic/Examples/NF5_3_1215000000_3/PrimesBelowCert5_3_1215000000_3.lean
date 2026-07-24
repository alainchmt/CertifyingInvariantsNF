import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F0
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F1
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F2
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F3
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F4
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F5
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F6
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F7
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F8
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F9
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F10
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F11
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F12
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F13
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F14
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F15
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F16
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F17
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F18
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F19
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F20
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F21
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F22
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F23
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F24
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F25
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F26
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F27
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F28
import IdealArithmetic.Examples.NF5_3_1215000000_3.PrimesBelow5_3_1215000000_3F29

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1279, 1321, 1427, 1481, 1543, 1601, 1663, 1704]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 1705 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB1705I0
  exact PB1705I1
  exact PB1705I2
  exact PB1705I3
  exact PB1705I4
  exact PB1705I5
  exact PB1705I6
  exact PB1705I7
  exact PB1705I8
  exact PB1705I9
  exact PB1705I10
  exact PB1705I11
  exact PB1705I12
  exact PB1705I13
  exact PB1705I14
  exact PB1705I15
  exact PB1705I16
  exact PB1705I17
  exact PB1705I18
  exact PB1705I19
  exact PB1705I20
  exact PB1705I21
  exact PB1705I22
  exact PB1705I23
  exact PB1705I24
  exact PB1705I25
  exact PB1705I26
  exact PB1705I27
  exact PB1705I28
  exact PB1705I29

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB1705 : PrimesBelowBoundCertificate O 1705 := by
  refine primesBelowBoundCertificate_of_Interval O eC 1704 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 1704 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 1704 hC

lemma cert_eq_𝔭 : PB1705.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 1704 rfl rfl hel hC
