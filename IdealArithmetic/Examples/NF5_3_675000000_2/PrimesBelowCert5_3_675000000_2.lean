import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F0
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F1
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F2
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F3
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F4
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F5
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F6
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F7
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F8
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F9
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F10
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F11
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F12
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F13
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F14
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F15
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F16
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F17
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F18
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F19
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F20
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F21
import IdealArithmetic.Examples.NF5_3_675000000_2.PrimesBelow5_3_675000000_2F22

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 953, 1019, 1069, 1129, 1213, 1270]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 1271 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB1271I0
  exact PB1271I1
  exact PB1271I2
  exact PB1271I3
  exact PB1271I4
  exact PB1271I5
  exact PB1271I6
  exact PB1271I7
  exact PB1271I8
  exact PB1271I9
  exact PB1271I10
  exact PB1271I11
  exact PB1271I12
  exact PB1271I13
  exact PB1271I14
  exact PB1271I15
  exact PB1271I16
  exact PB1271I17
  exact PB1271I18
  exact PB1271I19
  exact PB1271I20
  exact PB1271I21
  exact PB1271I22

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB1271 : PrimesBelowBoundCertificate O 1271 := by
  refine primesBelowBoundCertificate_of_Interval O eC 1270 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 1270 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 1270 hC

lemma cert_eq_𝔭 : PB1271.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 1270 rfl rfl hel hC
