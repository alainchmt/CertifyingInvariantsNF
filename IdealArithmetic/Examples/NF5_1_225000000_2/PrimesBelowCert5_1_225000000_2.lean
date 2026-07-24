import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F0
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F1
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F2
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F3
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F4
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F5
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F6
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F7
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F8
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F9
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F10
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F11
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F12
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F13
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F14
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F15
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F16
import IdealArithmetic.Examples.NF5_1_225000000_2.PrimesBelow5_1_225000000_2F17

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 761, 827, 883, 933]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 934 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB934I0
  exact PB934I1
  exact PB934I2
  exact PB934I3
  exact PB934I4
  exact PB934I5
  exact PB934I6
  exact PB934I7
  exact PB934I8
  exact PB934I9
  exact PB934I10
  exact PB934I11
  exact PB934I12
  exact PB934I13
  exact PB934I14
  exact PB934I15
  exact PB934I16
  exact PB934I17

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB934 : PrimesBelowBoundCertificate O 934 := by
  refine primesBelowBoundCertificate_of_Interval O eC 933 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 933 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 933 hC

lemma cert_eq_𝔭 : PB934.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 933 rfl rfl hel hC
