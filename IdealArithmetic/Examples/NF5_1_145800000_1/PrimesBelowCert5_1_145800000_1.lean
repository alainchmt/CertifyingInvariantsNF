import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F0
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F1
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F2
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F3
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F4
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F5
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F6
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F7
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F8
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F9
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F10
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F11
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F12
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F13
import IdealArithmetic.Examples.NF5_1_145800000_1.PrimesBelow5_1_145800000_1F14

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 523, 593, 643, 701, 751]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 752 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB752I0
  exact PB752I1
  exact PB752I2
  exact PB752I3
  exact PB752I4
  exact PB752I5
  exact PB752I6
  exact PB752I7
  exact PB752I8
  exact PB752I9
  exact PB752I10
  exact PB752I11
  exact PB752I12
  exact PB752I13
  exact PB752I14

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB752 : PrimesBelowBoundCertificate O 752 := by
  refine primesBelowBoundCertificate_of_Interval O eC 751 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 751 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 751 hC

lemma cert_eq_𝔭 : PB752.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 751 rfl rfl hel hC
