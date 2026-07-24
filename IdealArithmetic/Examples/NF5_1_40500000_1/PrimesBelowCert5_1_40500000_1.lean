import IdealArithmetic.Examples.NF5_1_40500000_1.PrimesBelow5_1_40500000_1F0
import IdealArithmetic.Examples.NF5_1_40500000_1.PrimesBelow5_1_40500000_1F1
import IdealArithmetic.Examples.NF5_1_40500000_1.PrimesBelow5_1_40500000_1F2
import IdealArithmetic.Examples.NF5_1_40500000_1.PrimesBelow5_1_40500000_1F3
import IdealArithmetic.Examples.NF5_1_40500000_1.PrimesBelow5_1_40500000_1F4
import IdealArithmetic.Examples.NF5_1_40500000_1.PrimesBelow5_1_40500000_1F5
import IdealArithmetic.Examples.NF5_1_40500000_1.PrimesBelow5_1_40500000_1F6
import IdealArithmetic.Examples.NF5_1_40500000_1.PrimesBelow5_1_40500000_1F7
import IdealArithmetic.Examples.NF5_1_40500000_1.PrimesBelow5_1_40500000_1F8

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 396]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 397 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB397I0
  exact PB397I1
  exact PB397I2
  exact PB397I3
  exact PB397I4
  exact PB397I5
  exact PB397I6
  exact PB397I7
  exact PB397I8

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB397 : PrimesBelowBoundCertificate O 397 := by
  refine primesBelowBoundCertificate_of_Interval O eC 396 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 396 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 396 hC

lemma cert_eq_𝔭 : PB397.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 396 rfl rfl hel hC
