import IdealArithmetic.Examples.NF5_3_121500000_4.PrimesBelow5_3_121500000_4F0
import IdealArithmetic.Examples.NF5_3_121500000_4.PrimesBelow5_3_121500000_4F1
import IdealArithmetic.Examples.NF5_3_121500000_4.PrimesBelow5_3_121500000_4F2
import IdealArithmetic.Examples.NF5_3_121500000_4.PrimesBelow5_3_121500000_4F3
import IdealArithmetic.Examples.NF5_3_121500000_4.PrimesBelow5_3_121500000_4F4
import IdealArithmetic.Examples.NF5_3_121500000_4.PrimesBelow5_3_121500000_4F5
import IdealArithmetic.Examples.NF5_3_121500000_4.PrimesBelow5_3_121500000_4F6
import IdealArithmetic.Examples.NF5_3_121500000_4.PrimesBelow5_3_121500000_4F7
import IdealArithmetic.Examples.NF5_3_121500000_4.PrimesBelow5_3_121500000_4F8
import IdealArithmetic.Examples.NF5_3_121500000_4.PrimesBelow5_3_121500000_4F9
import IdealArithmetic.Examples.NF5_3_121500000_4.PrimesBelow5_3_121500000_4F10

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 419, 463, 538]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 539 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB539I0
  exact PB539I1
  exact PB539I2
  exact PB539I3
  exact PB539I4
  exact PB539I5
  exact PB539I6
  exact PB539I7
  exact PB539I8
  exact PB539I9
  exact PB539I10

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB539 : PrimesBelowBoundCertificate O 539 := by
  refine primesBelowBoundCertificate_of_Interval O eC 538 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 538 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 538 hC

lemma cert_eq_𝔭 : PB539.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 538 rfl rfl hel hC
