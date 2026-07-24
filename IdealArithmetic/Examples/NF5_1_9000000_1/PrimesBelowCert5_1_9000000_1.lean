import IdealArithmetic.Examples.NF5_1_9000000_1.PrimesBelow5_1_9000000_1F0
import IdealArithmetic.Examples.NF5_1_9000000_1.PrimesBelow5_1_9000000_1F1
import IdealArithmetic.Examples.NF5_1_9000000_1.PrimesBelow5_1_9000000_1F2
import IdealArithmetic.Examples.NF5_1_9000000_1.PrimesBelow5_1_9000000_1F3
import IdealArithmetic.Examples.NF5_1_9000000_1.PrimesBelow5_1_9000000_1F4

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 186]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 187 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB187I0
  exact PB187I1
  exact PB187I2
  exact PB187I3
  exact PB187I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB187 : PrimesBelowBoundCertificate O 187 := by
  refine primesBelowBoundCertificate_of_Interval O eC 186 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 186 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 186 hC

lemma cert_eq_𝔭 : PB187.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 186 rfl rfl hel hC
