import IdealArithmetic.Examples.NF3_1_746956_1.PrimesBelow3_1_746956_1F0
import IdealArithmetic.Examples.NF3_1_746956_1.PrimesBelow3_1_746956_1F1
import IdealArithmetic.Examples.NF3_1_746956_1.PrimesBelow3_1_746956_1F2
import IdealArithmetic.Examples.NF3_1_746956_1.PrimesBelow3_1_746956_1F3
import IdealArithmetic.Examples.NF3_1_746956_1.PrimesBelow3_1_746956_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 244]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 245 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB245I0
  exact PB245I1
  exact PB245I2
  exact PB245I3
  exact PB245I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB245 : PrimesBelowBoundCertificate O 245 := by
  refine primesBelowBoundCertificate_of_Interval O eC 244 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 244 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 244 hC

lemma cert_eq_𝔭 : PB245.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 244 rfl rfl hel hC
