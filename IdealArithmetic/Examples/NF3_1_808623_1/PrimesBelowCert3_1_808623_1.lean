import IdealArithmetic.Examples.NF3_1_808623_1.PrimesBelow3_1_808623_1F0
import IdealArithmetic.Examples.NF3_1_808623_1.PrimesBelow3_1_808623_1F1
import IdealArithmetic.Examples.NF3_1_808623_1.PrimesBelow3_1_808623_1F2
import IdealArithmetic.Examples.NF3_1_808623_1.PrimesBelow3_1_808623_1F3
import IdealArithmetic.Examples.NF3_1_808623_1.PrimesBelow3_1_808623_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 254]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 255 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB255I0
  exact PB255I1
  exact PB255I2
  exact PB255I3
  exact PB255I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB255 : PrimesBelowBoundCertificate O 255 := by
  refine primesBelowBoundCertificate_of_Interval O eC 254 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 254 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 254 hC

lemma cert_eq_𝔭 : PB255.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 254 rfl rfl hel hC
