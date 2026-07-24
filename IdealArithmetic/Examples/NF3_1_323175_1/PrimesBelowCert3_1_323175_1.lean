import IdealArithmetic.Examples.NF3_1_323175_1.PrimesBelow3_1_323175_1F0
import IdealArithmetic.Examples.NF3_1_323175_1.PrimesBelow3_1_323175_1F1
import IdealArithmetic.Examples.NF3_1_323175_1.PrimesBelow3_1_323175_1F2
import IdealArithmetic.Examples.NF3_1_323175_1.PrimesBelow3_1_323175_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 160]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 161 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB161I0
  exact PB161I1
  exact PB161I2
  exact PB161I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB161 : PrimesBelowBoundCertificate O 161 := by
  refine primesBelowBoundCertificate_of_Interval O eC 160 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 160 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 160 hC

lemma cert_eq_𝔭 : PB161.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 160 rfl rfl hel hC
