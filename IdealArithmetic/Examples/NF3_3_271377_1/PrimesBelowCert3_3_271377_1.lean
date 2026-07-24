import IdealArithmetic.Examples.NF3_3_271377_1.PrimesBelow3_3_271377_1F0
import IdealArithmetic.Examples.NF3_3_271377_1.PrimesBelow3_3_271377_1F1
import IdealArithmetic.Examples.NF3_3_271377_1.PrimesBelow3_3_271377_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 115]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 116 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB116I0
  exact PB116I1
  exact PB116I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB116 : PrimesBelowBoundCertificate O 116 := by
  refine primesBelowBoundCertificate_of_Interval O eC 115 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 115 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 115 hC

lemma cert_eq_𝔭 : PB116.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 115 rfl rfl hel hC
